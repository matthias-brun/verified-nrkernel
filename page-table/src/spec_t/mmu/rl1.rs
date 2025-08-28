use vstd::prelude::*;
use vstd::assert_by_contradiction;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ aligned, LoadResult, update_range, MAX_BASE };
use crate::spec_t::mmu::defs::{ PTE, Core };
use crate::spec_t::mmu::rl3::{ Writes };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };


verus! {

// This file contains refinement layer 1 of the MMU. Compared to layer 2, it removes store buffers
// and defines an atomic semantics to page table walks. This is the most abstract version of the
// MMU model.

pub struct State {
    pub happy: bool,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    pub writes: Writes,
    /// Tracks the virtual addresses and entries for which we may see non-atomic results.
    /// If polarity is positive, translations may non-atomically fail.
    /// If polarity is negative, translations may non-atomically succeed.
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
    pub polarity: Polarity,
}

pub enum Step {
    // Mixed
    Invlpg,
    // Faulting memory op due to failed translation
    // (atomic walk)
    MemOpNoTr,
    // Faulting memory op due to failed translation
    // (non-atomic walk result)
    MemOpNoTrNA { vbase: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    TLBFill { core: Core, vaddr: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // Non-atomic TLB fill after an unmap
    TLBFillNA { core: Core, vaddr: usize },
    // TSO
    WriteNonneg,
    WriteNonpos,
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}


impl State {
    pub open spec fn is_happy_writenonneg(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonneg_write(addr, value)
    }

    pub open spec fn is_happy_writenonpos(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonpos_write(addr, value)
    }

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.tso.contains(addr) ==> self.writes.core == core
    }

    pub open spec fn can_flip_polarity(self, c: Constants) -> bool {
        &&& self.writes.tso === set![]
        &&& self.writes.nonpos === set![]
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& !pre.tlbs[core].contains_key(va)

    &&& post == State {
        writes: Writes {
            core: pre.writes.core,
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            nonpos:
                if post.writes.tso === set![] {
                    pre.writes.nonpos.remove(core)
                } else { pre.writes.nonpos },
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        pending_unmaps: if post.writes.nonpos === set![] { map![] } else { pre.pending_unmaps },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pt_mem.pt_walk(memop_vaddr).result() is Invalid
    &&& memop.is_pagefault()

    &&& post == pre
}

pub open spec fn step_MemOpNoTrNA(pre: State, post: State, c: Constants, vbase: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy
    &&& pre.polarity is Mapping

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pending_maps.contains_key(vbase)
    &&& vbase <= memop_vaddr < vbase + pre.pending_maps[vbase].frame.size
    &&& memop.is_pagefault()

    &&& post == pre
}

pub open spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& {
    let pte = pre.tlbs[core][tlb_va];
    let paddr = pte.frame.base + (memop_vaddr - tlb_va);
    &&& tlb_va <= memop_vaddr < tlb_va + pte.frame.size
    &&& match memop {
        MemOp::Store { new_value, result } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                &&& result is Ok
                &&& post.phys_mem === update_range(pre.phys_mem, paddr, new_value)
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
        MemOp::Load { is_exec, result, .. } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                &&& result == LoadResult::Value(pre.phys_mem.subrange(paddr, paddr + memop.op_size()))
                &&& post.phys_mem === pre.phys_mem
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
    }
    }

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.writes == pre.writes
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps
    &&& post.polarity == pre.polarity
}

// ---- Non-atomic page table walks ----

/// A TLB fill resulting from an atomic page table walk
pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& vaddr < MAX_BASE
    &&& pre.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }
    &&& !pre.tlbs[core].contains_key(vbase)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vbase, pte)),
        ..pre
    }
}

pub open spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.tlbs[core].contains_key(tlb_va)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].remove(tlb_va)),
        ..pre
    }
}

/// A TLB fill resulting from a non-atomic page table walk
pub open spec fn step_TLBFillNA(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let pte = pre.pending_unmaps[vaddr];
    &&& lbl is Tau
    &&& pre.happy
    &&& pre.polarity is Unmapping

    &&& c.valid_core(core)
    &&& pre.writes.nonpos.contains(core)
    &&& pre.pending_unmaps.contains_key(vaddr)
    &&& !pre.tlbs[core].contains_key(vaddr)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vaddr, pte)),
        ..pre
    }
}



// ---- TSO ----

pub open spec fn step_WriteNonneg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_happy_writenonneg(core, addr, value)
    &&& pre.polarity is Mapping || pre.can_flip_polarity(c)

    &&& post.happy      == pre.happy
    &&& post.phys_mem   == pre.phys_mem
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.tlbs       == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Mapping
    &&& post.writes.nonpos == pre.writes.nonpos
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
    &&& post.pending_unmaps == pre.pending_unmaps
}

pub open spec fn step_WriteNonpos(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_happy_writenonpos(core, addr, value)
    &&& pre.polarity is Unmapping || pre.can_flip_polarity(c)

    &&& post.happy      == pre.happy
    &&& post.phys_mem   == pre.phys_mem
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.tlbs       == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Unmapping
    &&& post.writes.nonpos == Set::new(|core| c.valid_core(core))
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.pt_mem@.contains_key(vbase) && !post.pt_mem@.contains_key(vbase),
            |vbase| pre.pt_mem@[vbase]
        ))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_tso_read_deterministic(core, addr)
            ==> value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            ..pre.writes
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& {
        ||| value & 1 == 1 && !pre.is_happy_writenonneg(core, addr, value)
        ||| value & 1 == 0 && !pre.is_happy_writenonpos(core, addr, value)
    }
    &&& !post.happy
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                    => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr                 => step_MemOpNoTr(pre, post, c, lbl),
        Step::MemOpNoTrNA { vbase }     => step_MemOpNoTrNA(pre, post, c, vbase, lbl),
        Step::MemOpTLB { tlb_va }       => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::TLBFill { core, vaddr }   => step_TLBFill(pre, post, c, core, vaddr, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::TLBFillNA { core, vaddr } => step_TLBFillNA(pre, post, c, core, vaddr, lbl),
        Step::WriteNonneg               => step_WriteNonneg(pre, post, c, lbl),
        Step::WriteNonpos               => step_WriteNonpos(pre, post, c, lbl),
        Step::Read                      => step_Read(pre, post, c, lbl),
        Step::Barrier                   => step_Barrier(pre, post, c, lbl),
        Step::SadWrite                  => step_SadWrite(pre, post, c, lbl),
        Step::Sadness                   => step_Sadness(pre, post, c, lbl),
        Step::Stutter                   => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.happy
    &&& pre.tlbs === Map::new(|core| c.valid_core(core), |core| map![])
    &&& pre.writes.tso === set![]
    &&& pre.writes.nonpos === set![]
    &&& pre.pending_maps === map![]
    &&& pre.pending_unmaps === map![]
    &&& pre.polarity === Polarity::Mapping

    &&& c.valid_core(pre.writes.core)
    &&& pre.pt_mem.mem === Map::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8), |va| 0)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& c.memories_disjoint()
    &&& pre.phys_mem.len() == c.range_mem.1
    &&& c.in_ptmem_range(pre.pt_mem.pml4 as nat, 4096)
}



impl State {
    pub open spec fn wf(self, c: Constants) -> bool {
        &&& c.valid_core(self.writes.core)
        &&& self.writes.tso.finite()

        // &&& aligned(self.pt_mem.pml4 as nat, 4096)
        // &&& c.in_ptmem_range(self.pt_mem.pml4 as nat, 4096)
        // &&& c.memories_disjoint()
        //&&& self.phys_mem.len() == c.range_mem.1
        // &&& self.wf_ptmem_range(c)
    }

    pub open spec fn inv_mapping(self, c: Constants) -> bool {
        &&& self.pending_unmaps === map![]
    }

    pub open spec fn inv_unmapping(self, c: Constants) -> bool {
        &&& self.pending_maps === map![]
        &&& forall|va| #[trigger] self.pending_unmaps.contains_key(va) ==> !self.pt_mem@.contains_key(va)
        &&& forall|core| #[trigger] c.valid_core(core) && !self.writes.nonpos.contains(core)
        ==> !self.pt_mem@.contains_key(va)
    }

    pub open spec fn inv_tlb_entry_is_in_mem_or_pending_unmaps(self, c: Constants) -> bool {
        forall|va, core| c.valid_core(core) && #[trigger] self.tlbs[core].contains_key(va) ==> {
            let pte = self.tlbs[core][va];
            self.pt_mem@.contains_pair(va, pte) || self.pending_unmaps.contains_pair(va, pte)
        }
    }

    pub open spec fn inv(self, c: Constants) -> bool {
       self.happy ==> {
       &&& self.wf(c)
       &&& self.inv_tlb_entry_is_in_mem_or_pending_unmaps(c)
       &&& self.polarity is Mapping ==> self.inv_mapping(c)
       &&& self.polarity is Unmapping ==> self.inv_unmapping(c)
       }
    }
}

proof fn init_implies_inv(pre: State, c: Constants)
   requires init(pre, c)
   ensures pre.inv(c)
{}

pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.inv(c),
        next(pre, post, c, lbl),
    ensures post.inv(c)
{
    let step = choose|step| next_step(pre, post, c, step, lbl);
    next_step_preserves_inv(pre, post, c, step, lbl);
}

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
   requires
       pre.inv(c),
       next_step(pre, post, c, step, lbl),
   ensures post.inv(c)
{
    if pre.happy && post.happy {
        assert(post.wf(c));
        if post.polarity is Mapping {
            if pre.polarity is Unmapping { // Flipped polarity in this transition
                assert(step is WriteNonneg);
                assert(pre.can_flip_polarity(c));
                assert(post.wf(c));
                // TODO: switching invariant
                assume(pre.pending_unmaps === map![]);
                assert(post.inv_mapping(c));
            }
        } else {
            if pre.polarity is Mapping { // Flipped polarity in this transition
                // TODO: switching invariant
                assume(pre.pending_maps === map![]);
            } else {
                // TODO: can probably lift from rl1
                assume(post.pt_mem@.submap_of(pre.pt_mem@));
                assert(post.inv_unmapping(c));
            }
        }
        next_step_preserves_inv_tlb_entry_is_in_mem_or_pending_unmaps(pre, post, c, step, lbl);
    } else {
    }
}

proof fn next_step_preserves_inv_tlb_entry_is_in_mem_or_pending_unmaps(
    pre: State,
    post: State,
    c: Constants,
    step: Step,
    lbl: Lbl
)
   requires
       pre.inv(c),
       post.wf(c),
       post.polarity is Mapping ==> post.inv_mapping(c),
       post.polarity is Unmapping ==> post.inv_unmapping(c),
       pre.happy,
       post.happy,
       next_step(pre, post, c, step, lbl),
   ensures post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c)
{
    assert(pre.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
    match step {
        rl1::Step::Invlpg => {
            assume(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::MemOpNoTr => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::MemOpNoTrNA { vbase } => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::MemOpTLB { tlb_va } => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::TLBFill { core, vaddr } => {
            assert(pre.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte });
            let vbase = pre.pt_mem.pt_walk(vaddr).result()->Valid_vbase;
            assume(pre.pt_mem.pt_walk(vaddr).result() == pre.pt_mem.pt_walk(vbase).result());
            assert forall|va, core| c.valid_core(core) && #[trigger] post.tlbs[core].contains_key(va) implies {
                let pte = post.tlbs[core][va];
                post.pt_mem@.contains_pair(va, pte) || post.pending_unmaps.contains_pair(va, pte)
            } by {
                let pte = post.tlbs[core][va];
                // assume(post.pt_mem@.submap_of(pre.pt_mem@));
                assume(post.pt_mem@.contains_key(va));
                assume(post.pt_mem@.contains_pair(va, pte));
            };
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::TLBFillNA { .. } => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::TLBEvict { core, tlb_va } => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::WriteNonneg => {
            assume(pre.pt_mem@.submap_of(post.pt_mem@));
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::WriteNonpos => {
            assume(post.pt_mem@.submap_of(pre.pt_mem@));
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::Read => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::Barrier => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::SadWrite => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::Sadness => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
        rl1::Step::Stutter => {
            assert(post.inv_tlb_entry_is_in_mem_or_pending_unmaps(c));
        },
    }
}



pub mod refinement {
    // use vstd::assert_by_contradiction;

    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl0;
    use crate::spec_t::mmu::rl1;
    // #[cfg(verus_keep_ghost)]
    // use crate::spec_t::mmu::defs::MAX_BASE;

    impl rl1::State {
        pub open spec fn interp(self) -> rl0::State {
            rl0::State {
                happy: self.happy,
                pt_mem: self.pt_mem,
                phys_mem: self.phys_mem,
                writes: self.writes,
                pending_maps: self.pending_maps,
                pending_unmaps: self.pending_unmaps,
                polarity: self.polarity,
            }
        }
    }

    impl rl1::Step {
        pub open spec fn interp(self, pre: rl1::State, lbl: Lbl) -> rl0::Step {
            match self {
                rl1::Step::Invlpg => rl0::Step::Invlpg,
                rl1::Step::MemOpNoTr => rl0::Step::MemOpNoTr,
                rl1::Step::MemOpNoTrNA { vbase } => rl0::Step::MemOpNoTrNA { vbase },
                rl1::Step::MemOpTLB { tlb_va } => {
                    if pre.pending_unmaps.contains_key(tlb_va) {
                        rl0::Step::MemOpNA { vbase: tlb_va }
                    } else {
                        rl0::Step::MemOp { vbase: tlb_va }
                    }
                },
                rl1::Step::TLBFill { .. } => rl0::Step::Stutter,
                rl1::Step::TLBFillNA { .. } => rl0::Step::Stutter,
                rl1::Step::TLBEvict { .. } => rl0::Step::Stutter,
                rl1::Step::WriteNonneg => rl0::Step::WriteNonneg,
                rl1::Step::WriteNonpos => rl0::Step::WriteNonpos,
                rl1::Step::Read => rl0::Step::Read,
                rl1::Step::Barrier => rl0::Step::Barrier,
                rl1::Step::SadWrite => rl0::Step::SadWrite,
                rl1::Step::Sadness => rl0::Step::Sadness,
                rl1::Step::Stutter => rl0::Step::Stutter,
            }
        }
    }

    proof fn next_step_refines(pre: rl1::State, post: rl1::State, c: rl1::Constants, step: rl1::Step, lbl: Lbl)
        requires
            pre.inv(c),
            rl1::next_step(pre, post, c, step, lbl),
        ensures rl0::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        match step {
            rl1::Step::Invlpg => {
                assert(rl0::step_Invlpg(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::MemOpNoTr => {
                assert(rl0::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::MemOpNoTrNA { vbase } => {
                assert(rl0::step_MemOpNoTrNA(pre.interp(), post.interp(), c, vbase, lbl));
            },
            rl1::Step::MemOpTLB { tlb_va } => {
                next_step_MemOpTLB_refines(pre, post, c, step, lbl);
                if pre.pending_unmaps.contains_key(tlb_va) {
                    assert(rl0::step_MemOpNA(pre.interp(), post.interp(), c, tlb_va, lbl));
                } else {
                    assert(rl0::step_MemOp(pre.interp(), post.interp(), c, tlb_va, lbl));
                }
            },
            rl1::Step::TLBFill { .. } => {
                assert(rl0::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::TLBFillNA { .. } => {
                assert(rl0::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::TLBEvict { .. } => {
                assert(rl0::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::WriteNonneg => {
                assert(rl0::step_WriteNonneg(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::WriteNonpos => {
                assert(rl0::step_WriteNonpos(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::Read => {
                assert(rl0::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::Barrier => {
                assert(rl0::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::SadWrite => {
                assert(rl0::step_SadWrite(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::Sadness => {
                assert(rl0::step_Sadness(pre.interp(), post.interp(), c, lbl));
            },
            rl1::Step::Stutter => {
                assert(rl0::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    proof fn next_step_MemOpTLB_refines(pre: rl1::State, post: rl1::State, c: rl1::Constants, step: rl1::Step, lbl: Lbl)
        requires
            step is MemOpTLB,
            pre.happy,
            pre.inv(c),
            rl1::next_step(pre, post, c, step, lbl),
        ensures rl0::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        let (core, memop_vaddr, memop) = if let Lbl::MemOp(core, vaddr, memop) = lbl {
                (core, vaddr, memop)
            } else { arbitrary() };
        let tlb_va = step->MemOpTLB_tlb_va;
        let pte = pre.tlbs[core][tlb_va];
        assert(pre.tlbs[core].contains_pair(tlb_va, pte));

        assert(c.valid_core(core));
        // assume(forall|va, pte, core| #[trigger] pre.tlbs[core].contains_pair(va, pte)
        //     ==> pre.pt_mem@.contains_pair(va, pte) || pre.pending_unmaps.contains_pair(va, pte)
        //     );
        if pre.pending_unmaps.contains_key(tlb_va) {
            // assume(pre.polarity is Unmapping);
            // Unmapping polarity -> Unmapped entry isn't in PT anymore
            // assume(forall|va| #[trigger] pre.pending_unmaps.contains_key(va) ==> !pre.pt_mem@.contains_key(va));
            assert(pre.pending_unmaps.contains_pair(tlb_va, pte));
            assert(rl0::step_MemOpNA(pre.interp(), post.interp(), c, tlb_va, lbl));
        } else {
            assert(pre.pt_mem@.contains_pair(tlb_va, pte));
            assert(rl0::step_MemOp(pre.interp(), post.interp(), c, tlb_va, lbl));
        }
        // let walk = step->MemOpTLB_walk;
        // let (core, memop_vaddr, memop) = if let Lbl::MemOp(core, vaddr, memop) = lbl {
        //         (core, vaddr, memop)
        //     } else { arbitrary() };
        // let core_mem = pre.core_mem(core);
        // let writer_mem = pre.writer_mem();
        // let walk_na = rl2::walk_next(pre.core_mem(core), walk);
        //
        // rl2::lemma_iter_walk_equals_pt_walk(core_mem, walk.vaddr);
        // rl2::lemma_iter_walk_equals_pt_walk(writer_mem, walk.vaddr);
        //
        // if pre.polarity is Mapping {
        //     assert(forall|i| 0 <= i < walk.path.len() ==> walk_na.path[i] == walk.path[i]) by {
        //         reveal(rl2::walk_next);
        //     };
        //     assert(walk_na.result() is Invalid);
        //
        //     // This walk has the same result if done on the same core but atomically.
        //     let walk_a_same_core = rl2::iter_walk(core_mem, walk.vaddr);
        //     assert(walk_a_same_core == walk_na);
        //
        //     // The atomic walk on this core is the same as an atomic walk on the writer's view
        //     // of the memory. (Or if not, it's in a region in `pre.pending_maps`.)
        //     let walk_a_writer_core = rl2::iter_walk(writer_mem, walk.vaddr);
        //
        //     assert(walk_a_writer_core == writer_mem.pt_walk(walk.vaddr));
        //
        //     if pre.pending_map_for(walk.vaddr) {
        //         let vb = choose|vb| {
        //             &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
        //             &&& vb <= walk.vaddr < vb + pre.hist.pending_maps[vb].frame.size
        //         };
        //         pre.interp().pending_maps.contains_key(vb);
        //         assert(rl1::step_MemOpNoTrNA(pre.interp(), post.interp(), c, vb, lbl));
        //     } else {
        //         if core == pre.writes.core {
        //             // If the walk happens on the writer core, the two atomic walks are done on the same
        //             // memory, i.e. are trivially equal.
        //             assert(walk_a_writer_core == walk_a_same_core);
        //             assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
        //         } else {
        //             rl2::lemma_valid_implies_equal_walks(pre, c, core, walk.vaddr);
        //             assert forall|va: usize| va < MAX_BASE && writer_mem.pt_walk(va).result() is Valid && !pre.pending_map_for(va)
        //                 implies #[trigger] core_mem.pt_walk(va).result() == writer_mem.pt_walk(va).result()
        //             by { rl2::lemma_valid_not_pending_implies_equal(pre, c, core, va); };
        //             assert(walk_a_same_core.result() == walk_a_writer_core.result());
        //             assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
        //         }
        //     }
        // } else {
        //     broadcast use rl2::lemma_invalid_walk_is_invalid_in_writer_mem;
        //     assert(pre.core_mem(core).pt_walk(walk.vaddr).result() is Invalid);
        //     assert(pre.writer_mem().pt_walk(walk.vaddr).result() is Invalid);
        // }
    }

    pub proof fn init_refines(pre: rl1::State, c: rl1::Constants)
        requires rl1::init(pre, c),
        ensures rl0::init(pre.interp(), c),
    {}

    pub proof fn next_refines(pre: rl1::State, post: rl1::State, c: rl1::Constants, lbl: Lbl)
        requires
            pre.inv(c),
            rl1::next(pre, post, c, lbl),
        ensures
            rl0::next(pre.interp(), post.interp(), c, lbl),
    {
        let step = choose|step: rl1::Step| rl1::next_step(pre, post, c, step, lbl);
        next_step_refines(pre, post, c, step, lbl);
    }
}


} // verus!
