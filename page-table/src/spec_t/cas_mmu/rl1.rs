use vstd::prelude::*;
use crate::spec_t::cas_mmu::*;
use crate::spec_t::cas_mmu::pt_mem::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::cas_mmu::defs::{ aligned, LoadResult, update_range, MAX_VIRTADDR };
use crate::spec_t::cas_mmu::defs::{ PTE, Core, Paddr, Vaddr, Vpn };
use crate::spec_t::cas_mmu::rl3::{ CASProgress };
use crate::spec_t::cas_mmu::translation::{ MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 1 of the MMU. Compared to layer 2, it removes store buffers
// and defines an atomic semantics to page table walks. This is the most abstract version of the
// MMU model.

/// Represents the Per-Core State.
pub ghost struct CoreState {
    /// the CR3 register containing the pml4 pointer (we abstract away the PCID here)
    pub cr3: Paddr,
    /// the cores's TLB. Note: technically it's the VPN there, but we're using the full Vaddr
    pub tlb: IMap<Vaddr, PTE>,
}

/// Represents the Per-Core State
impl CoreState {
    #[verifier(inline)]
    pub open spec fn new(cr3: Paddr) -> CoreState {
        CoreState {
            cr3,
            tlb: imap![]
        }
    }

    pub open spec fn init(self) -> bool {
        self.tlb == imap![]
    }

    pub open spec fn cr3_set(self, cr3: Paddr) -> CoreState
    {
        CoreState {
            cr3,
            ..self
        }
    }

    /// checks whether the TLB contains a mapping for the Vaddr `va` with the current `pcid`
    #[verifier(inline)]
    pub open spec fn tlb_contains(self, va: Vaddr) -> bool {
        self.tlb.contains_key(va)
    }

    /// checks whether the TLB does not have an entry associated with the current pcid
    #[verifier(inline)]
    pub open spec fn tlb_empty(self) -> bool {
        self.tlb.is_empty()
    }

    #[verifier(inline)]
    pub open spec fn tlb_fill(self, vbase: Vaddr, pte: PTE) -> CoreState
        recommends !self.tlb.contains_key(vbase)
    {
        CoreState {
            tlb: self.tlb.insert(vbase, pte),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn tlb_evict(self, va: Vaddr) -> CoreState
    {
        CoreState {
            tlb: self.tlb.remove(va),
            ..self
        }
    }
}


pub ghost struct State {
    pub happy: bool,
    pub cr3: Cr3,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub cores: IMap<Core, CoreState>,
    /// Tracks the virtual addresses and entries for which we may see non-atomic results.
    pub pending_maps: IMap<usize, PTE>,
    pub cas: CASProgress,
}

pub ghost enum Step {
    // Mixed
    Invlpg,
    InvPcid,
    SadInvPcid,
    WriteCr3,
    SadWriteCr3,
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
    // TSO
    CASWrite,
    Read,
    Barrier,
    Lock { addr: Paddr, expect: u64, new: u64 },
    Unlock,
    SadWrite,
    Sadness,
    Stutter,
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_WriteCr3(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::WriteCr3(core, cr3, flush)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& flush ==> pre.cores[core].tlb_empty()
    &&& pre.cores[core].cr3 == cr3.pml4

    &&& post == pre
}

pub open spec fn step_SadWriteCr3(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::WriteCr3(core, cr3, flush)

    &&& pre.cr3 != cr3 || !flush

    &&& pre.cr3 == post.cr3
    &&& !post.happy
}


pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& !pre.cores[core].tlb.contains_key(va)

    &&& post == pre
}

pub open spec fn step_InvPcid(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InvPcid(core, typ)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& match typ {
        // Individual-address invalidation: If the INVPCID type is 0, the logical processor invalidates
        // mappings—except global translations—for the linear address and PCID specified in the INVPCID
        // descriptor. In some cases, the instruction may invalidate global translations or mappings
        // for other linear addresses (or other PCIDs) as well.
        InvPcidType::IndividualAddress(d) => {
            &&& pre.cr3.pcid == d.pcid
            &&& !pre.cores[core].tlb.contains_key(d.vaddr)
        }
        InvPcidType::SingleContext(d) => {
            &&& pre.cr3.pcid == d.pcid
            &&& pre.cores[core].tlb.is_empty()
        }
        _ => {
            &&& pre.cores[core].tlb.is_empty()
        }
    }

    // Individual-address inv

    &&& post == pre
}

pub open spec fn step_SadInvpcid(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::InvPcid(core, typ)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& match typ {
        // Individual-address invalidation: If the INVPCID type is 0, the logical processor invalidates
        // mappings—except global translations—for the linear address and PCID specified in the INVPCID
        // descriptor. In some cases, the instruction may invalidate global translations or mappings
        // for other linear addresses (or other PCIDs) as well.
        InvPcidType::IndividualAddress(d) => {
            &&& pre.cr3.pcid != d.pcid
        }
        InvPcidType::SingleContext(d) => {
            &&& pre.cr3.pcid != d.pcid
        }
        _ => {
            &&& false // we should not reach here
        }
    }

    &&& post.cr3 == pre.cr3
    &&& !post.happy
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
    &&& pre.cores[core].tlb.contains_key(tlb_va)
    &&& {
    let pte = pre.cores[core].tlb[tlb_va];
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

    &&& post.cas == pre.cas
    &&& post.happy == pre.happy
    &&& post.cr3 == pre.cr3
    &&& post.pt_mem == pre.pt_mem
    &&& post.cores == pre.cores
    &&& post.pending_maps == pre.pending_maps
}

// ---- Non-atomic page table walks ----

/// A TLB fill resulting from an atomic page table walk
pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& vaddr < MAX_VIRTADDR
    &&& pre.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].tlb_fill(vbase, pte)),
        ..pre
    }
}

pub open spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.cores[core].tlb.contains_key(tlb_va)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].tlb_evict(tlb_va)),
        ..pre
    }
}


// ---- TSO ----

pub open spec fn step_CASWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.cas is NextWrite
    &&& pre.cas.core() == core
    &&& pre.cas.addr() == addr
    &&& pre.cas->NextWrite_new == value
    &&& pre.pt_mem.is_nonneg_write(addr, value)

    &&& post == State {
        pt_mem: pre.pt_mem.write(addr, value),
        cas: CASProgress::Done { core, addr },
        pending_maps:
            IMap::new(
                |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
                |vbase| post.pt_mem@[vbase]
            ),
        ..pre
    }
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& !(pre.cas is NextRead && pre.cas.core() == core && pre.cas.addr() == addr)

    &&& pre.cas is NoOngoingCAS
        ==> value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

pub open spec fn step_CASRead(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.cas is NextRead
    &&& pre.cas.core() == core
    &&& pre.cas.addr() == addr

    &&& value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == State {
        cas: if pre.cas->NextRead_expect == value {
            CASProgress::NextWrite { core, addr, new: pre.cas->NextRead_new }
        } else { CASProgress::Done { core, addr } },
        ..pre
    }
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == pre
}

/// Indicates start of a CAS instruction
pub closed spec fn step_Lock(pre: State, post: State, c: Constants, addr: Paddr, expect: u64, new: u64, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Lock(core)

    &&& c.valid_core(core)
    &&& pre.cas is NoOngoingCAS

    &&& post == State {
        cas: CASProgress::NextRead {
            core, addr, expect, new
        },
        ..pre
    }
}

/// Indicates end of a CAS instruction
pub closed spec fn step_Unlock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Unlock(core)

    &&& c.valid_core(core)
    &&& pre.cas matches CASProgress::Done { core: c, .. } && c == core

    &&& post == State {
        cas: CASProgress::NoOngoingCAS,
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

    &&& !post.happy
    &&& post.cr3 == pre.cr3
    // &&& pre.pt_mem.is_nonneg_write(addr, value) ==> !pre.is_happy_writenonneg(core, addr, value)
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                     => step_Invlpg(pre, post, c, lbl),
        Step::InvPcid                    => step_InvPcid(pre,post, c, lbl),
        Step::SadInvPcid                 => step_SadInvpcid(pre, post, c, lbl),
        Step::WriteCr3                   => step_WriteCr3(pre, post, c, lbl),
        Step::SadWriteCr3                => step_SadWriteCr3(pre, post, c, lbl),
        Step::MemOpNoTr                  => step_MemOpNoTr(pre, post, c, lbl),
        Step::MemOpNoTrNA { vbase }      => step_MemOpNoTrNA(pre, post, c, vbase, lbl),
        Step::MemOpTLB { tlb_va }        => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::TLBFill { core, vaddr }    => step_TLBFill(pre, post, c, core, vaddr, lbl),
        Step::TLBEvict { core, tlb_va }  => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::CASWrite                   => step_CASWrite(pre, post, c, lbl),
        Step::Read                       => step_Read(pre, post, c, lbl),
        Step::Barrier                    => step_Barrier(pre, post, c, lbl),
        Step::Lock { addr, expect, new } => step_Lock(pre, post, c, addr, expect, new, lbl),
        Step::Unlock                     => step_Unlock(pre, post, c, lbl),
        Step::SadWrite                   => step_SadWrite(pre, post, c, lbl),
        Step::Sadness                    => step_Sadness(pre, post, c, lbl),
        Step::Stutter                    => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.happy == (pre.pt_mem.pml4 == c.cr3.pml4)
    &&& pre.cores === IMap::new(|core| c.valid_core(core), |core| CoreState::new(c.cr3.pml4))
    &&& pre.pending_maps === imap![]
    &&& pre.cas == CASProgress::NoOngoingCAS

    &&& pre.pt_mem.mem === IMap::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8), |va| 0)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& c.memories_disjoint()
    &&& pre.phys_mem.len() == c.range_mem.1
    &&& c.in_ptmem_range(pre.pt_mem.pml4 as nat, 4096)
}

//proof fn init_implies_inv(pre: State, c: Constants)
//    requires init(pre, c)
//    ensures pre.inv(c)
//{}
//
//proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next_step(pre, post, c, step, lbl),
//    ensures post.inv(c)
//{}


} // verus!
