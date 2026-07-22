// #![cfg_attr(verus_keep_ghost, verus::trusted)]
// Trusted: This file defines the assumed semantics of the memory translation hardware as a state
// machine.
// TODO: manually applying ranges here because the refinement proofs should be counted normally as
// spec and proof, not trusted

// $line_count$Trusted${$

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::extra::lemma_bits_misc;
use crate::spec_t::cas_mmu::*;
use crate::spec_t::cas_mmu::pt_mem::*;
use crate::spec_t::cas_mmu::defs::{ bit, Core, bitmask_inc, MemOp, LoadResult, PTE, Vpn, Paddr, Vaddr, Pcid, Cr3 };
#[cfg(verus_keep_ghost)]
use crate::spec_t::cas_mmu::defs::{ aligned, update_range, MAX_VIRTADDR };
use crate::spec_t::cas_mmu::translation::{ l0_bits, l1_bits, l2_bits, l3_bits, MASK_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 3 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.
//
// Most of the definitions in this file are `closed`. We reason about the behavior of this state
// machine exclusively in terms of the more abstract MMU models it refines.


/// Represents the Per-Core State
pub struct CoreState {
    /// the CR3 register containing the pml4 pointer and pcid
    pub cr3: Cr3,
    /// the cores's TLB, this is a total map from PCID -> Map<Vaddr, PTE>
    pub tlb: IMap<Pcid, IMap<Vaddr, PTE>>,
    /// Paging Structure Caches (PSCs) of the core, this is a total map from PCID -> ISet<Walk>
    pub psc: IMap<Pcid, ISet<Walk>>,
    /// Ongoing walks of the core, this is a total
    pub walks: ISet<Walk>,
    /// Store Buffer of the core (for PTMem Updates)
    pub stbuf: Seq<(Vaddr, usize)>
}

impl CoreState {
    pub open spec fn new(cr3: Cr3) -> CoreState {
        CoreState {
            cr3,
            tlb: IMap::total(|k| IMap::empty()),
            psc: IMap::total(|k| iset![]),
            walks: iset![],
            stbuf:  seq![],
        }
    }

    pub open spec fn init(&self, cr3: Cr3) -> bool {
        &&& self.cr3   === cr3
        &&& self.tlb   === IMap::total(|k| IMap::empty())
        &&& self.psc === IMap::total(|k| iset![])
        &&& self.walks === iset![]
        &&& self.stbuf  === seq![]
    }

    /// Well-formedness Condition
    #[verifier(inline)]
    pub open spec fn wf(self) -> bool {
        // the TLB is a full/total map from PCID -> Map<Vaddr, PTE> and its map with the TLB
        // entries is finite
        &&& self.tlb.is_full()
        &&& forall |p| #[trigger]self.tlb.contains_key(p) ==> self.tlb[p].dom().finite()

        // the PSC is a full/total map from PCID -> ISet<Walk> and its set with the cached
        // partial walks is finite
        &&& self.psc.is_full()    //
        &&& forall |p| #[trigger]self.psc.contains_key(p) ==> self.psc[p].finite()

        // there is a finite number of ongoing walks
        &&& self.walks.finite()
    }

    pub open spec fn walk_valid(walk: Walk) -> bool {
        &&& aligned(walk.vaddr as nat, 8)
        &&& walk.path.len() <= 3
        &&& !walk.complete
    }

    /// Invariant
    pub open spec fn inv(self) -> bool {
        &&& forall |walk| #[trigger] self.walks_contains(walk)
            ==> Self::walk_valid(walk)
        &&& forall |pcid, walk| self.psc_contains_pcid(pcid, walk)
            ==> Self::walk_valid(walk)
    }

    // -------------------------------------- CR3 -------------------------------------------------

    #[verifier(inline)]
    pub open spec fn cr3_set(self, cr3: Cr3) -> CoreState
    {
        CoreState {
            cr3,
            ..self
        }
    }

    /// obtains the current PCID
    #[verifier(inline)]
    pub open spec fn pcid(&self) -> Pcid {
        self.cr3.pcid
    }

    // -------------------------------------- TLB --------------------------------------------------


    /// checks whether the TLB does not have an entry associated with the supplied pcid
    #[verifier(inline)]
    pub open spec fn tlb_empty_pcid(self, pcid: Pcid) -> bool {
        self.tlb[pcid].is_empty()
    }

    /// checks whether the TLB does not have an entry associated with the current pcid
    #[verifier(inline)]
    pub open spec fn tlb_empty(self) -> bool {
        self.tlb_empty_pcid(self.pcid())
    }

    /// checks whether the TLB does not have any entry
    #[verifier(inline)]
    pub open spec fn tlb_empty_all(self) -> bool {
        forall |p| #[trigger]self.tlb[p].is_empty()
    }

    /// checks whether the TLB contains an entry with the supplied `pcid` and `vaddr`
    #[verifier(inline)]
    pub open spec fn tlb_contains_pcid(self, pcid: Pcid, va: Vaddr) -> bool {
        self.tlb[pcid].contains_key(va)
    }

    /// checks whether the TLB contains a mapping for the Vaddr `va` with the current `pcid`
    #[verifier(inline)]
    pub open spec fn tlb_contains(self, va: Vaddr) -> bool {
        self.tlb_contains_pcid(self.pcid(), va)
    }

    /// obtains the element from the TLB, which must contain the element
    #[verifier(inline)]
    pub open spec fn tlb_lookup_pcid(self, pcid: Pcid, va: Vaddr) -> PTE
        recommends self.tlb_contains_pcid(pcid, va)
    {
        self.tlb[pcid][va]
    }

    /// obtains the element by VA with the current PCID, which must contain the element
    #[verifier(inline)]
    pub open spec fn tlb_lookup(self, va: Vaddr) -> PTE
        recommends self.tlb_contains(va)
    {
        self.tlb_lookup_pcid(self.pcid(), va)
    }

    /// inserts an entry in the TLB. it will be associated with the current `pcid`
    #[verifier(inline)]
    pub open spec fn tlb_fill(self, vbase: Vaddr, pte: PTE) -> CoreState
        recommends !self.tlb[self.pcid()].contains_key(vbase)
    {
        CoreState {
            tlb: self.tlb.insert(self.pcid(), self.tlb[self.pcid()].insert(vbase, pte)),
            ..self
        }
    }

    /// evicts an entry with the given `pcid` and `vaddr` from the TLB
    #[verifier(inline)]
    pub open spec fn tlb_evict(self, pcid: Pcid, va: Vaddr) -> CoreState
    {
        CoreState {
            tlb: self.tlb.insert(pcid, self.tlb[pcid].remove(va)),
            ..self
        }
    }


    // ---------------------------- Paging Structure Caches ----------------------------------------

    /// checks whether the PSC does not contain an entry associated with the supplied pcid
    #[verifier(inline)]
    pub open spec fn psc_empty_pcid(&self, pcid: Pcid) -> bool {
        self.psc[pcid].is_empty()
    }

    /// checks whether the PCS does not contain an entry associated with the current pcid
    #[verifier(inline)]
    pub open spec fn psc_empty(&self) -> bool {
        self.psc_empty_pcid(self.pcid())
    }

    /// checks whether the PCS does not contain any entry
    #[verifier(inline)]
    pub open spec fn psc_empty_all(&self) -> bool {
        forall |p| (#[trigger]self.psc[p]).is_empty()
    }

    /// checks whether the walk is part of the PSC and associated with the current PCID
    #[verifier(inline)]
    pub open spec fn psc_contains_pcid(&self, pcid: Pcid, walk: Walk) -> bool {
        self.psc[pcid].contains(walk)
    }

    /// checks whether the walk is part of the PSC and associated with the current PCID
    #[verifier(inline)]
    pub open spec fn psc_contains(&self, walk: Walk) -> bool {
        self.psc_contains_pcid(self.pcid(), walk)
    }

    /// inserts the current partial walk into the PSC and associates it with the current PCID
    #[verifier(inline)]
    pub open spec fn psc_fill(self, walk: Walk) -> CoreState {
        CoreState {
            psc: self.psc.insert(self.pcid(), self.psc[self.pcid()].insert(walk)),
            ..self
        }
    }

    /// evicts the walk from the PSC with the supplied pcid
    #[verifier(inline)]
    pub open spec fn psc_evict(self, pcid: Pcid, walk: Walk) -> CoreState {
      CoreState {
            psc: self.psc.insert(pcid, self.psc[pcid].remove(walk)),
            ..self
        }
    }

    // -------------------------------------- Walks ------------------------------------------------

    /// whether the current ongoing walks are empty
    #[verifier(inline)]
    pub open spec fn walks_empty(&self) -> bool {
        self.walks.is_empty()
    }

    /// whether the supplied walk is ongoing
    #[verifier(inline)]
    pub open spec fn walks_contains(&self, walk: Walk) -> bool {
        self.walks.contains(walk)
    }

    /// removes a walk from the core
    #[verifier(inline)]
    pub open spec fn walks_remove(self, walk: Walk) -> CoreState {
        CoreState {
            walks: self.walks.remove(walk),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn walks_insert(self, walk: Walk) -> CoreState {
        CoreState {
            walks: self.walks.insert(walk),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn walks_replace(self, walk: Walk, walk_next: Walk) -> CoreState {
        CoreState {
            walks: self.walks.remove(walk).insert(walk_next),
            ..self
        }
    }

    // ----------------------------------- Store Buffers--------------------------------------------

    /// whether or not the store buffer is empty
    #[verifier(inline)]
    pub open spec fn stbuf_empty(self) -> bool {
        self.stbuf.len() == 0
    }

    #[verifier(inline)]
    pub open spec fn stbuf_push(self, addr: Paddr, value: usize) -> CoreState {
        CoreState {
            stbuf: self.stbuf.push((addr, value)),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn stbuf_drop(self) -> CoreState
    {
        CoreState {
            stbuf: self.stbuf.drop_first(),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn stbuf_first(self) -> (Paddr, usize)
    {
        self.stbuf.first()
    }
}


/// System State
pub struct State {
    /// For locked instructions (modeled as in Sewell et al. x86-TSO)
    lock: Option<Core>,
    /// Byte-indexed physical (non-page-table) memory
    phys_mem: Seq<u8>,
    /// Page table memory
    pt_mem: PTMem,
    /// the cores in the system
    cores: IMap<Core, CoreState>,
    /// History variables. These do not influence the transitions in any way. Neither in enabling
    /// conditions nor in state updates. We only use these during the refinement.
    hist: History,
}

/// Progress within a CAS operation, i.e., the ops between lock and unlock: read, write
pub enum CASProgress {
    NextRead {
        core: Core,
        addr: Paddr, 
        expect: u64,
        new: u64,
    },
    NextWrite {
        core: Core,
        addr: Paddr, 
        new: u64,
    },
    Done {
        core: Core,
        addr: Paddr,
    },
    NoOngoingCAS,
}

impl CASProgress {
    pub open spec fn core(self) -> Core
        recommends self !is NoOngoingCAS
    {
        match self {
            CASProgress::NextRead { core, .. } => core,
            CASProgress::NextWrite { core, .. } => core,
            CASProgress::Done { core, .. } => core,
            _ => arbitrary(),
        }
    }

    pub open spec fn addr(self) -> Paddr
        recommends self !is NoOngoingCAS
    {
        match self {
            CASProgress::NextRead { addr, .. } => addr,
            CASProgress::NextWrite { addr, .. } => addr,
            CASProgress::Done { addr, .. } => addr,
            _ => arbitrary(),
        }
    }
}

pub struct History {
    pub happy: bool,
    pub cr3: Cr3,
    pub cas: CASProgress,
    /// All partial walks since the last invlpg
    pub walks: IMap<Core, ISet<Walk>>,
}

/// Any transition that reads from page table memory takes an arbitrary usize `r`, which is used to
/// non-deterministically flip the accessed and dirty bits.
/// A seemingly easier way to specify this would be:
/// `result & MASK_NEG_DIRTY_ACCESS = read(addr) & MASK_NEG_DIRTY_ACCESS`
/// But this makes specifying the page table walks very awkward because read is now specified as a
/// predicate. Instead we explicitly xor with an arbitrary value. At higher refinement layers we do
/// use the predicate approach because we can prove in the refinement that the value of `r` is
/// irrelevant for page table walks, so the read predicate only shows up in `step_Read`.
pub enum Step {
    Invlpg,
    InvPcid,
    WriteCr3,
    // Faulting memory op due to failed translation
    MemOpNoTr { walk: Walk, r: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: Vaddr },
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, pcid: Pcid, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk, r: usize },
    WalkAbort { core: Core, walk: Walk },
    TLBFill { core: Core, walk: Walk, r: usize },
    TLBEvict { core: Core, tlb_pcid: Pcid, tlb_va: Vaddr },
    // TSO, operations on page table memory
    Lock { addr: Paddr, expect: u64, new: u64 }, // These are ghost arguments, not part of lock itself
    Unlock,
    Write,
    Writeback { core: Core },
    Read { r: usize },
    Barrier,
    Stutter,
}


impl State {
    pub closed spec fn read_from_mem_tso(self, core: Core, addr: usize, r: usize) -> usize {
        self.core_mem(core).read(addr) ^ (r & MASK_DIRTY_ACCESS)
    }

    /// The memory as seen by the given core. I.e. taking into consideration the core's store
    /// buffers.
    pub closed spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.cores[core].stbuf)
    }

    /// The view of the memory from the writer core's perspective.
    pub closed spec fn writer_mem(self) -> PTMem {
        match self.lock {
            None => self.pt_mem,
            Some(core) => self.core_mem(core),
        }
    }

    pub closed spec fn is_happy_write(self, core: Core, addr: Paddr, value: usize) -> bool {
        &&& self.hist.cas is NextWrite
        &&& self.hist.cas.core() == core
        &&& self.hist.cas.addr() == addr
        &&& self.hist.cas->NextWrite_new == value
        &&& self.writer_mem().is_nonneg_write(addr, value)
        // && pre.lock == Some(core)
        // && pre.cores[core].stbuf_empty()
    }
}


//
// State machine transitions
//
pub closed spec fn step_WriteCr3(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::WriteCr3(core, cr3, flush)

    &&& c.valid_core(core)

    // mov cr3 is a serializing instruction, ..
    &&& pre.cores[core].stbuf_empty()
    &&& pre.cores[core].walks_empty()

    // Writing to control register with lock prefix causes exception
    &&& pre.lock != Some(core)

    // If CR4.PCIDE = 1 and bit 63 of the instruction’s source operand is 1, the instruction is not
    // required to invalidate any TLB entries or entries in paging-structure caches.
    // If CR4.PCIDE = 1 and bit 63 of the instruction’s source operand is 0, the instruction
    // invalidates all TLB entries associated with the PCID specified in bits 11:0 of the
    // instruction’s source operand except those for global pages. It also invalidates all entries
    // in all paging-structure caches associated with that PCID. It is not required to invalidate
    // entries in the TLBs and paging-structure caches that are associated with other PCIDs.
    &&& flush ==> {
        &&& pre.cores[core].tlb_empty_pcid(cr3.pcid)
        &&& pre.cores[core].psc_empty_pcid(cr3.pcid)
    }

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].cr3_set(cr3)),
        hist: History {
            happy: pre.hist.happy && cr3 == pre.hist.cr3 && flush,
            // if there was a flush, then we clear the walks since last invlpg
            walks: if flush { pre.hist.walks.insert(core, iset![]) } else { pre.hist.walks },
            ..pre.hist
        },
        ..pre
    }
}


/// Invlpg Instruction
pub closed spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction, ..
    &&& pre.cores[core].stbuf_empty()
    // .. evicts corresponding entries from the translation caches, ..
    // Note that per Intel Manual 3A, 4.10.4.1:
    // "INVLPG also invalidates all entries in all paging-structure caches associated with the
    // current PCID, regardless of the linear addresses to which they correspond."
    &&& pre.cores[core].psc_empty()
    // .. and waits for inflight walks to complete
    &&& pre.cores[core].walks_empty()
    // .. and evicts the corresponding TLB entry
    &&& !pre.cores[core].tlb_contains(va)
    // invlpg with lock prefix causes exception
    &&& pre.lock != Some(core)

    &&& post == State {
        hist: History {
            walks: pre.hist.walks.insert(core, iset![]),
            ..pre.hist
        },
        ..pre
    }
}


/// InvPcid Instruction
pub closed spec fn step_InvPcid(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InvPcid(core, typ)

    &&& c.valid_core(core)
    // InvPcid is a serializing instruction, ..
    &&& pre.cores[core].stbuf_empty()
    &&& pre.cores[core].walks_empty()
    // invpcid with lock prefix causes exception
    &&& pre.lock != Some(core)



    &&& match typ {
        // Individual-address invalidation: If the INVPCID type is 0, the logical processor invalidates
        // mappings—except global translations—for the linear address and PCID specified in the INVPCID
        // descriptor. In some cases, the instruction may invalidate global translations or mappings
        // for other linear addresses (or other PCIDs) as well.
        InvPcidType::IndividualAddress(d) => {
            &&& pre.cores[core].tlb_contains_pcid(d.pcid, d.vaddr)
                    ==> pre.cores[core].tlb_lookup_pcid(d.pcid, d.vaddr).flags.global()
            &&& pre.cores[core].psc_empty_pcid(d.pcid)
        }
        // Single-context invalidation: If the INVPCID type is 1, the logical processor invalidates
        // all mappings—except global translations—associated with the PCID specified in the INVPCID
        // descriptor. In some cases, the instruction may invalidate global translations or mappings
        // for other PCIDs as well.
        InvPcidType::SingleContext(d) => {
            &&& forall |pcid, vaddr| #[trigger]pre.cores[core].tlb_contains_pcid(pcid, vaddr)
                    ==> (pcid != d.pcid  || pre.cores[core].tlb_lookup_pcid(pcid, vaddr).flags.global())
            &&& pre.cores[core].psc_empty_pcid(d.pcid)
        }
        // All-context invalidation, including global translations: If the INVPCID type is 2, the
        // logical processor invalidates all mappings—including global translations—associated with any
        // PCID.
        InvPcidType::AllContextGlobal(d) => {
            &&& pre.cores[core].tlb_empty_all()
            &&& pre.cores[core].psc_empty_all()
        }
        // All-context invalidation: If the INVPCID type is 3, the logical processor invalidates all
        // mappings—except global translations—associated with any PCID. In some case, the instruction
        // may invalidate global translations as well.
        InvPcidType::AllContext(d) => {
            &&& forall |pcid, vaddr| #[trigger]pre.cores[core].tlb_contains_pcid(pcid, vaddr)
                    ==> pre.cores[core].tlb_lookup_pcid(pcid, vaddr).flags.global()
            &&& pre.cores[core].psc_empty_all()
        }
    }

    &&& post == State {
        hist: History {
            happy: pre.hist.happy && match typ {
                InvPcidType::IndividualAddress(d) => { pre.hist.cr3.pcid == d.pcid }
                InvPcidType::SingleContext(d) => { pre.hist.cr3.pcid == d.pcid },
                _ => true
            },
            walks: pre.hist.walks.insert(core, iset![]),
            ..pre.hist
        },
        ..pre
    }
}


pub closed spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    r: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)

    // Atomic sequences only happen in the kernel, so even on the core executing a locked sequence,
    // the sequence never contains userspace memory accesses.
    &&& pre.lock is None

    &&& {
    let walk_next = walk_next(pre, core, walk, r);
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.cores[core].walks_contains(walk)
    &&& walk.vaddr == memop_vaddr
    &&& walk_next.complete
    &&& walk_next.result() is Invalid
    &&& memop.is_pagefault()
    }

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].walks_remove(walk)),
        ..pre
    }
}

pub closed spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)

    // Atomic sequences only happen in the kernel, so even on the core executing a locked sequence,
    // the sequence never contains userspace memory accesses.
    &&& pre.lock is None

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.cores[core].tlb_contains(tlb_va)
    &&& {
        let pte = pre.cores[core].tlb_lookup(tlb_va);
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

    &&& post.lock == pre.lock
    &&& post.pt_mem == pre.pt_mem
    &&& post.cores == pre.cores
    &&& post.hist == pre.hist
}



// ---- Translation caching ----

pub closed spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].walks_contains(walk)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].psc_fill(walk)),
        ..pre
    }
}

pub closed spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].psc_contains(walk)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].walks_insert(walk)),
        ..pre
    }
}

pub closed spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, pcid: Pcid,  walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].psc_contains_pcid(pcid, walk)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].psc_evict(pcid, walk)),
        ..pre
    }
}


// ---- Non-atomic page table walks ----

pub closed spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& aligned(vaddr as nat, 8)
    &&& vaddr < MAX_VIRTADDR

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].walks_insert(walk)),
        hist: History {
            walks: pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk)),
            ..pre.hist
        },
        ..pre
    }
}

pub closed spec fn walk_next(state: State, core: Core, walk: Walk, r: usize) -> Walk {
    let Walk { vaddr, path, .. } = walk;
    let mem = state.pt_mem;
    let addr = if path.len() == 0 {
        add(state.cores[core].cr3.pml4, mul(l0_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
    } else { arbitrary() };
    let value = state.read_from_mem_tso(core, addr, r);
    let entry = PDE { entry: value, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory)
    };
    walk
}

pub closed spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    r: usize,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre, core, walk, r);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].walks.contains(walk)
    &&& !walk_next.complete

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].walks_replace(walk, walk_next)),
        hist: History {
            walks: pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk_next)),
            ..pre.hist
        },
        ..pre
    }
}

pub closed spec fn step_WalkAbort(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    lbl: Lbl
    ) -> bool
{
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].walks_contains(walk)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].walks_remove(walk)),
        ..pre
    }
}

/// Completes a (valid) page table walk and caches the resulting translation in the TLB.
///
/// Note: A valid walk's result is a region whose base and size depend on the path taken. E.g. a
/// huge page mapping results in a 2M-sized region. Invalid walks are always for a 4K-sized region.
pub closed spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, r: usize, lbl: Lbl) -> bool {
    let walk_next = walk_next(pre, core, walk, r);
    &&& lbl is Tau

    // XXX: do we need to have a condition here that there cannot be an existing tlb entry?

    &&& c.valid_core(core)
    &&& pre.cores[core].walks.contains(walk)
    &&& walk_next.complete
    &&& walk_next.result() matches WalkResult::Valid { vbase, pte }

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].tlb_fill(vbase, pte).walks_remove(walk)),
        ..pre
    }
}

pub closed spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_pcid: Pcid, tlb_va: Vaddr, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cores[core].tlb_contains_pcid(tlb_pcid, tlb_va)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].tlb_evict(tlb_pcid, tlb_va)),
        ..pre
    }
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
/// Write to core's local store buffer.
pub closed spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)

    &&& post == State {
        cores: pre.cores.insert(core, pre.cores[core].stbuf_push(addr, value)),
        hist: History {
            happy: pre.hist.happy && pre.is_happy_write(core, addr, value),
            cas: CASProgress::Done { core, addr },
            ..pre.hist
        },
        ..pre
    }

}

pub closed spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.cores[core].stbuf_first();
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& !pre.cores[core].stbuf_empty()
    &&& pre.not_blocked(core)

    &&& post == State {
        pt_mem: pre.pt_mem.write(addr, value),
        cores: pre.cores.insert(core, pre.cores[core].stbuf_drop()),
        ..pre
    }
}

pub closed spec fn step_Read(pre: State, post: State, c: Constants, r: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.not_blocked(core)
    &&& value == pre.read_from_mem_tso(core, addr, r)

    &&& post == State {
        hist: History {
            cas: if pre.hist.cas is NextRead && pre.hist.cas.core() == core && pre.hist.cas.addr() == addr {
                if pre.hist.cas->NextRead_expect == value {
                    CASProgress::NextWrite { core, addr, new: pre.hist.cas->NextRead_new }
                } else { CASProgress::Done { core, addr } }
            } else { pre.hist.cas },
            ..pre.hist
        },
        ..pre
    }
}

/// The `step_Barrier` transition corresponds to any memory-serializing instruction. This includes
/// `mfence` and `iret`.
pub closed spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.cores[core].stbuf_empty()

    &&& post == State {
        ..pre
    }
}

/// Indicates start of a locked instruction
pub closed spec fn step_Lock(pre: State, post: State, c: Constants, paddr: Paddr, expect: u64, new: u64, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Lock(core)

    &&& c.valid_core(core)
    &&& pre.cores[core].stbuf_empty()
    &&& pre.lock is None

    &&& post == State {
        lock: Some(core),
        hist: History {
            happy: pre.hist.happy && pre.hist.cas is NoOngoingCAS,
            cas: CASProgress::NextRead { core, addr: paddr, expect, new },
            ..pre.hist
        },
        ..pre
    }
}

/// Indicates end of a locked instruction
pub closed spec fn step_Unlock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Unlock(core)

    &&& c.valid_core(core)
    &&& pre.cores[core].stbuf_empty()
    &&& pre.lock == Some(core)

    &&& post == State {
        lock: None,
        hist: History {
            happy: pre.hist.happy && (pre.hist.cas matches CASProgress::Done { core: c, .. } && c == core),
            cas: CASProgress::NoOngoingCAS,
            ..pre.hist
        },
        ..pre
    }
}

pub closed spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        //Step::ReadWrite { paddr, wr }    => step_ReadWrite(pre, post, c, paddr, wr, lbl),
        Step::Invlpg                       => step_Invlpg(pre, post, c, lbl),
        Step::InvPcid                      => step_InvPcid(pre, post, c, lbl),
        Step::WriteCr3                     => step_WriteCr3(pre, post, c, lbl),
        Step::MemOpNoTr { walk, r }        => step_MemOpNoTr(pre, post, c, walk, r, lbl),
        Step::MemOpTLB { tlb_va }          => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::CacheFill { core, walk }     => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }      => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, pcid, walk }    => step_CacheEvict(pre, post, c, core, pcid, walk, lbl),
        Step::WalkInit { core, vaddr }     => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, r }   => step_WalkStep(pre, post, c, core, walk, r, lbl),
        Step::WalkAbort { core, walk }     => step_WalkAbort(pre, post, c, core, walk, lbl),
        Step::TLBFill { core, walk, r }    => step_TLBFill(pre, post, c, core, walk, r, lbl),
        Step::TLBEvict { core, tlb_pcid,  tlb_va }    => step_TLBEvict(pre, post, c, core, tlb_pcid, tlb_va, lbl),
        //Step::WalkDone { core, walk, r } => step_WalkDone(pre, post, c, core, walk, r, lbl),
        Step::Write                        => step_Write(pre, post, c, lbl),
        Step::Writeback { core }           => step_Writeback(pre, post, c, core, lbl),
        Step::Read { r }                   => step_Read(pre, post, c, r, lbl),
        Step::Barrier                      => step_Barrier(pre, post, c, lbl),
        Step::Lock { addr, expect, new }   => step_Lock(pre, post, c, addr, expect, new, lbl),
        Step::Unlock                       => step_Unlock(pre, post, c, lbl),
        Step::Stutter                      => step_Stutter(pre, post, c, lbl),
    }
}

pub closed spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.cores === IMap::new(|core| c.valid_core(core), |core| CoreState::new(c.cr3))

    // the PMl4 must match
    &&& pre.hist.happy == true
    &&& pre.hist.walks === IMap::new(|core| c.valid_core(core), |core| iset![])
    &&& pre.hist.cr3 == c.cr3
    &&& pre.hist.cas == CASProgress::NoOngoingCAS

    &&& pre.lock is None
    &&& pre.pt_mem.mem === IMap::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8), |va| 0)
    &&& pre.pt_mem.pml4 == c.cr3.pml4
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& c.memories_disjoint()
    &&& pre.phys_mem.len() == c.range_mem.1
    &&& c.in_ptmem_range(pre.pt_mem.pml4 as nat, 4096)
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}





// Invariants for this state machine

impl State {
    pub closed spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.cores.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.walks.contains_key(core)
        // &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].wf()
        &&& forall|core| #[trigger] self.cores.contains_key(core) ==> self.cores[core].wf()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.walks[core].finite()
    }

    pub closed spec fn inv_inflight_walks(self, c: Constants) -> bool {
        &&& forall|core, walk| c.valid_core(core) && #[trigger](self.cores[core]).walks_contains(walk) ==> {
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
        }
        &&& forall|core, pcid, walk| c.valid_core(core) && self.cores[core].psc_contains_pcid(pcid, walk) ==> {
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
        }
    }

    pub closed spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].walks.subset_of(self.hist.walks[core])
    }

    // phrase this only for the current pcid.
    pub closed spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core, walk|
            c.valid_core(core) &&   #[trigger] self.cores[core].psc_contains(walk)
                ==> #[trigger] self.hist.walks[core].contains(walk)
    }

    pub closed spec fn inv_cache_no_other_entries(self, c: Constants) -> bool {
        forall |core, pcid| c.valid_core(core) && pcid != self.hist.cr3.pcid ==>
            (#[trigger] self.cores[core].psc[pcid]).is_empty()
    }

    pub closed spec fn inv_unlocked_stbuf_empty(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) && self.lock != Some(core) ==> self.cores[core].stbuf_empty()
    }

    pub closed spec fn inv_cr3_match(self, c: Constants) -> bool {
        // the history CR3 value must be the one in PTMem
        &&& self.hist.cr3.pml4 == self.pt_mem.pml4
        // all cores have the same cr3 value
        &&& forall |core| #[trigger]c.valid_core(core)
            ==> self.cores[core].cr3 == self.hist.cr3
    }

    // pub closed spec fn inv_cache_no_other_entries(self, c: Constants) -> bool {
    //     forall |core, pcid| c.valid_core(core) && pcid != self.hist.cr3.pcid ==>
    //         self.cores[core].psc[pcid].is_empty()
    // }

    pub closed spec fn inv(self, c: Constants) -> bool {
        &&& self.wf(c)
        &&& self.hist.happy ==> {
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].inv()
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].cr3 == self.hist.cr3
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.cr3.pml4 == self.pt_mem.pml4
            &&& self.inv_walks_subset_of_hist_walks(c)
            &&& self.inv_cache_subset_of_hist_walks(c)
            &&& self.inv_cache_no_other_entries(c)
            &&& self.inv_unlocked_stbuf_empty(c)
            &&& self.inv_cr3_match(c)
        }
    }

    pub closed spec fn not_blocked(self, core: Core) -> bool {
        self.lock == Some(core) || self.lock is None
    }
} // impl State


pub proof fn init_implies_inv(pre: State, c: Constants)
    requires init(pre, c)
    ensures pre.inv(c)
{}

pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.inv(c),
        next(pre, post, c, lbl),
    ensures post.inv(c)
{
    assert forall |c| #[trigger] pre.cores.contains_key(c) implies
        pre.cores[c].wf() && post.cores[c].wf() by {
            assert(pre.cores[c].tlb.dom() == post.cores[c].tlb.dom());
            assert(pre.cores[c].psc.dom() == post.cores[c].psc.dom());
        }
    assert(post.hist.cr3 == pre.hist.cr3);

    if post.hist.happy {
        let step = choose|step| next_step(pre, post, c, step, lbl);
        match step {
            Step::Invlpg                       => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::InvPcid                      => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::WriteCr3                     => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::MemOpNoTr { walk, r }        => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::MemOpTLB { tlb_va }          => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::CacheFill { core, walk }     => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::CacheUse { core, walk }      => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::CacheEvict { core, pcid, walk }    => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::WalkInit { core, vaddr }     => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::WalkStep { core, walk, r }   => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::WalkAbort { core, walk }     => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::TLBFill { core, walk, r }    => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::TLBEvict { core, tlb_pcid, tlb_va }    => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::Write                        => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::Writeback { core }           => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::Read { r }                   => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::Barrier                      => { assert(post.inv_unlocked_stbuf_empty(c)); }
            Step::Stutter                      => {
                assert(post.inv_unlocked_stbuf_empty(c));
            }
            _ => assert(post.inv_unlocked_stbuf_empty(c))
        }
    }
}

// $line_count$}$


proof fn lemma_mem_view_after_step_write(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.hist.happy,
        post.hist.happy,
        pre.wf(c),
        // pre.inv_sbuf_facts(c),
        step_Write(pre, post, c, lbl),
    ensures
        post.writer_mem().pml4 == pre.pt_mem.pml4,
        post.writer_mem().mem  == pre.writer_mem().mem.insert(lbl->Write_1, lbl->Write_2),
{
    admit();
    // let (core, wraddr, value) =
    //     if let Lbl::Write(core, addr, value) = lbl {
    //         (core, addr, value)
    //     } else { arbitrary() };
    // reveal_with_fuel(vstd::seq::Seq::fold_left, 5);
    // if post.writes.core == pre.writes.core {
    //     pre.pt_mem.lemma_write_seq_push(pre.writer_sbuf(), wraddr, value);
    // } else {
    //     assert_by_contradiction!(pre.writer_sbuf() =~= seq![], {
    //         assert(pre.writes.tso.contains(pre.writer_sbuf()[0].0));
    //     });
    // }
}

proof fn lemma_step_Writeback_preserves_writer_mem(pre: State, post: State, c: Constants, core: Core, lbl: Lbl)
    requires
        // pre.inv_sbuf_facts(c),
        step_Writeback(pre, post, c, core, lbl),
    ensures post.writer_mem() == pre.writer_mem()
{
    // assert(post.writes.core == core);
    pt_mem::PTMem::lemma_write_seq_first(pre.pt_mem, pre.cores[core].stbuf);
}


pub mod refinement {
    use vstd::pervasive::arbitrary;

    #[cfg(verus_keep_ghost)]
    use crate::extra::lemma_bits_misc;
    use crate::spec_t::cas_mmu::*;
    use crate::spec_t::cas_mmu::rl1;
    use crate::spec_t::cas_mmu::rl3;
    #[cfg(verus_keep_ghost)]
    use crate::spec_t::cas_mmu::rl3::bit;
    use crate::spec_t::cas_mmu::translation::{ MASK_DIRTY_ACCESS, MASK_NEG_DIRTY_ACCESS };

    impl rl3::CoreState {
        #[verifier(inline)]
        pub open spec fn interp(self, walks: ISet<Walk>) -> rl1::CoreState {
            rl1::CoreState {
                cr3: self.cr3.pml4,
                tlb: self.tlb[self.pcid()],
            }
        }
    }

    impl rl3::State {
        pub closed spec fn interp(self) -> rl1::State {
            rl1::State {
                happy: self.hist.happy,
                cas: self.hist.cas,
                cr3: self.hist.cr3,
                phys_mem: self.phys_mem,
                pt_mem: self.writer_mem(),
                cores: self.cores.map_entries(|k, v:rl3::CoreState| v.interp(self.hist.walks[k])),
            }
        }
    }

    impl rl3::Step {
        pub closed spec fn interp(self, pre: rl3::State, c: Constants, lbl: Lbl) -> rl1::Step {
            if pre.hist.happy {
                match self {
                    rl3::Step::Invlpg                     => rl1::Step::Invlpg,
                    rl3::Step::InvPcid                    => {
                        if let Lbl::InvPcid(core, typ) = lbl {
                            match typ {
                                InvPcidType::IndividualAddress(d) => {
                                    if pre.hist.cr3.pcid == d.pcid {
                                        rl1::Step::InvPcid
                                    } else {
                                        rl1::Step::InvPcidSad
                                    }
                                }
                                InvPcidType::SingleContext(d) => {
                                    if pre.hist.cr3.pcid == d.pcid {
                                        rl1::Step::InvPcid
                                    } else {
                                        rl1::Step::InvPcidSad
                                    }
                                },
                                _ => rl1::Step::InvPcid
                            }
                        } else {
                            arbitrary()
                        }
                    }
                    rl3::Step::WriteCr3                   => {
                        if let Lbl::WriteCr3(core, cr3, flush) = lbl {
                            if cr3 == pre.hist.cr3 && flush {
                                rl1::Step::WriteCr3
                            } else {
                                rl1::Step::SadWriteCr3
                            }
                        } else {
                            arbitrary()
                        }
                    }
                    rl3::Step::MemOpNoTr { walk, r }      => rl1::Step::MemOpNoTr,
                    rl3::Step::MemOpTLB { tlb_va }        => rl1::Step::MemOpTLB { tlb_va },
                    rl3::Step::CacheFill { core, walk }   => rl1::Step::Stutter,
                    rl3::Step::CacheUse { core, walk }    => rl1::Step::Stutter,
                    rl3::Step::CacheEvict { core, pcid, walk }  => rl1::Step::Stutter,
                    rl3::Step::WalkInit { core, vaddr }   => rl1::Step::Stutter,
                    rl3::Step::WalkStep { core, walk, r } => rl1::Step::Stutter,
                    rl3::Step::WalkAbort { core, walk }   => rl1::Step::Stutter,
                    rl3::Step::TLBFill { core, walk, r }  => {
                        let walk_na_res = rl3::walk_next(pre, core, walk, r).result();
                        let vbase = walk_na_res->Valid_vbase;
                        rl1::Step::TLBFill { core, vaddr: vbase }
                    },
                    rl3::Step::TLBEvict { core, tlb_pcid, tlb_va }  => {
                        if tlb_pcid == pre.hist.cr3.pcid {
                            rl1::Step::TLBEvict { core, tlb_va }
                        } else {
                            rl1::Step::Stutter
                        }
                    },
                    rl3::Step::Write                      => {
                        let (core, addr, value) =
                            if let Lbl::Write(core, addr, value) = lbl {
                                (core, addr, value)
                            } else { arbitrary() };

                        if pre.is_happy_write(core, addr, value) {
                            rl1::Step::CASWrite
                        } else {
                            rl1::Step::SadWrite
                        }
                    },
                    rl3::Step::Writeback { core } => rl1::Step::Stutter,
                    rl3::Step::Read { r }         => {
                        let core = lbl->Read_0;
                        let addr = lbl->Read_1;
                        if pre.hist.cas is NextRead && pre.hist.cas.core() == core && pre.hist.cas.addr() == addr {
                            rl1::Step::CASRead
                        } else {
                            rl1::Step::Read
                        }
                    },
                    rl3::Step::Barrier            => rl1::Step::Barrier,
                    rl3::Step::Lock { addr, expect, new } => {
                        if pre.hist.cas is NoOngoingCAS {
                            rl1::Step::Lock { addr, expect, new }
                        } else {
                            rl1::Step::SadLock
                        }
                    },
                    rl3::Step::Unlock             => {
                        if pre.hist.cas matches rl3::CASProgress::Done { core, .. } && core == lbl->Unlock_0 {
                            rl1::Step::Unlock
                        } else {
                            rl1::Step::SadUnlock
                        }
                    },
                    rl3::Step::Stutter            => rl1::Step::Stutter,
                }
            } else {
                rl1::Step::Sadness
            }
        }
    }

    broadcast proof fn lemma_mask_dirty_access_after_xor(v: usize, r: usize)
        ensures
            #[trigger] (v ^ (r & MASK_DIRTY_ACCESS)) & MASK_NEG_DIRTY_ACCESS
                            == v & MASK_NEG_DIRTY_ACCESS
    {
        assert((v ^ (r & ((bit!(5) | bit!(6))))) & (!(bit!(5) | bit!(6)))
                == v & (!(bit!(5) | bit!(6)))) by (bit_vector);
    }

    // /// The value of r is irrelevant, so we can just ignore it.
    // broadcast proof fn rl3_walk_next_is_rl1_walk_next(state: rl3::State, core: Core, walk: Walk, r: usize)
    //     requires walk.path.len() <= 3,
    //         state.cores.contains_key(core),
    //         state.cores[core].cr3.pml4 == state.pt_mem.pml4
    //     ensures
    //     #[trigger] rl3::walk_next(state, core, walk, r)
    //             == rl1::walk_next(state.interp().core_mem(core), walk)
    // {
    //
    //     reveal(rl1::walk_next);
    //     state.pt_mem.lemma_write_seq(state.interp().cores[core].stbuf);
    //     broadcast use
    //         lemma_mask_dirty_access_after_xor,
    //         PDE::lemma_view_unchanged_dirty_access;
    // }

    #[verifier(spinoff_prover)]
    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: Constants, step: rl3::Step, lbl: Lbl)
        requires
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl1::next_step(pre.interp(), post.interp(), c, step.interp(pre, c, lbl), lbl)
    {
        if pre.hist.happy {
            assert(pre.interp().cores.dom() == post.interp().cores.dom());
            match step {
                rl3::Step::Invlpg => {
                    assert(rl1::step_Invlpg(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::InvPcid => {
                    let core = lbl->InvPcid_0;
                    let typ = lbl->InvPcid_1;
                    match typ {
                        InvPcidType::IndividualAddress(d) => {
                            if d.pcid == pre.hist.cr3.pcid {
                                assert(rl1::step_InvPcid(pre.interp(), post.interp(), c, lbl));
                            } else {
                                assert(!post.hist.happy);
                                assert(rl1::step_InvPcidSad(pre.interp(), post.interp(), c, lbl));
                            }
                        }
                        InvPcidType::SingleContext(d) => {
                            if d.pcid == pre.hist.cr3.pcid {
                                assert(rl1::step_InvPcid(pre.interp(), post.interp(), c, lbl));
                            } else {
                                assert(!post.interp().happy);
                                assert(rl1::step_InvPcidSad(pre.interp(), post.interp(), c, lbl));
                            }
                        }
                        _ => {
                            // assert(post.interp().cores == pre.interp().cores.insert(core,
                            //     pre.interp().cores[core].walks_clear()
                            // ));
                            assert(rl1::step_InvPcid(pre.interp(), post.interp(), c, lbl));
                        }
                    }
                }
                rl3::Step::WriteCr3 => {
                    let core = lbl->WriteCr3_0;
                    let cr3 = lbl->WriteCr3_1;
                    let flush = lbl->WriteCr3_2;
                    if cr3 == pre.hist.cr3 && flush {
                        assert(post.cores =~= pre.cores);
                        assert(rl1::step_WriteCr3(pre.interp(), post.interp(), c, lbl));
                    } else {
                        assert(!post.interp().happy);
                        assert(rl1::step_SadWriteCr3(pre.interp(), post.interp(), c, lbl));
                    }
                }
                rl3::Step::MemOpNoTr { walk, r } => {
                    let core = lbl->MemOp_0;
                    // rl3_walk_next_is_rl1_walk_next(pre, core, walk, r);
                    assume(pre.hist.cas is NoOngoingCAS <==> pre.lock is None);
                    admit(); // TODO: needs some work, check rl2

                    assert(post.interp().cores == pre.interp().cores);
                    assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::MemOpTLB { tlb_va } => {
                    assert(rl1::step_MemOpTLB(pre.interp(), post.interp(), c, tlb_va, lbl));
                },
                rl3::Step::CacheFill { core, walk } => {
                    assert(post.interp().cores == pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheUse { core, walk } => {
                    assert(post.interp().cores == pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheEvict { core, pcid, walk } => {
                    assert(post.interp().cores == pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::WalkInit { core, vaddr } => {
                    assert(post.interp().cores =~= pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::WalkStep { core, walk, r } => {
                    assert(post.interp().cores =~= pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::WalkAbort { core, walk } => {
                    assert(post.interp().cores == pre.interp().cores);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::TLBFill { core, walk, r } => {
                    admit();
                    // rl3_walk_next_is_rl1_walk_next(pre, core, walk, r);
                    let wnext = crate::spec_t::cas_mmu::rl3::walk_next(pre, core, walk, r);
                    let vbase = wnext.result()->Valid_vbase;
                    let pte = wnext.result()->Valid_pte;
                    assert(post.interp().cores == pre.interp().cores.insert(core,
                            pre.interp().cores[core].tlb_fill(vbase, pte)));
                    assert(rl1::step_TLBFill(pre.interp(), post.interp(), c, core, vbase, lbl));
                },
                rl3::Step::TLBEvict { core, tlb_pcid, tlb_va } => {
                    if tlb_pcid == pre.hist.cr3.pcid {
                        assert(post.interp().cores == pre.interp().cores.insert(core, pre.interp().cores[core].tlb_evict(tlb_va)));
                        assert(rl1::step_TLBEvict(pre.interp(), post.interp(), c, core, tlb_va, lbl));
                    } else {
                        assert(post.interp().cores =~= pre.interp().cores);
                        assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Write => {
                    let (core, addr, value) =
                        if let Lbl::Write(core, addr, value) = lbl {
                            (core, addr, value)
                        } else { arbitrary() };

                    if pre.is_happy_write(core, addr, value) {
                        assume(pre.lock == Some(core));
                        // lemma_bits_misc();
                        pre.pt_mem.lemma_write_seq(pre.cores[core].stbuf);
                        rl3::lemma_mem_view_after_step_write(pre, post, c, lbl);
                        assert(post.interp().cores =~= pre.interp().cores);
                        assert(rl1::step_CASWrite(pre.interp(), post.interp(), c, lbl));
                    } else {
                        assert(rl1::step_SadWrite(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Writeback { core } => {
                    assert(post.interp().cores =~= pre.interp().cores);
                    rl3::lemma_step_Writeback_preserves_writer_mem(pre, post, c, core, lbl);
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::Read { r } => {
                    let core = lbl->Read_0;
                    let addr = lbl->Read_1;
                    broadcast use lemma_mask_dirty_access_after_xor;

                    if pre.hist.cas is NextRead && pre.hist.cas.core() == core && pre.hist.cas.addr() == addr {
                        assert(rl1::step_CASRead(pre.interp(), post.interp(), c, lbl));
                    } else {
                        assert(rl1::step_Read(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Barrier => {
                    assert(rl1::step_Barrier(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::Lock { addr, expect, new } => {
                    if pre.hist.cas is NoOngoingCAS {
                        assert(post.hist.happy);
                        assert(rl1::step_Lock(pre.interp(), post.interp(), c, addr, expect, new, lbl));
                    } else {
                        assert(rl1::step_SadLock(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Unlock => {
                    if pre.hist.cas matches rl3::CASProgress::Done { core, .. } && core == lbl->Unlock_0 {
                        assert(rl1::step_Unlock(pre.interp(), post.interp(), c, lbl));
                    } else {
                        assert(rl1::step_SadUnlock(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Stutter => {
                    assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
            }
        } else {
            assert(rl1::step_Sadness(pre.interp(), post.interp(), c, lbl));
        }
    }

    proof fn init_refines(pre: rl3::State, c: Constants)
        requires rl3::init(pre, c),
        ensures rl1::init(pre.interp(), c),
    {
        assert(pre.interp().cores === IMap::new(|core| c.valid_core(core), |core| rl1::CoreState::new(c.cr3.pml4)));
    }

    proof fn next_refines(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
        requires
            pre.inv(c),
            rl3::next(pre, post, c, lbl),
        ensures
            rl1::next(pre.interp(), post.interp(), c, lbl),
    {
        let step = choose|step: rl3::Step| rl3::next_step(pre, post, c, step, lbl);
        next_step_refines(pre, post, c, step, lbl);
    }

    // pub mod to_rl1 {
    //     //! Machinery to lift rl3 semantics to rl1 (interp twice and corresponding lemmas), which we use for
    //     //! reasoning about the OS state machine.
    //
    //     use crate::spec_t::cas_mmu::*;
    //     use crate::spec_t::cas_mmu::rl3;
    //     use crate::spec_t::cas_mmu::rl1;
    //
    //     impl rl3::State {
    //         pub open spec fn view(self) -> rl1::State {
    //             self.interp().interp()
    //         }
    //     }
    //
    //     pub proof fn init_implies_inv(pre: rl3::State, c: Constants)
    //         requires rl3::init(pre, c),
    //         ensures
    //             pre.inv(c),
    //             pre.interp().inv(c),
    //             pre@.happy
    //     {
    //         reveal(rl2::State::wf_ptmem_range);
    //     }
    //
    //     pub broadcast proof fn next_preserves_inv(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
    //         requires
    //             pre.inv(c),
    //             pre.interp().inv(c),
    //             #[trigger] rl3::next(pre, post, c, lbl),
    //         ensures
    //             post.inv(c),
    //             post.interp().inv(c),
    //     {
    //         rl3::next_preserves_inv(pre, post, c, lbl);
    //         rl3::refinement::next_refines(pre, post, c, lbl);
    //         rl2::next_preserves_inv(pre.interp(), post.interp(), c, lbl);
    //     }
    //
    //     pub proof fn init_refines(pre: rl3::State, c: Constants)
    //         requires rl3::init(pre, c),
    //         ensures rl1::init(pre@, c),
    //     {
    //         assert(pre@.cores == IMap::new(|core| c.valid_core(core), |core| rl1::CoreState::new(c.cr3.pml4)));
    //
    //     }
    //
    //     pub broadcast proof fn next_refines(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
    //         requires
    //             pre.inv(c),
    //             pre.interp().inv(c),
    //             #[trigger] rl3::next(pre, post, c, lbl),
    //         ensures
    //             rl1::next(pre@, post@, c, lbl),
    //     {
    //         rl3::refinement::next_refines(pre, post, c, lbl);
    //         rl2::refinement::next_refines(pre.interp(), post.interp(), c, lbl);
    //     }
    // }
}


} // verus!
