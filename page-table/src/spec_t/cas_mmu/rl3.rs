use vstd::prelude::*;
use vstd::assert_by_contradiction;

#[cfg(verus_keep_ghost)]
use crate::extra::lemma_bits_misc;
use crate::spec_t::cas_mmu::*;
use crate::spec_t::cas_mmu::pt_mem::*;
use crate::spec_t::cas_mmu::defs::{ bit, Core, bitmask_inc, MemOp, LoadResult, PTE, Vpn, Paddr, Vaddr, Pcid, Cr3 };
#[cfg(verus_keep_ghost)]
use crate::spec_t::cas_mmu::defs::{ aligned, update_range, MAX_VIRTADDR, MAX_PHYADDR_WIDTH, axiom_max_phyaddr_width_facts };
use crate::spec_t::cas_mmu::translation::{ l0_bits, l1_bits, l2_bits, l3_bits, MASK_DIRTY_ACCESS, MASK_NEG_DIRTY_ACCESS };

verus! {

// Hardware model which includes support for atomics/CAS, using the lock/unlock modeling from the paper 
// "A Better x86 Memory Model: x86-TSO" by Sewell et al.
// Note: That paper shows that it is sound to model atomic instructions with lock/unlock
// transitions. We adopt this modeling for kernel and userspace memory accesses but still permit MMU
// memory reads and other MMU actions to take place, even when the lock is held. This modeling might
// be overly conservative but as it is sufficient for our purposes, we avoid making a stronger
// assumption.
//
// Refines directly to rl1, without the intermediate rl2 in the main development.


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
        &&& forall|p| #[trigger] self.tlb.contains_key(p) ==> self.tlb[p].dom().finite()

        // the PSC is a full/total map from PCID -> ISet<Walk> and its set with the cached
        // partial walks is finite
        &&& self.psc.is_full()    //
        &&& forall|p| #[trigger] self.psc.contains_key(p) ==> self.psc[p].finite()

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
        expect: usize,
        new: usize,
    },
    NextWrite {
        core: Core,
        addr: Paddr, 
        new: usize,
    },
    Done {
        core: Core,
        addr: Paddr,
        new: usize,
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
    Lock { addr: Paddr, expect: usize, new: usize }, // These are ghost arguments, not part of lock itself
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

    pub closed spec fn writer_sbuf(self) -> Seq<(usize, usize)>
        // recommends self.lock is Some
    {
        self.cores[self.lock->Some_0].stbuf
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

    &&& post == pre
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
            cas: CASProgress::Done { core, addr, new: value },
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
                } else { CASProgress::Done { core, addr, new: pre.hist.cas->NextRead_new } }
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
pub closed spec fn step_Lock(pre: State, post: State, c: Constants, paddr: Paddr, expect: usize, new: usize, lbl: Lbl) -> bool {
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
        // &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].wf()
        &&& forall|core| #[trigger] self.cores.contains_key(core) ==> self.cores[core].wf()
        &&& self.lock matches Some(core) ==> c.valid_core(core)
        &&& aligned(self.pt_mem.pml4 as nat, 4096)
        &&& c.in_ptmem_range(self.pt_mem.pml4 as nat, 4096)
        &&& c.memories_disjoint()
        &&& self.wf_ptmem_range(c)
    }

    // For some reason this causes issues in a few proofs, so making it opaque
    #[verifier(opaque)]
    pub closed spec fn wf_ptmem_range(self, c: Constants) -> bool {
        //self.pt_mem.mem.dom() === ISet::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8))
        &&& forall|va| #[trigger] self.pt_mem.mem.contains_key(va)
            <==> aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8)
        &&& forall|i| #![auto] self.lock is Some && 0 <= i < self.cores[self.lock->Some_0].stbuf.len() ==> {
            &&& c.in_ptmem_range(self.cores[self.lock->Some_0].stbuf[i].0 as nat, 8)
            &&& aligned(self.cores[self.lock->Some_0].stbuf[i].0 as nat as nat, 8)
        }
    }

    pub closed spec fn inv_inflight_walks_are_prefixes(self, c: Constants) -> bool {
        &&& forall|core, walk| c.valid_core(core) && #[trigger] self.cores[core].walks_contains(walk) ==> {
            &&& walk.vaddr < MAX_VIRTADDR
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            &&& is_iter_walk_prefix(self.core_mem(core), walk)
        }
        &&& forall|core, pcid, walk| c.valid_core(core) && #[trigger] self.cores[core].psc_contains_pcid(pcid, walk) ==> {
            &&& walk.vaddr < MAX_VIRTADDR
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            &&& is_iter_walk_prefix(self.core_mem(core), walk)
        }
    }

    pub closed spec fn inv_cache_no_other_entries(self, c: Constants) -> bool {
        forall |core, pcid| c.valid_core(core) && pcid != self.hist.cr3.pcid ==>
            (#[trigger] self.cores[core].psc[pcid]).is_empty()
    }

    pub closed spec fn inv_unlocked_stbuf_empty(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) && self.lock != Some(core) ==> self.cores[core].stbuf == seq![]
    }

    pub closed spec fn inv_cas_progress(self, c: Constants) -> bool {
        &&& self.hist.cas !is NoOngoingCAS <==> self.lock is Some
        &&& self.lock matches Some(core) ==> self.hist.cas.core() == core
        &&& match self.hist.cas {
            CASProgress::NoOngoingCAS => true,
            CASProgress::NextRead { core, .. }
            | CASProgress::NextWrite { core, .. } => self.cores[core].stbuf == seq![],
            CASProgress::Done { core, addr, new } => {
                self.cores[core].stbuf == seq![] || self.cores[core].stbuf == seq![(addr, new)]
            },
        }
    }

    pub closed spec fn inv_cr3_match(self, c: Constants) -> bool {
        // the history CR3 value must be the one in PTMem
        &&& self.hist.cr3.pml4 == self.pt_mem.pml4
        // all cores have the same cr3 value
        &&& forall|core| #[trigger] c.valid_core(core)
            ==> self.cores[core].cr3 == self.hist.cr3
    }

    /// If any non-writer core reads a value that has the P bit set, we know that no write for that address is
    /// in the writer's store buffer.
    pub closed spec fn inv_valid_is_not_in_sbuf(self, c: Constants) -> bool {
        forall|core, addr: usize|
            c.valid_core(core) && aligned(addr as nat, 8) &&
            self.lock is Some && self.lock != Some(core) &&
            #[trigger] self.core_mem(core).read(addr) & 1 == 1
                ==> !self.writer_sbuf().contains_fst(addr)
    }

    pub closed spec fn inv(self, c: Constants) -> bool {
        &&& self.hist.happy ==> {
            &&& self.wf(c)
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].inv()
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.cores[core].cr3 == self.hist.cr3
            &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.cr3.pml4 == self.pt_mem.pml4
            &&& self.inv_inflight_walks_are_prefixes(c)
            &&& self.inv_valid_is_not_in_sbuf(c)
            &&& self.inv_cache_no_other_entries(c)
            &&& self.inv_unlocked_stbuf_empty(c)
            &&& self.inv_cas_progress(c)
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
{
    reveal(State::wf_ptmem_range);
}

pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.inv(c),
        next(pre, post, c, lbl),
    ensures post.inv(c)
{
    reveal(State::wf_ptmem_range);
    if post.hist.happy {
        assert forall |c| #[trigger] pre.cores.contains_key(c) implies
            pre.cores[c].wf() && post.cores[c].wf() by {
                assert(pre.cores[c].tlb.dom() == post.cores[c].tlb.dom());
                assert(pre.cores[c].psc.dom() == post.cores[c].psc.dom());
            }
        assert(post.hist.cr3 == pre.hist.cr3);

        let step = choose|step| next_step(pre, post, c, step, lbl);
        next_step_preserves_wf(pre, post, c, step, lbl);
        next_step_preserves_inv_inflight_walks_are_prefixes(pre, post, c, step, lbl);
        next_step_preserves_inv_valid_is_not_in_sbuf(pre, post, c, step, lbl);
        match step {
            Step::Invlpg                       => { assert(post.inv(c)); }
            Step::InvPcid                      => { assert(post.inv(c)); }
            Step::WriteCr3                     => { assert(post.inv(c)); }
            Step::MemOpNoTr { walk, r }        => { assert(post.inv(c)); }
            Step::MemOpTLB { tlb_va }          => { assert(post.inv(c)); }
            Step::CacheFill { core, walk }     => { assert(post.inv(c)); }
            Step::CacheUse { core, walk }      => { assert(post.inv(c)); }
            Step::CacheEvict { core, pcid, walk }    => { assert(post.inv(c)); }
            Step::WalkInit { core, vaddr }     => { assert(post.inv(c)); }
            Step::WalkStep { core, walk, r }   => { assert(post.inv(c)); }
            Step::WalkAbort { core, walk }     => { assert(post.inv(c)); }
            Step::TLBFill { core, walk, r }    => { assert(post.inv(c)); }
            Step::TLBEvict { core, tlb_pcid, tlb_va }    => { assert(post.inv(c)); }
            Step::Write                        => { assert(post.inv(c)); }
            Step::Writeback { core }           => {
                assert(post.writer_sbuf() == seq![]);
                assert(post.inv(c));
            }
            Step::Read { r }                   => { assert(post.inv(c)); }
            Step::Barrier                      => { assert(post.inv(c)); }
            Step::Lock { addr, expect, new }   => { assert(post.inv(c)); }
            Step::Unlock                      => { assert(post.inv(c)); }
            Step::Stutter                      => {
                assert(post.inv(c));
            }
        }
    }
}

proof fn next_step_preserves_inv_valid_is_not_in_sbuf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.hist.happy,
        post.hist.happy,
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_valid_is_not_in_sbuf(c)
{
    broadcast use lemma_step_core_mem;
}

#[verifier(spinoff_prover)]
proof fn next_step_preserves_inv_inflight_walks_are_prefixes(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        pre.hist.happy,
        post.hist.happy,
        pre.inv_cr3_match(c),
        pre.inv_cas_progress(c),
        pre.inv_unlocked_stbuf_empty(c),
        post.inv_unlocked_stbuf_empty(c),
        pre.inv_valid_is_not_in_sbuf(c),
        pre.inv_inflight_walks_are_prefixes(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_inflight_walks_are_prefixes(c)
{
    broadcast use
        lemma_core_mem_pml4,
        lemma_step_core_mem,
        lemma_walk_next_is_walk_next_alt;
    match step {
        Step::WalkStep { core, walk, r } => {
            reveal(rl3::walk_next_alt);
            assert(post.inv_inflight_walks_are_prefixes(c));
        },
        Step::Write => {
            let wrcore = lbl->Write_0;
            let wraddr = lbl->Write_1;
            let value = lbl->Write_2;
            assert(post.inv_inflight_walks_are_prefixes(c)) by {
                assert forall|core, walk|
                    c.valid_core(core) && #[trigger] post.cores[core].walks_contains(walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        reveal(rl3::walk_next_alt);
                        lemma_mem_view_after_step_write(pre, post, c, lbl);
                        pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                        assert(post.core_mem(core) == post.writer_mem());
                    }
                };
                assert forall|core, pcid, walk|
                    c.valid_core(core) && #[trigger] post.cores[core].psc_contains_pcid(pcid, walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        reveal(rl3::walk_next_alt);
                        lemma_mem_view_after_step_write(pre, post, c, lbl);
                        pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                        assert(post.core_mem(core) == post.writer_mem());
                    }
                };
            };
        },
        Step::Writeback { core: wrcore } => {
            let wraddr = pre.writer_sbuf()[0].0;
            let value = pre.writer_sbuf()[0].1;
            assert(post.inv_inflight_walks_are_prefixes(c)) by {
                assert forall|core, walk|
                    c.valid_core(core) && #[trigger] post.cores[core].walks_contains(walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        lemma_step_Writeback_preserves_writer_mem(pre, post, c, core, lbl);
                    } else {
                        lemma_writeback_other_core_preserves_walk_prefix(pre, post, c, core, wrcore, walk, step, lbl);
                    }
                };
                assert forall|core, pcid, walk|
                    c.valid_core(core) && #[trigger] post.cores[core].psc_contains_pcid(pcid, walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        lemma_step_Writeback_preserves_writer_mem(pre, post, c, core, lbl);
                    } else {
                        lemma_writeback_other_core_preserves_psc_walk_prefix(pre, post, c, core, wrcore, pcid, walk, step, lbl);
                    }
                };
            };
        },
        _ => assert(post.inv_inflight_walks_are_prefixes(c)),
    }
}

proof fn lemma_writeback_other_core_preserves_walk_prefix(
    pre: State, post: State, c: Constants, core: Core, wrcore: Core, walk: Walk, step: Step, lbl: Lbl
)
    requires
        pre.wf(c),
        pre.hist.happy,
        post.hist.happy,
        pre.inv_unlocked_stbuf_empty(c),
        post.inv_unlocked_stbuf_empty(c),
        pre.inv_valid_is_not_in_sbuf(c),
        pre.inv_inflight_walks_are_prefixes(c),
        c.valid_core(core),
        pre.cores[core].walks_contains(walk),
        next_step(pre, post, c, step, lbl),
        step == (Step::Writeback { core: wrcore }),
        core != wrcore,
    ensures
        is_iter_walk_prefix(post.core_mem(core), walk),
{
    broadcast use lemma_core_mem_pml4, lemma_step_core_mem, lemma_walk_next_is_walk_next_alt;
    reveal(rl3::walk_next_alt);
    assert(!walk.complete);
    pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
    post.pt_mem.lemma_write_seq(post.writer_sbuf());
    assert(bit!(0usize) == 1) by (bit_vector);
    assert(pre.core_mem(core) == pre.pt_mem);
    assert(post.core_mem(core) == post.pt_mem);
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> aligned(walk.path[i].0 as nat, 8)) by {
        broadcast use PDE::lemma_view_addr_aligned;
        crate::spec_t::cas_mmu::translation::lemma_bit_indices_less_512(walk.vaddr);
    };
    let wraddr = pre.cores[wrcore].stbuf_first().0;
    assert(pre.writer_sbuf().contains_fst(wraddr));
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> walk.path[i].0 != wraddr) by {
        assert forall|i| 0 <= i < walk.path.len() implies #[trigger] walk.path[i].0 != wraddr by {
            assert(pre.core_mem(core).read(walk.path[i].0) & 1 == 1);
            assert(!pre.writer_sbuf().contains_fst(walk.path[i].0));
        };
    };
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==>
        pre.pt_mem.read(walk.path[i].0) == post.pt_mem.read(walk.path[i].0));
    lemma_iter_walk_prefix_mem_agree(pre.pt_mem, post.pt_mem, walk);
}

proof fn lemma_writeback_other_core_preserves_psc_walk_prefix(
    pre: State, post: State, c: Constants, core: Core, wrcore: Core, pcid: Pcid, walk: Walk, step: Step, lbl: Lbl
)
    requires
        pre.wf(c),
        pre.hist.happy,
        post.hist.happy,
        pre.inv_unlocked_stbuf_empty(c),
        post.inv_unlocked_stbuf_empty(c),
        pre.inv_valid_is_not_in_sbuf(c),
        pre.inv_inflight_walks_are_prefixes(c),
        c.valid_core(core),
        pre.cores[core].psc_contains_pcid(pcid, walk),
        next_step(pre, post, c, step, lbl),
        step == (Step::Writeback { core: wrcore }),
        core != wrcore,
    ensures
        is_iter_walk_prefix(post.core_mem(core), walk),
{
    broadcast use lemma_core_mem_pml4, lemma_step_core_mem, lemma_walk_next_is_walk_next_alt;
    reveal(rl3::walk_next_alt);
    assert(!walk.complete);
    pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
    post.pt_mem.lemma_write_seq(post.writer_sbuf());
    assert(bit!(0usize) == 1) by (bit_vector);
    assert(pre.core_mem(core) == pre.pt_mem);
    assert(post.core_mem(core) == post.pt_mem);
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> aligned(walk.path[i].0 as nat, 8)) by {
        broadcast use PDE::lemma_view_addr_aligned;
        crate::spec_t::cas_mmu::translation::lemma_bit_indices_less_512(walk.vaddr);
    };
    let wraddr = pre.cores[wrcore].stbuf_first().0;
    assert(pre.writer_sbuf().contains_fst(wraddr));
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> walk.path[i].0 != wraddr) by {
        assert forall|i| 0 <= i < walk.path.len() implies #[trigger] walk.path[i].0 != wraddr by {
            assert(pre.core_mem(core).read(walk.path[i].0) & 1 == 1);
            assert(!pre.writer_sbuf().contains_fst(walk.path[i].0));
        };
    };
    assert(forall|i| #![auto] 0 <= i < walk.path.len() ==>
        pre.pt_mem.read(walk.path[i].0) == post.pt_mem.read(walk.path[i].0));
    lemma_iter_walk_prefix_mem_agree(pre.pt_mem, post.pt_mem, walk);
}

proof fn lemma_iter_walk_prefix_mem_agree(mem1: PTMem, mem2: PTMem, walk: Walk)
    requires
        mem1.pml4 == mem2.pml4,
        is_iter_walk_prefix(mem1, walk),
        walk.path.len() <= 3,
        forall|i| #![auto] 0 <= i < walk.path.len() ==> mem1.read(walk.path[i].0) == mem2.read(walk.path[i].0),
    ensures
        is_iter_walk_prefix(mem2, walk),
{
    broadcast use lemma_walk_next_is_walk_next_alt;
    reveal(rl3::walk_next_alt);
    let walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
    let pre_walkp1 = walk_next_alt(mem1, walkp0);
    let post_walkp1 = walk_next_alt(mem2, walkp0);
    if walk.path.len() == 0 {
    } else if walk.path.len() == 1 {
        assert(post_walkp1.path[0] == pre_walkp1.path[0]);
    } else if walk.path.len() == 2 {
        assert(!pre_walkp1.complete);
        let pre_walkp2 = walk_next_alt(mem1, pre_walkp1);
        let post_walkp2 = walk_next_alt(mem2, post_walkp1);
        assert(post_walkp2.path[0] == pre_walkp2.path[0]);
        assert(post_walkp2.path[1] == pre_walkp2.path[1]);
    } else if walk.path.len() == 3 {
        assert(!pre_walkp1.complete);
        let pre_walkp2 = walk_next_alt(mem1, pre_walkp1);
        let post_walkp2 = walk_next_alt(mem2, post_walkp1);
        assert(!pre_walkp2.complete);
        let pre_walkp3 = walk_next_alt(mem1, pre_walkp2);
        let post_walkp3 = walk_next_alt(mem2, post_walkp2);
        assert(post_walkp3.path[0] == pre_walkp3.path[0]);
        assert(post_walkp3.path[1] == pre_walkp3.path[1]);
        assert(post_walkp3.path[2] == pre_walkp3.path[2]);
    } else {
        assert(false);
    }
}

broadcast proof fn lemma_step_core_mem(pre: State, post: State, c: Constants, step: Step, lbl: Lbl, core: Core)
    requires
        pre.hist.happy,
        post.hist.happy,
        #[trigger] next_step(pre, post, c, step, lbl),
        step !is Write,
        step !is Writeback,
    ensures
        #[trigger] post.core_mem(core) == pre.core_mem(core)
{}

proof fn next_step_preserves_wf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        post.hist.happy,
        next_step(pre, post, c, step, lbl),
    ensures post.wf(c)
{
    reveal(State::wf_ptmem_range);
    // assert(post.pt_mem.mem.dom() =~= pre.pt_mem.mem.dom());
    assert forall|core| #[trigger] c.valid_core(core) implies post.cores[core].wf() by {
        assert(post.cores[core].psc.dom() =~= pre.cores[core].psc.dom());
        assert(post.cores[core].tlb.dom() =~= pre.cores[core].tlb.dom());
    };
}


proof fn lemma_mem_view_after_step_write(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.hist.happy,
        post.hist.happy,
        pre.wf(c),
        pre.inv_unlocked_stbuf_empty(c),
        pre.inv_cas_progress(c),
        step_Write(pre, post, c, lbl),
    ensures
        post.writer_mem().pml4 == pre.pt_mem.pml4,
        post.writer_mem().mem  == pre.writer_mem().mem.insert(lbl->Write_1, lbl->Write_2),
{
    reveal_with_fuel(vstd::seq::Seq::fold_left, 5);
}

proof fn lemma_step_Writeback_preserves_writer_mem(pre: State, post: State, c: Constants, core: Core, lbl: Lbl)
    requires
        pre.inv_unlocked_stbuf_empty(c),
        step_Writeback(pre, post, c, core, lbl),
    ensures post.writer_mem() == pre.writer_mem()
{
    pt_mem::PTMem::lemma_write_seq_first(pre.pt_mem, pre.cores[core].stbuf);
}

broadcast proof fn lemma_bits_align_to_usize(vaddr: usize)
    ensures
        #![trigger align_to_usize(vaddr, L1_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L2_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L3_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, 8)]
        l0_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE)) == l1_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l2_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l2_bits!(vaddr),
        l3_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l3_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, 8)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, 8)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, 8)) == l2_bits!(vaddr),
        l3_bits!(align_to_usize(vaddr, 8)) == l3_bits!(vaddr),
{
    let l1_es = L1_ENTRY_SIZE;
    let l2_es = L2_ENTRY_SIZE;
    let l3_es = L3_ENTRY_SIZE;
    assert(l0_bits!(sub(vaddr, vaddr % l1_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l1_es == 512 * 512 * 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l1_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l1_es == 512 * 512 * 4096;
    assert(l0_bits!(sub(vaddr, vaddr % l2_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l2_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l2_bits!(sub(vaddr, vaddr % l2_es)) == l2_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l0_bits!(sub(vaddr, vaddr % l3_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l3_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l2_bits!(sub(vaddr, vaddr % l3_es)) == l2_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l3_bits!(sub(vaddr, vaddr % l3_es)) == l3_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l0_bits!(sub(vaddr, vaddr % 8)) == l0_bits!(vaddr)) by (bit_vector);
    assert(l1_bits!(sub(vaddr, vaddr % 8)) == l1_bits!(vaddr)) by (bit_vector);
    assert(l2_bits!(sub(vaddr, vaddr % 8)) == l2_bits!(vaddr)) by (bit_vector);
    assert(l3_bits!(sub(vaddr, vaddr % 8)) == l3_bits!(vaddr)) by (bit_vector);
}

// This thing has to be opaque because the iterated if makes Z3 explode, especially but not only
// with how we use this function in `iter_walk`.
//
// Alternative version of walk_next, which is easier to reason about because it doesn't have the
// extra XOR'd argument.
#[verifier(opaque)]
pub open spec fn walk_next_alt(mem: PTMem, walk: Walk) -> Walk {
    let Walk { vaddr, path, .. } = walk;
    let addr = if path.len() == 0 {
        add(mem.pml4, mul(l0_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
    } else { arbitrary() };

    let entry = PDE { entry: mem.read(addr), layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory),
    };
    walk
}

broadcast proof fn lemma_core_mem_pml4(state: State, c: Constants, core: Core)
    requires
        #[trigger] c.valid_core(core),
    ensures
        (#[trigger] state.core_mem(core)).pml4 == state.pt_mem.pml4,
{
    state.pt_mem.lemma_write_seq(state.cores[core].stbuf)
}

broadcast proof fn lemma_mask_dirty_access_after_xor(v: usize, r: usize)
    ensures
        #[trigger] (v ^ (r & MASK_DIRTY_ACCESS)) & MASK_NEG_DIRTY_ACCESS
                        == v & MASK_NEG_DIRTY_ACCESS
{
    assert((v ^ (r & ((bit!(5) | bit!(6))))) & (!(bit!(5) | bit!(6)))
            == v & (!(bit!(5) | bit!(6)))) by (bit_vector);
}

broadcast proof fn lemma_walk_next_is_walk_next_alt(state: State, core: Core, walk: Walk, r: usize, c: Constants)
    requires
        walk.path.len() <= 3,
        #[trigger] c.valid_core(core),
        state.inv_cr3_match(c)
    ensures #[trigger] walk_next(state, core, walk, r) == walk_next_alt(state.core_mem(core), walk)
{
    reveal(walk_next_alt);
    broadcast use
        lemma_core_mem_pml4,
        lemma_mask_dirty_access_after_xor,
        PDE::lemma_view_unchanged_dirty_access;
}

// MB: Ideally this would be some one liner `walk.path.is_prefix_of(..)`. But that doesn't seem to work well.
pub open spec fn is_iter_walk_prefix(mem: PTMem, walk: Walk) -> bool {
    let walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
    let walkp1 = walk_next_alt(mem, walkp0);
    let walkp2 = walk_next_alt(mem, walkp1);
    let walkp3 = walk_next_alt(mem, walkp2);
    let walkp4 = walk_next_alt(mem, walkp3);
    if walk.path.len() == 0 {
        walk == walkp0
    } else if walk.path.len() == 1 {
        walk == walkp1
    } else if walk.path.len() == 2 {
        &&& walk == walkp2
        &&& !walkp1.complete
    } else if walk.path.len() == 3 {
        &&& walk == walkp3
        &&& !walkp1.complete
        &&& !walkp2.complete
    } else if walk.path.len() == 4 {
        &&& walk == walkp4
        &&& !walkp1.complete
        &&& !walkp2.complete
        &&& !walkp3.complete
    } else {
        false
    }
}

pub open spec fn finish_iter_walk(mem: PTMem, walk: Walk) -> Walk {
    if walk.complete { walk } else {
        let walk = rl3::walk_next_alt(mem, walk);
        if walk.complete { walk } else {
            let walk = rl3::walk_next_alt(mem, walk);
            if walk.complete { walk } else {
                let walk = rl3::walk_next_alt(mem, walk);
                if walk.complete { walk } else {
                    rl3::walk_next_alt(mem, walk)
                }
            }
        }
    }
}

pub open spec fn iter_walk(mem: PTMem, vaddr: usize) -> Walk {
    let walk = rl3::walk_next_alt(mem, Walk { vaddr, path: seq![], complete: false });
    if walk.complete { walk } else {
        let walk = rl3::walk_next_alt(mem, walk);
        if walk.complete { walk } else {
            let walk = rl3::walk_next_alt(mem, walk);
            if walk.complete { walk } else {
                rl3::walk_next_alt(mem, walk)
            }
        }
    }
}

broadcast proof fn lemma_iter_walk_equals_pt_walk(mem: PTMem, vaddr: usize)
    ensures #[trigger] iter_walk(mem, vaddr) == mem.pt_walk(vaddr)
{
    reveal(walk_next_alt);
    let walk = Walk { vaddr, path: seq![], complete: false };
    let walk = rl3::walk_next_alt(mem, walk);
    let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
    let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
    let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
    let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
    let l0_addr = add(mem.pml4, l0_idx);
    let l0e = PDE { entry: mem.read(l0_addr), layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let walk = rl3::walk_next_alt(mem, walk);
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: mem.read(l1_addr), layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let walk = rl3::walk_next_alt(mem, walk);
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: mem.read(l2_addr), layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let walk = rl3::walk_next_alt(mem, walk);
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: mem.read(l3_addr), layer: Ghost(3) };
                            assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)]);
                        },
                        _ => {
                            assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)]);
                        },
                    }
                },
                _ => {
                    assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@)]);
                },
            }
        },
        _ => {
            assert(walk.path == seq![(l0_addr, l0e@)]);
        },
    }
}

proof fn lemma_iter_walk_result_vbase_equal(mem: PTMem, vaddr: usize)
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).path == iter_walk(mem, vaddr).path,
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).result().vaddr() == iter_walk(mem, vaddr).result().vaddr(),
{
    lemma_iter_walk_result_vbase_equal_aux1(mem, vaddr);
    lemma_iter_walk_result_vbase_equal_aux2(mem, vaddr);
}

proof fn lemma_iter_walk_result_vbase_equal_aux1(mem: PTMem, vaddr: usize)
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).path == iter_walk(mem, vaddr).path,
{
    reveal(rl3::walk_next_alt);
    broadcast use lemma_bits_align_to_usize;
}

pub proof fn lemma_pt_walk_result_vbase_equal(mem: PTMem, vaddr: usize)
    ensures
        mem.pt_walk(mem.pt_walk(vaddr).result().vaddr()).path     == mem.pt_walk(vaddr).path,
        mem.pt_walk(mem.pt_walk(vaddr).result().vaddr()).result() == mem.pt_walk(vaddr).result(),
        mem.pt_walk(vaddr).result().vaddr() <= vaddr,
{
    broadcast use lemma_iter_walk_equals_pt_walk;
    lemma_iter_walk_result_vbase_equal(mem, mem.pt_walk(vaddr).result().vaddr());
    lemma_iter_walk_result_vbase_equal(mem, vaddr);
}

// unstable
#[verifier(spinoff_prover)]
proof fn lemma_iter_walk_result_vbase_equal_aux2(mem: PTMem, vaddr: usize)
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).result().vaddr() == iter_walk(mem, vaddr).result().vaddr(),
{
    reveal(rl3::walk_next_alt);
    broadcast use lemma_bits_align_to_usize;
}

broadcast proof fn lemma_valid_implies_equal_reads(state: State, c: Constants, core: Core, addr: usize)
    requires
        state.inv_unlocked_stbuf_empty(c),
        state.inv_valid_is_not_in_sbuf(c),
        #[trigger] c.valid_core(core),
        state.lock is Some,
        state.lock != Some(core),
        aligned(addr as nat, 8),
        state.core_mem(core).read(addr) & 1 == 1,
    ensures state.core_mem(core).read(addr) == #[trigger] state.writer_mem().read(addr)
{
    reveal(State::wf_ptmem_range);
    state.pt_mem.lemma_write_seq_idle(state.cores[state.lock->Some_0].stbuf, addr);
    assert(state.core_mem(core).read(addr) == state.pt_mem.read(addr));
    assert(state.writer_mem().read(addr) == state.pt_mem.read(addr));
}

proof fn lemma_valid_implies_equal_walks(state: State, c: Constants, core: Core, va: usize)
    requires
        state.wf(c),
        state.wf_ptmem_range(c),
        state.inv_unlocked_stbuf_empty(c),
        state.inv_valid_is_not_in_sbuf(c),
        c.valid_core(core),
        state.lock is Some,
        state.lock != Some(core),
    ensures ({
        let core_walk = state.core_mem(core).pt_walk(va);
        let writer_walk = state.writer_mem().pt_walk(va);
        core_walk.result() is Valid ==> core_walk == writer_walk
    })
{
    broadcast use lemma_core_mem_pml4;
    let core_walk = state.core_mem(core).pt_walk(va);
    let writer_walk = state.writer_mem().pt_walk(va);
    if core_walk.result() is Valid {
        state.pt_mem.lemma_write_seq(state.cores[state.lock->Some_0].stbuf);
        assert(bit!(0usize) == 1) by (bit_vector);
        axiom_max_phyaddr_width_facts();
        let mw = MAX_PHYADDR_WIDTH;
        assert(forall|v: usize| (#[trigger] (v & bitmask_inc!(12usize, sub(mw, 1)))) % 4096 == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        crate::spec_t::cas_mmu::translation::lemma_bit_indices_less_512(va);
        broadcast use lemma_valid_implies_equal_reads;
        assert(core_walk.path =~= writer_walk.path);
    }
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
    use crate::spec_t::cas_mmu::defs::{ MAX_VIRTADDR };

    impl rl3::CoreState {
        #[verifier(inline)]
        pub open spec fn interp(self) -> rl1::CoreState {
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
                cores: self.cores.map_entries(|k, v:rl3::CoreState| v.interp()),
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
                    broadcast use rl3::lemma_walk_next_is_walk_next_alt;
                    let walk = step->MemOpNoTr_walk;
                    let (core, memop_vaddr, memop) = if let Lbl::MemOp(core, vaddr, memop) = lbl {
                            (core, vaddr, memop)
                        } else { arbitrary() };
                    let core_mem = pre.core_mem(core);
                    let writer_mem = pre.writer_mem();

                    rl3::lemma_iter_walk_equals_pt_walk(core_mem, walk.vaddr);
                    rl3::lemma_iter_walk_equals_pt_walk(writer_mem, walk.vaddr);

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
                    // rl3_walk_next_is_rl1_walk_next(pre, core, walk, r);
                    let walk_na = crate::spec_t::cas_mmu::rl3::walk_next(pre, core, walk, r);
                    let w_vbase = walk_na.result()->Valid_vbase;
                    let w_pte = walk_na.result()->Valid_pte;
                    broadcast use rl3::lemma_walk_next_is_walk_next_alt;

                    rl3::lemma_iter_walk_equals_pt_walk(pre.core_mem(core), walk.vaddr);
                    rl3::lemma_pt_walk_result_vbase_equal(pre.core_mem(core), walk.vaddr);
                    assert(post.interp().cores == pre.interp().cores.insert(core,
                            pre.interp().cores[core].tlb_fill(w_vbase, w_pte)));
                    rl3::lemma_pt_walk_result_vbase_equal(pre.writer_mem(), walk.vaddr);

                    if pre.lock is Some && pre.lock != Some(core) {
                        rl3::lemma_valid_implies_equal_walks(pre, c, core, walk.vaddr);
                    }

                    assert(pre.writer_mem().pt_walk(w_vbase).result() matches WalkResult::Valid { vbase, pte } && vbase == w_vbase && pte == w_pte);
                    assert(w_vbase < MAX_VIRTADDR);


                    assert(rl1::step_TLBFill(pre.interp(), post.interp(), c, core, w_vbase, lbl));
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
                    broadcast use rl3::lemma_mask_dirty_access_after_xor;

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
}


} // verus!
