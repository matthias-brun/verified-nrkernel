#![verus::trusted]
// trusted:
// this is the process-level specification of the kernel's behaviour

use crate::definitions_t::{
    aligned, between, candidate_mapping_in_bounds,
    candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem, overlap,
    x86_arch_spec, MemRegion, PTE, RWOp, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
    MAX_PHYADDR, WORD_SIZE,
};
use crate::spec_t::mem;
use vstd::prelude::*;

use crate::spec_t::hlproof::{
    insert_non_map_preserves_unique, lemma_mem_domain_from_mapping_finite, map_end_preserves_inv,
    map_start_preserves_inv, unmap_start_preserves_inv,
};

verus! {

pub struct Constants {
    //so far const
    pub thread_no: nat,
    pub phys_mem_size: nat,
}

pub struct State {
    /// Word-indexed virtual memory
    pub mem: Map<nat, nat>,
    pub thread_state: Map<nat, ThreadState>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat, PTE>,
    pub sound: bool,
}

#[allow(inconsistent_fields)]
pub enum Step {
    ReadWrite { thread_id: nat, vaddr: nat, op: RWOp, pte: Option<(nat, PTE)> },
    MapStart { thread_id: nat, vaddr: nat, pte: PTE },
    MapEnd { thread_id: nat, result: Result<(), ()> },
    UnmapStart { thread_id: nat, vaddr: nat },
    UnmapEnd { thread_id: nat, result: Result<(), ()> },
    Stutter,
}

//To allow two-step transitions that preserve arguments
#[allow(inconsistent_fields)]
pub enum ThreadState {
    Map { vaddr: nat, pte: PTE },
    Unmap { vaddr: nat, pte: Option<PTE> },
    Idle,
}

pub open spec fn wf(c: Constants, s: State) -> bool {
    &&& forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
    &&& s.mem.dom().finite()
}

pub open spec fn init(c: Constants, s: State) -> bool {
    &&& s.mem === Map::empty()
    &&& s.mappings === Map::empty()
    &&& forall|id: nat| id < c.thread_no ==> (s.thread_state[id] === ThreadState::Idle)
    &&& wf(c, s)
    &&& s.sound
}

pub open spec fn mem_domain_from_mappings_contains(
    phys_mem_size: nat,
    word_idx: nat,
    mappings: Map<nat, PTE>,
) -> bool {
    let vaddr = word_idx * WORD_SIZE as nat;
    exists|base: nat, pte: PTE|
        {
            &&& #[trigger] mappings.contains_pair(base, pte)
            &&& mem_domain_from_entry_contains(phys_mem_size, vaddr, base, pte)
        }
}

pub open spec fn mem_domain_from_entry_contains(
    phys_mem_size: nat,
    vaddr: nat,
    base: nat,
    pte: PTE,
) -> bool {
    let paddr = (pte.frame.base + (vaddr - base)) as nat;
    let pmem_idx = mem::word_index_spec(paddr);
    &&& between(vaddr, base, base + pte.frame.size)
    &&& pmem_idx < phys_mem_size
}

pub open spec fn mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PTE>,
) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub open spec fn mem_domain_from_entry(phys_mem_size: nat, base: nat, pte: PTE) -> Set<
    nat,
> {
    Set::new(
        |word_idx: nat|
            mem_domain_from_entry_contains(phys_mem_size, (word_idx * WORD_SIZE as nat), base, pte),
    )
}

pub open spec fn valid_thread(c: Constants, thread_id: nat) -> bool {
    thread_id < c.thread_no
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper function to specify relation between 2 states
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn state_unchanged_besides_thread_state(
    s1: State,
    s2: State,
    thread_id: nat,
    thread_arguments: ThreadState,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings
    &&& s2.sound == s1.sound
}

pub open spec fn unsound_state(s1: State, s2: State) -> bool {
    !s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    inflightargs: Set<ThreadState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    &&& exists|b: ThreadState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                ThreadState::Map { vaddr, pte } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                ThreadState::Unmap { vaddr, pte } => {
                    let size = if pte.is_some() {
                        pte.unwrap().frame.size
                    } else {
                        0
                    };
                    overlap(
                        MemRegion { base: vaddr, size: size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                _ => { false },
            }
        }
}

pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    inflightargs: Set<ThreadState>,
    candidate: PTE,
) -> bool {
    &&& exists|b: ThreadState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                ThreadState::Map { vaddr, pte } => { overlap(candidate.frame, pte.frame) },
                ThreadState::Unmap { vaddr, pte } => {
                    &&& pte.is_some()
                    &&& overlap(candidate.frame, pte.unwrap().frame)
                },
                _ => { false },
            }
        }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// MMU atomic ReadWrite
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//since unmap deleted pte inflight pte == pagefault
pub open spec fn step_ReadWrite(
    c: Constants,
    s1: State,
    s2: State,
    thread_id: nat,
    vaddr: nat,
    op: RWOp,
    pte: Option<(nat, PTE)>,
) -> bool {
    let vmem_idx = mem::word_index_spec(vaddr);
    &&& s2.sound == s1.sound
    &&& aligned(vaddr, 8)
    &&& s2.mappings === s1.mappings
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& s2.thread_state === s1.thread_state
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(
                vaddr,
                base,
                base + pte.frame.size,
            )
            // .. and the result depends on the flags.
            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value)
                    } else {
                        &&& result is Undefined
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.index(vmem_idx)
                    } else {
                        &&& result is Undefined
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(
                vmem_idx,
            )
            // .. and the result is always a Undefined and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result is Undefined,
                RWOp::Load { is_exec, result } => result is Undefined,
            }
        },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_sound(
    mappings: Map<nat, PTE>,
    inflights: Set<ThreadState>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& !candidate_mapping_overlaps_inflight_vmem(inflights, vaddr, pte.frame.size)
    &&& !candidate_mapping_overlaps_existing_pmem(mappings, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(inflights, pte)
}

pub open spec fn step_Map_enabled(
    inflight: Set<ThreadState>,
    map: Map<nat, PTE>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
}

//think about weather or not map start is valid if it overlaps with existing vmem
pub open spec fn step_Map_start(
    c: Constants,
    s1: State,
    s2: State,
    thread_id: nat,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& step_Map_enabled(s1.thread_state.values(), s1.mappings, vaddr, pte)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Map_sound(s1.mappings, s1.thread_state.values(), vaddr, pte) {
        state_unchanged_besides_thread_state(
            s1,
            s2,
            thread_id,
            ThreadState::Map { vaddr, pte },
        )
    } else {
        unsound_state(s1, s2)
    }
}

pub open spec fn step_Map_end(
    c: Constants,
    s1: State,
    s2: State,
    thread_id: nat,
    result: Result<(), ()>,
) -> bool {
    &&& s2.sound == s1.sound
    &&& valid_thread(c, thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& match s1.thread_state[thread_id] {
        ThreadState::Map { vaddr, pte } => {
            //&&& !candidate_mapping_overlaps_existing_pmem(s1.mappings, pte)
            &&& if (candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte)) {
                &&& result is Err
                &&& s2.mappings === s1.mappings
                &&& s2.mem === s1.mem
            } else {
                &&& result is Ok
                &&& s2.mappings === s1.mappings.insert(vaddr, pte)
                &&& (forall|idx: nat|
                    #![auto]
                    s1.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
                &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
            }
        },
        _ => { false },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(
    inflights: Set<ThreadState>,
    vaddr: nat,
    pte_size: nat,
) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(inflights, vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

//shouldnt need to check for overlapping pmem bc:
// if its being mapped rn then itll cause Err anyways
// if its being unmapped rn then vmem is the way to go.
pub open spec fn step_Unmap_start(
    c: Constants,
    s1: State,
    s2: State,
    thread_id: nat,
    vaddr: nat,
) -> bool {
    let pte = if (s1.mappings.dom().contains(vaddr)) {
        Some(s1.mappings.index(vaddr))
    } else {
        Option::None
    };
    let pte_size = if (pte is Some) {
        pte.unwrap().frame.size
    } else {
        0
    };
    &&& step_Unmap_enabled(vaddr)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Unmap_sound(s1.thread_state.values(), vaddr, pte_size) {
        &&& s2.thread_state === s1.thread_state.insert(
            thread_id,
            ThreadState::Unmap { vaddr, pte },
        )
        &&& if (pte is None) {
            &&& s2.mappings === s1.mappings
            &&& s2.mem === s1.mem
        } else {
            &&& s2.mappings === s1.mappings.remove(vaddr)
            &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
            &&& (forall|idx: nat|
                #![auto]
                s2.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
        }
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s1.mappings.remove(vaddr))
        &&& s2.sound == s1.sound
    } else {
        unsound_state(s1, s2)
    }
}

pub open spec fn step_Unmap_end(
    c: Constants,
    s1: State,
    s2: State,
    thread_id: nat,
    result: Result<(), ()>,
) -> bool {
    &&& valid_thread(c, thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& s2.sound == s1.sound
    &&& s2.mappings === s1.mappings
    &&& s2.mem === s1.mem
    &&& match s1.thread_state[thread_id] {
        ThreadState::Unmap { vaddr, pte } => {
            &&& if pte is Some {
                result is Ok
            } else {
                result is Err
            }
        },
        _ => { false },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Stutter
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Stutter(
    c: Constants,
    s1: State,
    s2: State,
) -> bool {
    s1 === s2
}

//if s1.sound then match else !s2.sound
pub open spec fn next_step(
    c: Constants,
    s1: State,
    s2: State,
    step: Step,
) -> bool {
    if (s1.sound) {
        match step {
            Step::ReadWrite { thread_id, vaddr, op, pte } => step_ReadWrite(
                c,
                s1,
                s2,
                thread_id,
                vaddr,
                op,
                pte,
            ),
            Step::MapStart { thread_id, vaddr, pte } => step_Map_start(
                c,
                s1,
                s2,
                thread_id,
                vaddr,
                pte,
            ),
            Step::MapEnd { thread_id, result } => step_Map_end(
                c,
                s1,
                s2,
                thread_id,
                result,
            ),
            Step::UnmapStart { thread_id, vaddr } => step_Unmap_start(
                c,
                s1,
                s2,
                thread_id,
                vaddr,
            ),
            Step::UnmapEnd { thread_id, result } => step_Unmap_end(
                c,
                s1,
                s2,
                thread_id,
                result,
            ),
            Step::Stutter => step_Stutter(c, s1, s2),
        }
    } else {
        !s2.sound
    }
}

pub open spec fn next(c: Constants, s1: State, s2: State) -> bool {
    exists|step: Step| next_step(c, s1, s2, step)
}

pub open spec fn pmem_no_overlap(mappings: Map<nat, PTE>) -> bool {
    forall|bs1: nat, bs2: nat|
        mappings.dom().contains(bs1) && mappings.dom().contains(bs2) && overlap(
            mappings.index(bs1).frame,
            mappings.index(bs2).frame,
        ) ==> equal(bs1, bs2)
}

pub open spec fn inflight_map_no_overlap_pmem(
    inflightargs: Set<ThreadState>,
    mappings: Map<nat, PTE>,
) -> bool {
    forall|b: ThreadState|
        #![auto]
        {
            inflightargs.contains(b) ==> match b {
                ThreadState::Map { vaddr, pte } => {
                    !candidate_mapping_overlaps_existing_pmem(mappings, pte)
                },
                _ => { true },
            }
        }
}

pub open spec fn inflight_map_no_overlap_inflight_pmem(
    inflightargs: Set<ThreadState>,
) -> bool {
    forall|b: ThreadState|
        #![auto]
        {
            inflightargs.contains(b) ==> match b {
                ThreadState::Map { vaddr, pte } => {
                    !candidate_mapping_overlaps_inflight_pmem(inflightargs.remove(b), pte)
                },
                _ => { true },
            }
        }
}

pub open spec fn if_map_then_unique(thread_state: Map<nat, ThreadState>, id: nat) -> bool
    recommends
        thread_state.dom().contains(id),
{
    if let ThreadState::Map { vaddr, pte } = thread_state.index(id) {
        !thread_state.remove(id).values().contains(thread_state.index(id))
    } else {
        true
    }
}

pub open spec fn inflight_maps_unique(thread_state: Map<nat, ThreadState>) -> bool {
    forall|a: nat| #[trigger] thread_state.dom().contains(a) ==> if_map_then_unique(thread_state, a)
}

pub open spec fn inv(c: Constants, s: State) -> bool {
    &&& wf(c, s)
    &&& pmem_no_overlap(
        s.mappings,
    )
    //invariants needed to proof the former
    &&& inflight_map_no_overlap_pmem(s.thread_state.values(), s.mappings)
    &&& inflight_map_no_overlap_inflight_pmem(s.thread_state.values())
    &&& inflight_maps_unique(s.thread_state)
}

pub proof fn init_implies_inv(c: Constants, s: State)
    requires
        init(c, s),
    ensures
        inv(c, s),
{
}

pub proof fn next_step_preserves_inv(
    c: Constants,
    s1: State,
    s2: State,
)
    requires
        next(c, s1, s2),
        s1.sound ==> inv(c, s1),
    ensures
        s2.sound ==> inv(c, s2),
{
    if (s1.sound) {
        let p = choose|step: Step| next_step(c, s1, s2, step);
        match p {
            Step::UnmapStart { thread_id, vaddr } => {
                unmap_start_preserves_inv(c, s1, s2, thread_id, vaddr);
            },
            Step::UnmapEnd { thread_id, result } => {
                assert(s2.thread_state.values().subset_of(
                    s1.thread_state.values().insert(ThreadState::Idle),
                ));
                lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
                insert_non_map_preserves_unique(
                    s1.thread_state,
                    thread_id,
                    ThreadState::Idle,
                );
            },
            Step::MapStart { thread_id, vaddr, pte } => {
                map_start_preserves_inv(c, s1, s2, thread_id, vaddr, pte);
            },
            Step::MapEnd { thread_id, result } => {
                map_end_preserves_inv(c, s1, s2, thread_id, result);
            },
            _ => {},
        }
    } else {
        assert(!s2.sound);
    }
}

} // verus!
