#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_by_contradiction;

// use crate::spec_t::hlspec::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    x86_arch_spec_upper_bound,
    candidate_mapping_in_bounds,
    candidate_mapping_in_bounds_pmem,
    candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap,
    MAX_BASE, MemRegion, PTE, Core,
    L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
    aligned,
};
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::mmu::{ self, rl1 };
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_invariant::{
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl,
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl, next_step_preserves_inv,
    lemma_map_insert_values_equality, lemma_map_insert_value,
    lemma_init_implies_empty_map,
};
use crate::spec_t::{hlspec, os};
use crate::theorem::RLbl;
use crate::spec_t::mmu::defs::MemOp;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{between, update_range};
use crate::spec_t::mmu::pt_mem::PTMem;
use crate::spec_t::os::CoreState;

verus! {


///////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////

proof fn lemma_inflight_unmap_vaddr_equals_hl_unmap(c: os::Constants, s: os::State)
    requires s.inv_basic(c),
    ensures
        forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr)
            <==> exists|thread_state| {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().contains_key(v_addr)
                &&& (thread_state matches hlspec::ThreadState::Unmap { vaddr, .. } && vaddr === v_addr)
            },
{
    // proof ==> direction
    assert forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr) implies exists|thread_state| {
        &&& s.interp_thread_state(c).values().contains(thread_state)
        &&& s.interp_pt_mem().contains_key(v_addr)
        &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
        &&& vaddr === v_addr
    } by {
        let core = choose|core| {
            &&& s.core_states.contains_key(core)
            &&& ({
                &&& s.core_states[core] matches os::CoreState::UnmapWaiting { vaddr, .. }
                &&& vaddr == v_addr
            } || {
                &&& s.core_states[core] matches os::CoreState::UnmapExecuting { vaddr, .. }
                &&& vaddr == v_addr
            } || {
                &&& s.core_states[core] matches os::CoreState::UnmapOpDone { vaddr, .. }
                &&& vaddr == v_addr
            } || {
                &&& s.core_states[core] matches os::CoreState::UnmapShootdownWaiting {
                    vaddr,
                    ..
                }
                &&& vaddr == v_addr
            })
        };
        match s.core_states[core] {
            os::CoreState::UnmapWaiting { ult_id, vaddr }
            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                assert(s.interp_thread_state(c).contains_key(ult_id));
                let thread_state = s.interp_thread_state(c)[ult_id];
                assert(s.interp_thread_state(c).values().contains(thread_state));
            },
            _ => {
                assert(false);
            },
        }
    };
    // proof of <== direction
    assert forall|v_addr| exists|thread_state| {
        &&& s.interp_thread_state(c).values().contains(thread_state)
        &&& s.interp_pt_mem().contains_key(v_addr)
        &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
        &&& vaddr === v_addr
    } implies s.inflight_unmap_vaddr().contains(v_addr) by {
        let thread_state = choose|thread_state| {
            &&& s.interp_thread_state(c).values().contains(thread_state)
            &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, pte }
            &&& vaddr == v_addr
        };
        let ult_id = choose|id|
            #[trigger] s.interp_thread_state(c).contains_key(id) && s.interp_thread_state(c)[id]
                === thread_state;
        assert(s.core_states.contains_key(c.ult2core[ult_id]));
    };

}


proof fn lemma_inflight_mapunmap_vaddr_implies_hl_unmap_or_map(c: os::Constants, s: os::State)
    requires s.inv_basic(c),
    ensures
        forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr)
            ==> exists|thread_state| {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().contains_key(v_addr)
                &&& ((thread_state matches hlspec::ThreadState::Unmap { vaddr, .. } && vaddr === v_addr)
                    || (thread_state matches hlspec::ThreadState::Map { vaddr, .. } && vaddr === v_addr))
            },
{
    if (!(s.inflight_mapunmap_vaddr() =~= Set::empty()) && s.inflight_unmap_vaddr() =~= Set::empty()) {
        let v_address = s.inflight_mapunmap_vaddr().choose();
        assert(s.interp_pt_mem().contains_key(v_address));
        let map_core = choose|core| s.core_states.contains_key(core) && match s.core_states[core] {
            os::CoreState::UnmapWaiting { ult_id, vaddr }
            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
            | os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                vaddr === v_address
            },
            _ => false,
        };
        if (s.core_states[map_core] is MapDone) {
        let ult_id = s.core_states[map_core]->MapDone_ult_id;
        assert(s.interp_thread_state(c).contains_key(ult_id));
        let thread_state = s.interp_thread_state(c)[ult_id];
        assert(thread_state is Map);
        assert(s.interp_thread_state(c).values().contains(thread_state));
        } else {
            assert(s.inflight_unmap_vaddr().contains(v_address));
            assert(false);
        }
    } else {
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s);
    }
}

proof fn lemma_effective_mappings_unaffected_if_thread_state_constant(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
)
    requires
        s1.inv_basic(c),
        s1.inv_protect_vaddr_same_core(c),
        s2.inv_basic(c),
        s1.interp_thread_state(c) === s2.interp_thread_state(c),
        s1.interp_pt_mem() === s2.interp_pt_mem(),
        os::next(c, s1, s2, RLbl::Tau),
    ensures
        s1.effective_mappings() === s2.effective_mappings(),
{
    lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
    lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
    let step = choose|step| os::next_step(c, s1, s2, step, RLbl::Tau);

    assert(s2.inflight_mapunmap_vaddr() =~= s1.inflight_mapunmap_vaddr()) by {
        if s1.inflight_unmap_vaddr() =~= s1.inflight_mapunmap_vaddr() {
            assert_by_contradiction!(s2.inflight_unmap_vaddr() =~= s2.inflight_mapunmap_vaddr(), {
                let map_vaddr = choose|v| s2.inflight_mapunmap_vaddr().contains(v) && !s2.inflight_unmap_vaddr().contains(v);
                let map_core = choose|core| s2.core_states.contains_key(core) && s2.core_states[core] matches os::CoreState::MapDone { ult_id, vaddr: map_vaddr, result: Ok(()), .. };
                assert(!s2.effective_mappings().contains_key(map_vaddr));
                assert(s2.interp_pt_mem().contains_key(map_vaddr));
            });
            assert(s2.inflight_mapunmap_vaddr() =~= s1.inflight_mapunmap_vaddr());
        } else {
            let map_vaddr = choose|v| s1.inflight_mapunmap_vaddr().contains(v) && !s1.inflight_unmap_vaddr().contains(v);
            let map_core = choose |core| s1.core_states.contains_key(core) && s1.core_states[core] matches os::CoreState::MapDone { ult_id, vaddr: map_vaddr, result: Ok(()), .. };
            assert(s2.inflight_mapunmap_vaddr().contains(map_vaddr) && !s2.inflight_unmap_vaddr().contains(map_vaddr));
            assert(s2.inflight_mapunmap_vaddr() =~= s1.inflight_mapunmap_vaddr());
        }
    };

    assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
        assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
            <==> s2.is_inflight_protect_vaddr_core(va, core));
    };

    assert(s1.effective_mappings() =~= s2.effective_mappings());
}

///////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_map_soundness_equality(c: os::Constants, s: os::State, vaddr: nat, pte: PTE)
    requires
        s.inv_basic(c),
        s.inv_protect_frame_unchanged(c),
        pte.frame.size > 0,
    ensures
        hlspec::step_Map_sound(s.interp(c).mappings, s.interp(c).thread_state.values(), vaddr, pte)
            <==> os::step_Map_sound(s.interp_pt_mem(), s.core_states.values(), vaddr, pte),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte.frame.size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte.frame.size);
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(c, s, pte);
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(c, s, pte);
    assert(candidate_mapping_overlaps_existing_pmem(s.interp(c).mappings, pte)
        ==> candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte));

    assert(candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte) ==> (
            candidate_mapping_overlaps_existing_pmem(s.interp(c).mappings, pte)
            || hlspec::candidate_mapping_overlaps_inflight_pmem(s.interp(c).thread_state.values(), pte))
    ) by {
        if  candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte) {
            // candidate pte overlaps with base's pte
            let base = choose|b: nat| #![auto] {
                        &&& s.interp_pt_mem().contains_key(b)
                        &&& overlap(pte.frame, s.interp_pt_mem()[b].frame)
                    };
            let overlap_pte = s.interp_pt_mem()[base];
            if !os::candidate_mapping_overlaps_inflight_pmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                pte,
            ) {
                if !s.inflight_mapunmap_vaddr().contains(base) {
                    assert(s.effective_mappings().contains_key(base));
                } else {
                    let critical_core = choose|core|
                        s.core_states.contains_key(core) && match s.core_states[core] {
                            os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. }
                            | os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === base
                            },
                            _ => false,
                        };
                    assert(s.core_states.values().contains(s.core_states[critical_core]));
                    if s.core_states[critical_core] is MapDone {
                        let critical_ult_id = s.core_states[critical_core]->MapDone_ult_id;
                        let b = hlspec::ThreadState::Map { vaddr: base, pte: overlap_pte };
                        assert(s.interp(c).thread_state.values().contains(b) && match b {
                            hlspec::ThreadState::Map { vaddr: base, pte: overlap_pte } => overlap(pte.frame, overlap_pte.frame),
                            _ => false,
                        });
                        assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
                            s.interp(c).thread_state.values(),
                            pte,
                        ));
                    } else {
                        assert(os::candidate_mapping_overlaps_inflight_pmem(
                            s.interp_pt_mem(),
                            s.core_states.values(),
                            pte,
                        ));
                    }
                }
            }
        }
    }
}

proof fn lemma_protect_soundness_equality(c: os::Constants, s: os::State, vaddr: nat, pte_size: nat)
    requires
        s.inv_basic(c),
    ensures
        hlspec::step_Protect_sound(s.interp(c), vaddr, pte_size)
            <==> os::step_Protect_sound(s, vaddr, pte_size),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte_size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte_size);
}

proof fn lemma_unmap_soundness_equality(c: os::Constants, s: os::State, vaddr: nat, pte_size: nat)
    requires
        s.inv_basic(c),
    ensures
        hlspec::step_Unmap_sound(s.interp(c), vaddr, pte_size)
            <==> os::step_Unmap_sound(s, vaddr, pte_size),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte_size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte_size);
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Refinement proof
///////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn os_init_refines_hl_init(c: os::Constants, s: os::State)
    requires
        os::init(c, s),
    ensures
        hlspec::init(c.interp(), s.interp(c)),
{
    let abs_c = c.interp();
    let abs_s = s.interp(c);
    //lemma_effective_mappings_equal_interp_pt_mem(s);
    assert forall|id: nat| id < abs_c.thread_no implies abs_s.thread_state[id] is Idle by {
        assert(c.ult2core.contains_key(id));
        let core = c.ult2core[id];
        assert(c.valid_core(core));
        assert(s.core_states[core] === os::CoreState::Idle);  //nn
    };
    //assert(abs_s.mem === Map::empty());
    assert(abs_s.mappings =~= Map::empty()) by {
        lemma_init_implies_empty_map(s, c);
    };
}

pub proof fn os_next_refines_hl_next(c: os::Constants, s1: os::State, s2: os::State, lbl: RLbl)
    requires
        os::next(c, s1, s2, lbl),
        s1.inv(c),
    ensures
        hlspec::next(c.interp(), s1.interp(c), s2.interp(c), lbl.interp()),
{
    let step = choose|step: os::Step| os::next_step(c, s1, s2, step, lbl);
    next_step_refines_hl_next_step(c, s1, s2, step, lbl);
}

#[verifier(spinoff_prover)]
proof fn next_step_refines_hl_next_step(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        os::next_step(c, s1, s2, step, lbl),
        s1.inv(c),
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl.interp()),
{
    if s1.sound {
        match step { // Broadcasting these is very slow
            os::Step::MemOp { .. } | os::Step::ReadPTMem { .. } | os::Step::Invlpg { .. } | os::Step::Barrier { .. }
            | os::Step::UnmapOpChange { .. } | os::Step::MMU { .. } | os::Step::UnmapOpStutter { .. }
            | os::Step::MapOpStutter { .. } | os::Step::MapOpChange { .. }
            | os::Step::ProtectOpChange { .. } => {
                to_rl1::next_refines(s1.mmu, s2.mmu, c.common, step.mmu_lbl(s1, lbl));
                to_rl1::next_preserves_inv(s1.mmu, s2.mmu, c.common, step.mmu_lbl(s1, lbl));
            },
            _ => {},
        }
        next_step_preserves_inv(c, s1, s2, step, lbl);
        match step {
            os::Step::MemOp { core, .. } => {
                step_MemOp_refines(c, s1, s2, step, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            // Map steps
            os::Step::MapStart { core } => {
                step_MapStart_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::MapOpStart { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::MapOpChange { core, paddr, value } => {
                step_MapOpChange_refines(c, s1, s2, core, paddr, value, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::MapNoOp { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved_for_overlap_map(c, s1, s2, core);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::MapEnd { core } => {
                step_MapEnd_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            // Unmap steps
            os::Step::UnmapStart { core } => {
                step_UnmapStart_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::UnmapOpStart { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::UnmapOpChange { core, paddr, value } => {
                step_UnmapOpChange_refines(c, s1, s2, core, paddr, value, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            }
            os::Step::UnmapOpFail { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::UnmapInitiateShootdown { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::UnmapEnd { core } => {
                step_UnmapEnd_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            // Protect steps
            os::Step::ProtectStart { core } => {
                step_ProtectStart_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::ProtectOpStart { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::ProtectOpChange { core, paddr, value } => {
                admit();
                // step_ProtectOpChange_refines(c, s1, s2, core, paddr, value, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            }
            os::Step::ProtectOpFail { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::ProtectInitiateShootdown { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            os::Step::ProtectEnd { core } => {
                step_ProtectEnd_refines(c, s1, s2, core, lbl);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
            },
            _ => {
                assert(s1.effective_mappings() =~= s2.effective_mappings()) by {
                    assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
                        assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                            <==> s2.is_inflight_protect_vaddr_core(va, core));
                    };
                };
                extra_mappings_preserved(c, s1, s2);
                assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl.interp()));
            }
        }
    }
}

#[verifier(spinoff_prover)]
proof fn step_MemOp_refines(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::next_step(c, s1, s2, step, lbl),
        step is MemOp,
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl)
{
    let core = step->MemOp_core;
    let vaddr = lbl->MemOp_vaddr;
    let op = lbl->MemOp_op;
    let mlbl = mmu::Lbl::MemOp(core, vaddr as usize, op);

    to_rl1::next_refines(s1.mmu, s2.mmu, c.common, mlbl);
    let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mlbl);
    assert(rl1::next_step(s1.mmu@, s2.mmu@, c.common, mmu_step, mlbl));

    assert(s1.effective_mappings() =~= s2.effective_mappings()) by {
        assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
            assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                <==> s2.is_inflight_protect_vaddr_core(va, core));
        };
    };
    extra_mappings_preserved(c, s1, s2);
    assert(c.valid_core(core));

    match mmu_step {
        rl1::Step::MemOpNoTr { .. } => {
            assert(rl1::step_MemOpNoTr(s1.mmu@, s2.mmu@, c.common, mlbl));
            let t1 = s1.interp(c);
            let t2 = s2.interp(c);
            let d = c.interp();
            assert(lbl is MemOp);
            let thread_id = lbl->MemOp_thread_id;
            assert(!hlspec::is_in_mapped_region(c.common.phys_mem_size, t1.mappings, vaddr)) by {
                reveal(PTMem::view);
                assert forall|base: nat, pte: PTE|
                  #[trigger] t1.mappings.contains_pair(base, pte)
                   && between(vaddr, base, base + pte.frame.size)
                   && pte.frame.base + (vaddr - base) < c.common.phys_mem_size
                   implies false
                by {
                    assert(s1.interp_pt_mem().contains_key(base));
                    reveal(PTMem::view);
                    assert(s1.mmu@.pt_mem.pt_walk(base as usize).result() is Valid);
                    assert(s1.mmu@.pt_mem.pt_walk(vaddr as usize).result() is Invalid);

                    // assert(s1.mmu@.pt_mem.is_base_pt_walk(base as usize));
                    // assert(s1.effective_mappings()[base] == pte);
                    // assert(s1.mmu@.pt_mem.pt_walk(base as usize).result()->pte.frame == pte.frame);
                    s1.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(base as usize, vaddr as usize);
                    assert(false);
                }
            }
            assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), None, lbl));
        },
        rl1::Step::MemOpNoTrNA { vbase } => {
            let t1 = s1.interp(c);
            let t2 = s2.interp(c);
            let d = c.interp();
            let thread_id = lbl->MemOp_thread_id;
            let op = lbl->MemOp_op;

            let pte = t1.vaddr_mapping_is_being_modified_choose(d, vaddr);

            let core = choose|core| s1.is_pending_for_core(c, vbase, core);
            assert(s1.is_pending_for_core(c, vbase, core));

            let thread1 = s1.core_states[core]->MapDone_ult_id;
            assert(d.valid_thread(thread1));
            let thread = t1.vaddr_mapping_is_being_modified_choose_thread(d, vaddr);
            assert(thread == thread1) by {
                let core1 = c.ult2core[thread1];
                let core2 = c.ult2core[thread];
                assert(s1.inv_inflight_map_no_overlap_inflight_vmem(c));
                let mr1 = MemRegion {
                        base: s1.core_states[core1].vaddr(),
                        size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                    };
                let mr2 = MemRegion {
                        base: s1.core_states[core2].vaddr(),
                        size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                    };
                assert(overlap(mr1, mr2));
                assert(core1 == core2);
            }
            assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        rl1::Step::MemOpTLB { tlb_va } => {
            assert(s1.mmu@.tlbs[core].contains_key(tlb_va));
            assert(s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()).contains(tlb_va as nat));
            unmap_vaddr_set_le_extra_mappings_dom(c, s1);
            assert(s1.applied_mappings().contains_key(tlb_va as nat));
            assert(s1.applied_mappings()[tlb_va as nat] == s1.mmu@.tlbs[core][tlb_va]) by {
                reveal(os::State::extra_mappings);
                if s1.interp_pt_mem().contains_key(tlb_va as nat) {
                    assert(s1.interp_pt_mem()[tlb_va as nat] == s1.mmu@.tlbs[core][tlb_va]);
                    assert(s1.applied_mappings()[tlb_va as nat] == s1.mmu@.tlbs[core][tlb_va]);
                } else {
                    assert(s1.unmap_vaddr_set().contains(tlb_va as nat));
                    let core1 = choose|core: Core| s1.is_unmap_vaddr_core(core, tlb_va as nat);
                    assert(c.valid_core(core1));
                    assert(s1.is_unmap_vaddr_core(core1, tlb_va as nat));
                    assert(s1.core_states[core1].PTE() == s1.mmu@.tlbs[core][tlb_va]);
                    vaddr_distinct(c, s1);
                    assert(s1.core_states[core1].PTE() == s1.extra_mapping_for_vaddr(tlb_va as nat));
                    assert(s1.extra_mapping_for_vaddr(tlb_va as nat) == s1.extra_mappings()[tlb_va as nat]);
                    assert(s1.applied_mappings()[tlb_va as nat] == s1.mmu@.tlbs[core][tlb_va]);
                }
            }


            let d = c.interp();
            let base = tlb_va as nat;
            let pte = s1.applied_mappings()[tlb_va as nat];
            let hl_pte = Some((tlb_va as nat, pte));

            assert(pte == s1.mmu@.tlbs[core][tlb_va]);
            //assert(s1.mmu@.pt_mem.is_base_pt_walk(tlb_va));

            let paddr = pte.frame.base + (vaddr - base);
            no_overlaps_applied_mappings(c, s1);
            no_overlaps_pmem_applied_mappings(c, s1);
            bounds_applied_mappings(c, s1);

            assert(vaddr as int + op.op_size() as int <= base + pte.frame.size) by {
                let pte_frame_size = pte.frame.size;
                let op_size = op.op_size();
                assert(vaddr + op_size <= base + pte_frame_size) by (nonlinear_arith)
                    requires vaddr < base + pte_frame_size,
                      pte_frame_size == 4096 || pte_frame_size == 512 * 4096
                          || pte_frame_size == 512 * (512 * 4096),
                      op_size == 1 || op_size == 2 || op_size == 4 || op_size == 8,
                      vaddr % op_size == 0,
                      base % pte_frame_size == 0;
            }
            assert(candidate_mapping_in_bounds(base, pte));
            x86_arch_spec_upper_bound();
            assert(base + pte.frame.size <= s1.interp_vmem(c).len());
            assert(pte.frame.base + pte.frame.size <= s1.mmu@.phys_mem.len());

            match op {
                MemOp::Store { new_value, result } => {
                    if paddr < d.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        assert(result is Ok);
                        interp_vmem_update_range(c, s1, base, pte, vaddr as int, op.op_size() as int, new_value);
                        assert(s2.interp(c).mem === update_range(s1.interp(c).mem, vaddr as int, new_value));
                    } else {
                        assert(result is Pagefault);
                        assert(s2.interp(c).mem === s1.interp(c).mem);
                    }
                },
                MemOp::Load { is_exec, result, .. } => {
                    assert(s2.interp(c).mem === s1.interp(c).mem);
                    if paddr < d.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        assert(result is Value);
                        interp_vmem_subrange(c, s1, base, pte, vaddr as int, op.op_size() as int);
                        assert(result->0 == s1.interp(c).mem.subrange(vaddr as int, vaddr + op.op_size() as int));
                    } else {
                        assert(result is Pagefault);
                    }
                }
            }

            let tlb_pte = s1.mmu@.tlbs[core][tlb_va];
            if s1.effective_mappings().contains_key(tlb_va as nat)
                && s1.effective_mappings()[tlb_va as nat] == tlb_pte
            {
                assert(s1.interp(c).mappings.contains_pair(tlb_va as nat, tlb_pte));
                assert(s1.interp(c).mappings.contains_pair(base, tlb_pte));
                assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), hl_pte, lbl));
            } else {
                if s1.effective_mappings().contains_key(tlb_va as nat) {
                    assert(s1.inflight_protect_params().contains_key(tlb_va as nat));
                    assert(s1.is_inflight_protect_vaddr(tlb_va as nat));
                    let prot_core = s1.choose_inflight_protect_vaddr_core(tlb_va as nat);
                    assert(s1.is_inflight_protect_vaddr_core(tlb_va as nat, prot_core));
                    let pte = s1.inflight_protect_core_get_pte(prot_core);
                    // XXX: need tlb invariant for protects
                    assume(tlb_pte == pte);
                    assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
                } else {
                    assert(s1.extra_mappings().contains_key(tlb_va as nat)
                        || s1.inflight_mapunmap_vaddr().contains(tlb_va as nat));
                    assert(c.valid_core(core));
                    assert(s1.mmu@.tlbs[core].contains_key(tlb_va));
                    assert(between(vaddr, tlb_va as nat, tlb_va as nat + s1.mmu@.tlbs[core][tlb_va].frame.size));
                    vaddr_mapping_is_being_modified_from_vaddr_unmap(c, s1, core, tlb_va, vaddr);
                    assert(s1.interp(c).vaddr_mapping_is_being_modified(d, vaddr));
                    assert(Some((base, pte)) == s1.interp(c).vaddr_mapping_is_being_modified_choose(d, vaddr));
                    assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
                }
            }
        },
        _ => {
            assert(false);
        },
    };
}

proof fn vaddr_distinct(c: os::Constants, s: os::State)
    requires
        s.inv(c),
        s.sound,
    ensures 
        forall |core1, core2| #![all_triggers]
            s.core_states.contains_key(core1) && s.core_states.contains_key(core2)
            && s.core_states[core1] !is Idle && s.core_states[core2] !is Idle
            && s.core_states[core1].vaddr() == s.core_states[core2].vaddr() ==> core1 == core2
{
    assert forall |core1, core2| #![all_triggers]
        s.core_states.contains_key(core1) && s.core_states.contains_key(core2)
        && s.core_states[core1] !is Idle && s.core_states[core2] !is Idle
        && s.core_states[core1].vaddr() == s.core_states[core2].vaddr() implies core1 == core2
    by {
        let mr1 = MemRegion {
            base: s.core_states[core1].vaddr(),
            size: s.core_states[core1].pte_size(s.interp_pt_mem()),
        };
        let mr2 = MemRegion {
            base: s.core_states[core2].vaddr(),
            size: s.core_states[core2].pte_size(s.interp_pt_mem()),
        };
        assert(overlap(mr1, mr2));
    }
}

proof fn unmap_vaddr_set_le_extra_mappings_dom(c: os::Constants, s: os::State)
    requires s.inv(c), s.sound,
    ensures s.unmap_vaddr_set() <= s.extra_mappings().dom()
{
    assert forall |vaddr| #![all_triggers] s.unmap_vaddr_set().contains(vaddr)
        implies s.extra_mappings().contains_key(vaddr)
    by {
        vaddr_distinct(c, s);
        reveal(os::State::extra_mappings);
        let core = choose|core: Core| s.is_unmap_vaddr_core(core, vaddr);
        assert(s.is_extra_vaddr_core(core, vaddr));
        assert(s.is_extra_vaddr(vaddr));
        assert(!s.candidate_vaddr_overlaps(vaddr));
    }
}

proof fn extra_mappings_preserved(c: os::Constants, s1: os::State, s2: os::State)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
        s1.effective_mappings() == s2.effective_mappings(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    hide(candidate_mapping_overlaps_existing_vmem);

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if s1.extra_mappings().contains_key(vaddr) {
            let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
            assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
            assert(s1.get_extra_vaddr_core(vaddr) == core);
            assert(s2.get_extra_vaddr_core(vaddr) == core);
            assert(s2.is_extra_vaddr(vaddr));
            // assert(!s1.candidate_vaddr_overlaps(vaddr));
            // assert(!s2.candidate_vaddr_overlaps(vaddr));
            assert(s2.extra_mappings().contains_key(vaddr));
        }
        if s2.extra_mappings().contains_key(vaddr) {
            assert(s1.extra_mappings().contains_key(vaddr));
        }
    });
}

proof fn extra_mappings_preserved_effective_mapping_inserted(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
        s1.core_states.contains_key(this_core),
        match s1.core_states[this_core] {
            CoreState::MapDone { ult_id, vaddr, pte, result: Ok(_) } => {
                !s1.effective_mappings().contains_key(vaddr)
                && s2.effective_mappings() =~= s1.effective_mappings().insert(vaddr, pte)
            }
            _ => false,
        }
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let this_vaddr = s1.core_states[this_core]->MapDone_vaddr;
    let this_pte = s1.core_states[this_core]->MapDone_pte;

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().contains_key(vaddr) {
                assert(s2.extra_mappings().contains_key(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));

                match s2.core_states[s2.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        let mappings = s2.effective_mappings();
                        assert(vaddr1 == vaddr);

                        let core1 = this_core;
                        let core2 = s2.get_extra_vaddr_core(vaddr);
                        let mr1 = MemRegion {
                            base: s1.core_states[core1].vaddr(),
                            size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                        };
                        let mr2 = MemRegion {
                            base: s1.core_states[core2].vaddr(),
                            size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                        };
                        assert(!overlap(mr1, mr2));
                        assert(!overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size },
                        ));
                    }
                    _ => { }
                }

                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().contains_key(vaddr));
            }
            if s2.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s2.is_extra_vaddr_core(core, vaddr);

                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s1.is_extra_vaddr(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));

                match s1.core_states[s1.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => {
                        monotonic_candidate_mapping_overlaps_existing_vmem(
                            s1.effective_mappings(),
                            s2.effective_mappings(),
                            vaddr,
                            pte);
                    }
                    _ => { }
                }

                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });
}

proof fn extra_mappings_preserved_effective_mapping_inserted_protect(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
        s1.core_states.contains_key(this_core),
        match s2.core_states[this_core] {
            CoreState::ProtectWaiting { vaddr, flags, .. } => {
                let new_pte = PTE { frame: s1.interp_pt_mem()[vaddr].frame, flags };
                &&& s1.effective_mappings().contains_key(vaddr)
                &&& s2.effective_mappings() =~= s1.effective_mappings().insert(vaddr, new_pte)
            }
            _ => false,
        }
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let this_vaddr = s2.core_states[this_core]->ProtectWaiting_vaddr;
    let this_flags = s2.core_states[this_core]->ProtectWaiting_flags;
    let new_pte = PTE { frame: s1.interp_pt_mem()[this_vaddr].frame, flags: this_flags };

    assert(s1.effective_mappings().contains_key(this_vaddr));

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().contains_key(vaddr) {
                assert(s2.extra_mappings().contains_key(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));

                match s2.core_states[s2.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        assert(!candidate_mapping_overlaps_existing_vmem(s2.effective_mappings(), vaddr, pte));
                        let mappings = s2.effective_mappings();
                        assert(vaddr1 == vaddr);

                        let core1 = this_core;
                        let core2 = s2.get_extra_vaddr_core(vaddr);
                        let mr1 = MemRegion {
                            base: s2.core_states[core1].vaddr(),
                            size: s2.core_states[core1].pte_size(s1.interp_pt_mem()),
                        };
                        let mr2 = MemRegion {
                            base: s1.core_states[core2].vaddr(),
                            size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                        };
                        assert(!overlap(mr1, mr2));
                        assert(!overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size },
                        ));
                    }
                    _ => { }
                }

                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().contains_key(vaddr));
            }
            if s2.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s2.is_extra_vaddr_core(core, vaddr);

                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s1.is_extra_vaddr(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));

                match s1.core_states[s1.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => {
                        monotonic_candidate_mapping_overlaps_existing_vmem(
                            s1.effective_mappings(),
                            s2.effective_mappings(),
                            vaddr,
                            pte);
                    }
                    _ => { }
                }

                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });
}

proof fn extra_mappings_submap(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            this_core != core ==> s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core| this_core != core ==> (
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            })),
        s1.core_states.contains_key(this_core),
        s2.core_states.contains_key(this_core),
        s1.core_states[this_core] is Idle,
        s1.effective_mappings() == s2.effective_mappings(),
    ensures
        s1.extra_mappings().submap_of(s2.extra_mappings())
{
    hide(candidate_mapping_overlaps_existing_vmem);

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert forall |vaddr| #[trigger] s1.extra_mappings().contains_key(vaddr)
      implies s2.extra_mappings().contains_key(vaddr)
          && s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]
    by {
        let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
        assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
        assert(s1.get_extra_vaddr_core(vaddr) == core);
        assert(s2.get_extra_vaddr_core(vaddr) == core);
        assert(s2.is_extra_vaddr(vaddr));
        assert(!s1.candidate_vaddr_overlaps(vaddr));
        assert(!s2.candidate_vaddr_overlaps(vaddr));
        assert(s2.extra_mappings().contains_key(vaddr));
    }
}

proof fn monotonic_candidate_mapping_overlaps_existing_vmem_weak(
    mappings1: Map<nat, PTE>,
    mappings2: Map<nat, PTE>,
    base: nat,
    pte: PTE,
)
    requires
        forall|va| #[trigger] mappings1.contains_key(va) ==> #[trigger] mappings2.contains_key(va)
            && mappings2[va].frame == mappings1[va].frame,
    ensures
        candidate_mapping_overlaps_existing_vmem(mappings1, base, pte)
            ==> candidate_mapping_overlaps_existing_vmem(mappings2, base, pte)
{
    assert(forall|b| #[trigger] mappings1.contains_key(b) ==> mappings2.contains_key(b));
}

proof fn monotonic_candidate_mapping_overlaps_existing_vmem(
    mappings1: Map<nat, PTE>,
    mappings2: Map<nat, PTE>,
    base: nat,
    pte: PTE,
)
    requires
        forall|va| #[trigger] mappings1.contains_key(va)
            ==> #[trigger] mappings2.contains_key(va) && mappings2[va].frame == mappings1[va].frame
    ensures
        candidate_mapping_overlaps_existing_vmem(mappings1, base, pte)
        ==> candidate_mapping_overlaps_existing_vmem(mappings2, base, pte)
{
    assert(forall |b| #[trigger] mappings1.contains_key(b) ==> mappings2.contains_key(b));
}

proof fn extra_mappings_preserved_effective_mapping_removed(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
        s2.core_states.contains_key(this_core),
        match s2.core_states[this_core] {
            CoreState::UnmapWaiting { ult_id, vaddr } => {
                s1.effective_mappings().contains_key(vaddr)
                && s2.effective_mappings() =~= s1.effective_mappings().remove(vaddr)
                && s1.interp_pt_mem().contains_key(vaddr)
            }
            _ => false,
        },
        s1.interp_pt_mem() =~= s2.interp_pt_mem(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let this_vaddr = s2.core_states[this_core]->UnmapWaiting_vaddr;

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().contains_key(vaddr) {
                assert(s2.extra_mappings().contains_key(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));

                match s2.core_states[s2.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => {
                        monotonic_candidate_mapping_overlaps_existing_vmem(
                            s2.effective_mappings(),
                            s1.effective_mappings(),
                            vaddr,
                            pte);
                    }
                    _ => { }
                }

                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().contains_key(vaddr));
            }
            if s2.extra_mappings().contains_key(vaddr) {
                let core = choose|core: Core| s2.is_extra_vaddr_core(core, vaddr);

                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s1.is_extra_vaddr(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));

                match s1.core_states[s1.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => {
                        let mappings = s1.effective_mappings();
                        assert(vaddr1 == vaddr);

                        let core1 = this_core;
                        let core2 = core;
                        let mr1 = MemRegion {
                            base: s2.core_states[core1].vaddr(),
                            size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                        };
                        let mr2 = MemRegion {
                            base: s2.core_states[core2].vaddr(),
                            size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                        };
                        assert(!overlap(mr1, mr2));
                        assert(s2.core_states[core1].vaddr() == this_vaddr);

                        assert(s2.core_states[core1].pte_size(s2.interp_pt_mem())
                            == mappings[this_vaddr].frame.size);

                        assert(mr1 == MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size });
                        assert(mr2 == MemRegion { base: vaddr, size: pte.frame.size });
                        assert(!overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size },
                        ));
                    }
                    _ => { }
                }

                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });
}

// can go either direction:
// either starting a Map operation that is destined to fail because of overlap
// (thus moving Idle -> MapWaiting) or ending such an operation (MapExecution -> MapDone Err case)
#[verifier(spinoff_prover)]
proof fn extra_mappings_preserved_for_overlap_map(c: os::Constants, s1: os::State, s2: os::State, this_core: Core)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        c.valid_core(this_core),
        forall |core: Core, vaddr: nat|
            core != this_core ==>
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        s1.core_states.contains_key(this_core),
        match s1.core_states[this_core] {
            CoreState::MapWaiting { ult_id, vaddr, pte }
            | CoreState::MapExecuting { ult_id, vaddr, pte } =>
                candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte),
            _ => false,
        },
        forall|core: Core| core != this_core ==>
            ((match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            })),
        match s2.core_states[this_core] {
            CoreState::Idle | CoreState::MapDone { result: Err(_), .. } => true,
            _ => false,
        },
        s1.effective_mappings() == s2.effective_mappings(),
        s1.interp_pt_mem() =~= s2.interp_pt_mem(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let (this_vaddr, this_pte) = match s1.core_states[this_core] {
        CoreState::MapWaiting { ult_id, vaddr, pte }
        | CoreState::MapExecuting { ult_id, vaddr, pte } => (vaddr, pte),
        _ => arbitrary(),
    };

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().contains_key(vaddr) {
                assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, this_pte));
                assert(!s1.inflight_mapunmap_vaddr().contains(vaddr));

                assert_by_contradiction!(candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, this_pte), {
                    // need to show candidate can't overlap anything in
                    // interp_pt_mem() - effective_mappings()
                    // i.e., need to show candidate can't overlap anything in
                    // inflight_mapunmap_vaddr
                    let ov_vaddr = choose|b: nat|
                        #[trigger] s1.interp_pt_mem().contains_key(b)
                        && overlap(
                            MemRegion { base: vaddr, size: this_pte.frame.size },
                            MemRegion { base: b, size: s1.interp_pt_mem()[b].frame.size },
                        );
                    assert(s1.interp_pt_mem().contains_key(ov_vaddr));
                    assert(!s1.effective_mappings().contains_key(ov_vaddr));
                    assert(s1.inflight_mapunmap_vaddr().contains(ov_vaddr));

                    let ov_core = choose|ov_core: Core|
                        #[trigger] s1.core_states.contains_key(ov_core) &&
                        s1.core_states[ov_core] !is Idle &&
                        s1.core_states[ov_core].vaddr() == ov_vaddr;
                    assert(s1.core_states.contains_key(ov_core));
                    assert(s1.core_states[ov_core].vaddr() == ov_vaddr);

                    // contradiction through inv_inflight_map_no_overlap_inflight_vmem

                    let mr1 = MemRegion {
                        base: s1.core_states[this_core].vaddr(),
                        size: s1.core_states[this_core].pte_size(s1.interp_pt_mem()),
                    };
                    let mr2 = MemRegion {
                        base: s1.core_states[ov_core].vaddr(),
                        size: s1.core_states[ov_core].pte_size(s1.interp_pt_mem()),
                    };
                    assert(overlap(mr1, mr2));

                    assert(false);
                });

                assert(s1.candidate_vaddr_overlaps(vaddr));
                //assert(s2.extra_mappings().contains_key(vaddr));
                //assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
                assert(false);
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(false);
            }
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                assert(s2.extra_mappings().contains_key(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });
}

proof fn extra_mappings_removed(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
    this_vaddr: nat,
    ult_id: nat,
    pte: PTE,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            core != this_core ==>
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        //forall |core: Core|
        //    core != this_core ==>
        //    #[trigger] s1.core_states.contains_key(core) ==>
        //    s2.core_states.contains_key(core) ==>
        //    s1.core_states[core] == s2.core_states[core]  ,

        s1.core_states.contains_key(this_core),
        match s1.core_states[this_core] {
            CoreState::MapExecuting { ult_id, vaddr, pte } =>
                !candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)
                && vaddr == this_vaddr,
            _ => false,
        },

        //s2.core_states.contains_key(this_core),
        //match s1.core_states[this_core] {
        //    CoreState::MapDone { .. } => true,
        //    _ => false,
        //},
        s2.core_states == s1.core_states.insert(this_core, CoreState::MapDone { ult_id, vaddr: this_vaddr, pte, result: Ok(()) }),
            
        s1.effective_mappings() == s2.effective_mappings(),
    ensures
        s2.extra_mappings() == s1.extra_mappings().remove(this_vaddr),
        s1.extra_mappings().contains_key(this_vaddr),
        s1.extra_mappings()[this_vaddr] == s2.interp_pt_mem()[this_vaddr],
{
    hide(candidate_mapping_overlaps_existing_vmem);

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s2.extra_mappings(), s1.extra_mappings().remove(this_vaddr), vaddr => {
        if vaddr == this_vaddr {
            assert(!s2.extra_mappings().contains_key(vaddr));
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().contains_key(vaddr));
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });

    assert(s1.is_extra_vaddr_core(this_core, this_vaddr));
    assert(s1.get_extra_vaddr_core(this_vaddr) == this_core);
    assert(s1.is_extra_vaddr(this_vaddr));

    match s1.core_states[s1.get_extra_vaddr_core(this_vaddr)] {
        CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
        | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => {
            monotonic_candidate_mapping_overlaps_existing_vmem_weak(
                s1.effective_mappings(), s1.interp_pt_mem(), this_vaddr, pte);
            assert(!candidate_mapping_overlaps_existing_vmem(
                s1.effective_mappings(),
                this_vaddr,
                pte,
            ));
        }
        _ => { }
    }
    assert(!s1.candidate_vaddr_overlaps(this_vaddr));
}

proof fn extra_mappings_inserted(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
    this_vaddr: nat,
    ult_id: nat,
)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            core != this_core ==>
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            core != this_core ==>
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        //    s1.core_states[core] == s2.core_states[core]  ,

        s1.core_states.contains_key(this_core),
        s1.core_states[this_core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: None },

        s2.core_states == s1.core_states.insert(this_core, 
            CoreState::UnmapExecuting { ult_id, vaddr: this_vaddr, result: Some(Ok(s1.interp_pt_mem()[this_vaddr])) }),
            
        s1.effective_mappings() == s2.effective_mappings(),
    ensures
        !s1.extra_mappings().contains_key(this_vaddr),
        s2.extra_mappings() =~= s1.extra_mappings().insert(this_vaddr, s1.interp_pt_mem()[this_vaddr]),
{
    hide(candidate_mapping_overlaps_existing_vmem);

    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s2.extra_mappings(), s1.extra_mappings().insert(this_vaddr, s1.interp_pt_mem()[this_vaddr]), vaddr => {
        if vaddr == this_vaddr {
            assert(s2.is_extra_vaddr_core(this_core, this_vaddr));
            assert(s2.get_extra_vaddr_core(this_vaddr) == this_core);

            assert(s2.extra_mappings().contains_key(vaddr));
            assert(s2.extra_mappings()[vaddr] == s1.interp_pt_mem()[this_vaddr]);
        } else {
            if s1.extra_mappings().contains_key(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().contains_key(vaddr));
            }
            if s2.extra_mappings().contains_key(vaddr) {
                assert(s1.extra_mappings().contains_key(vaddr));
            }
        }
    });
}

proof fn vaddr_mapping_is_being_modified_from_vaddr_unmap(
    c: os::Constants,
    s: os::State,
    core: Core,
    tlb_va: usize,
    vaddr: nat,
)
    requires
        s.inv(c),
        s.sound,
        s.extra_mappings().contains_key(tlb_va as nat)
           || s.inflight_mapunmap_vaddr().contains(tlb_va as nat),
        c.valid_core(core),
        s.mmu@.tlbs[core].contains_key(tlb_va),
        between(vaddr, tlb_va as nat, tlb_va as nat + s.mmu@.tlbs[core][tlb_va].frame.size),
        //c.valid_ult(thread_id),
        //core == c.ult2core[thread_id],
    ensures
        s.interp(c).vaddr_mapping_is_being_modified(c.interp(), vaddr),
        s.interp(c).vaddr_mapping_is_being_modified_choose(c.interp(), vaddr)
            == Some((tlb_va as nat, s.mmu@.tlbs[core][tlb_va]))
{
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

    reveal(os::State::extra_mappings);
    vaddr_distinct(c, s);

    if s.unmap_vaddr_set().contains(tlb_va as nat) {
        let core1 = choose|core1: Core|
            #[trigger] s.core_states.contains_key(core1) &&
            s.core_states[core1] !is Idle &&
            s.core_states[core1].vaddr() == tlb_va;
        assert(s.core_states.contains_key(core1));
        // assert(!s.core_states[core1].is_idle());
        // assert(s.core_states[core1].vaddr() == tlb_va);
        assert(c.valid_core(core1));

        assert(s.core_states[core1].PTE() == s.mmu@.tlbs[core][tlb_va]);

        let thread1 = s.core_states[core1].ult_id();
        assert(c.interp().valid_thread(thread1));

        assert(s.interp(c).vaddr_mapping_is_being_modified(c.interp(), vaddr));

        let t = s.interp(c);
        let d = c.interp();
        let thread = t.vaddr_mapping_is_being_modified_choose_thread(d, vaddr);
        assert(thread == thread1) by {
            let core1 = c.ult2core[thread1];
            let core2 = c.ult2core[thread];
            assert(s.inv_inflight_map_no_overlap_inflight_vmem(c));
            let mr1 = MemRegion {
                    base: s.core_states[core1].vaddr(),
                    size: s.core_states[core1].pte_size(s.interp_pt_mem()),
                };
            let mr2 = MemRegion {
                    base: s.core_states[core2].vaddr(),
                    size: s.core_states[core2].pte_size(s.interp_pt_mem()),
                };
            assert(between(vaddr, mr1.base, mr1.base + mr1.size));
            assert(between(vaddr, mr2.base, mr2.base + mr2.size));
            assert(overlap(mr1, mr2));
            assert(core1 == core2);
            assert(thread1 == thread);
        }

        assert(s.interp(c).vaddr_mapping_is_being_modified_choose(c.interp(), vaddr)
            == Some((tlb_va as nat, s.mmu@.tlbs[core][tlb_va])));
    } else {
        assert(s.mmu@.tlbs[core].dom().map(|v| v as nat).contains(tlb_va as nat));
        assert(s.interp_pt_mem().contains_key(tlb_va as nat));

        let core1 = choose|core1: Core|
            #[trigger] s.core_states.contains_key(core1) &&
            s.core_states[core1] !is Idle &&
            s.core_states[core1].vaddr() == tlb_va;
        assert(s.core_states.contains_key(core1));
        assert(c.valid_core(core1));

        let thread1 = s.core_states[core1].ult_id();
        assert(c.interp().valid_thread(thread1));
        

        // Trigger in candidate_mapping_overlaps_existing_vmem
        let _ = s.effective_mappings().contains_key(tlb_va as nat);

        assert(s.interp_pt_mem()[tlb_va as nat] == s.mmu@.tlbs[core][tlb_va]);
        assert(s.interp(c).vaddr_mapping_is_being_modified(c.interp(), vaddr));

        let t = s.interp(c);
        let d = c.interp();
        let thread = t.vaddr_mapping_is_being_modified_choose_thread(d, vaddr);
        assert(thread == thread1) by {
            let core1 = c.ult2core[thread1];
            let core2 = c.ult2core[thread];
            assert(s.inv_inflight_map_no_overlap_inflight_vmem(c));
            let mr1 = MemRegion {
                    base: s.core_states[core1].vaddr(),
                    size: s.core_states[core1].pte_size(s.interp_pt_mem()),
                };
            let mr2 = MemRegion {
                    base: s.core_states[core2].vaddr(),
                    size: s.core_states[core2].pte_size(s.interp_pt_mem()),
                };
            assert(between(vaddr, mr1.base, mr1.base + mr1.size));
            assert(between(vaddr, mr2.base, mr2.base + mr2.size));
            assert(overlap(mr1, mr2));
            assert(core1 == core2);
            assert(thread1 == thread);
        }

        assert(s.interp(c).vaddr_mapping_is_being_modified_choose(c.interp(), vaddr)
            == Some((tlb_va as nat, s.mmu@.tlbs[core][tlb_va])));
    }
}

spec fn no_overlaps(m: Map<nat, PTE>) -> bool {
    forall |i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          ==> i + m[i].frame.size <= j
           || j + m[j].frame.size <= i
}

spec fn no_overlaps_pmem(m: Map<nat, PTE>) -> bool {
    forall |i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          ==> !overlap(m[i].frame, m[j].frame)
}

spec fn bounds(c: os::Constants, m: Map<nat, PTE>) -> bool {
    forall |i|
        #[trigger] m.contains_key(i)
          ==> candidate_mapping_in_bounds(i, m[i])
           && candidate_mapping_in_bounds_pmem(c.common, m[i])
}

proof fn bounds_applied_mappings(c: os::Constants, s: os::State)
    requires s.inv(c), s.sound,
    ensures bounds(c, s.applied_mappings()),
{
    reveal(os::State::extra_mappings);
    vaddr_distinct(c, s);
    let m = s.applied_mappings();
    assert forall |i|
        #[trigger] m.contains_key(i)
        implies candidate_mapping_in_bounds(i, m[i])
           && candidate_mapping_in_bounds_pmem(c.common, m[i])
    by {
        if s.interp_pt_mem().contains_key(i) {
            assert(candidate_mapping_in_bounds(i, m[i]));
            assert(s.interp_pt_mem().contains_pair(i, m[i]));
            assert(candidate_mapping_in_bounds_pmem(c.common, m[i]));
        } else {
            assert(candidate_mapping_in_bounds(i, m[i]));
            assert(candidate_mapping_in_bounds_pmem(c.common, m[i]));
        }
    }
}

proof fn no_overlaps_pmem_applied_mappings(c: os::Constants, s: os::State)
    requires s.inv(c), s.sound,
    ensures no_overlaps_pmem(s.applied_mappings()),
{
    reveal(os::State::extra_mappings);
    vaddr_distinct(c, s);
    let m = s.applied_mappings();

    assert forall |i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          && overlap(m[i].frame, m[j].frame)
          implies false
    by {
        if s.interp_pt_mem().contains_key(i) {
            if s.interp_pt_mem().contains_key(j) {
                assert(false);
            } else {
                assert(false);
            }
        } else {
            if s.interp_pt_mem().contains_key(j) {
                assert(false);
            } else {
                let core1 = s.get_extra_vaddr_core(i);
                let core2 = s.get_extra_vaddr_core(j);
                let mr1 = MemRegion {
                    base: s.core_states[core1].paddr(s.interp_pt_mem()),
                    size: s.core_states[core1].pte_size(s.interp_pt_mem()),
                };
                let mr2 = MemRegion {
                    base: s.core_states[core2].paddr(s.interp_pt_mem()),
                    size: s.core_states[core2].pte_size(s.interp_pt_mem()),
                };
                assert(c.valid_core(core1));
                assert(c.valid_core(core2));
                assert(!overlap(mr1, mr2));
                assert(false);
            }
        }
    }
}

proof fn no_overlaps_applied_mappings(c: os::Constants, s: os::State)
    requires
        s.inv(c),
        s.sound,
    ensures no_overlaps(s.applied_mappings()),
{
    reveal(os::State::extra_mappings);
    vaddr_distinct(c, s);
    let m = s.applied_mappings();

    assert forall|i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          && !(i + m[i].frame.size <= j || j + m[j].frame.size <= i)
          && !s.interp_pt_mem().contains_key(i)
          && s.interp_pt_mem().contains_key(j)
          implies false
    by {
        if s.inflight_mapunmap_vaddr().contains(j) {
            let core1 = s.get_extra_vaddr_core(i);
            let core2 = choose|core2: Core|
                #[trigger] s.core_states.contains_key(core2) &&
                s.core_states[core2] !is Idle &&
                s.core_states[core2].vaddr() == j;
            let mr1 = MemRegion {
                base: s.core_states[core1].vaddr(),
                size: s.core_states[core1].pte_size(s.interp_pt_mem()),
            };
            let mr2 = MemRegion {
                base: s.core_states[core2].vaddr(),
                size: s.core_states[core2].pte_size(s.interp_pt_mem()),
            };
            assert(c.valid_core(core1));
            assert(c.valid_core(core2));
            assert(!overlap(mr1, mr2));
            //assert(mr1.base == i);
            //assert(mr2.base == j);
            //assert(mr1.size == m[i].frame.size);
            //assert(mr2.size == m[j].frame.size);
            assert(false);
        } else {
            assert(s.is_extra_vaddr(i));
            match s.core_states[s.get_extra_vaddr_core(i)] {
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. } => {
                    assert(!candidate_mapping_overlaps_existing_vmem(s.effective_mappings(), i, pte));
                    assert(s.effective_mappings().contains_key(j));
                    assert(!s.inflight_protect_params().contains_key(j));

                    assert(false);
               },
               CoreState::ProtectExecuting { vaddr, result: Some(Ok(_)), .. }
               | CoreState::ProtectOpDone { vaddr, result: Ok(_), .. }
               | CoreState::ProtectShootdownWaiting { vaddr, result: Ok(_), .. } => {

               },
               _ => {
                  assert(false);
               }
            }
        }
    }

    assert forall|i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          && !(i + m[i].frame.size <= j || j + m[j].frame.size <= i)
          implies false
    by {
        if s.interp_pt_mem().contains_key(i) {
            if s.interp_pt_mem().contains_key(j) {
                no_overlaps_interp_pt_mem(c, s);
                assert(false);
            } else {
                // handled above (symmetric)
            }
        } else {
            if s.interp_pt_mem().contains_key(j) {
                // handled above
            } else {
                let core1 = s.get_extra_vaddr_core(i);
                let core2 = s.get_extra_vaddr_core(j);
                let mr1 = MemRegion {
                    base: s.core_states[core1].vaddr(),
                    size: s.core_states[core1].pte_size(s.interp_pt_mem()),
                };
                let mr2 = MemRegion {
                    base: s.core_states[core2].vaddr(),
                    size: s.core_states[core2].pte_size(s.interp_pt_mem()),
                };
                assert(c.valid_core(core1));
                assert(c.valid_core(core2));
                assert(!overlap(mr1, mr2));
                assert(false);
            }
        }
    }
}

proof fn no_overlaps_interp_pt_mem(c: os::Constants, s: os::State)
    requires s.inv(c),
    ensures no_overlaps(s.interp_pt_mem()),
{
    let m = s.interp_pt_mem();
    assert forall |i, j|
        #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) && i != j
          && i + m[i].frame.size > j
          && j + m[j].frame.size > i
          implies false
    by {
        reveal(PTMem::view);
        if i <= j < i + m[i].frame.size {
            s.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(i as usize, j as usize);
            assert(false);
        } else if j <= i < j + m[j].frame.size {
            s.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(j as usize, i as usize);
            assert(false);
        } else {
            assert(false);
        }
    }
}

proof fn interp_vmem_subrange(c: os::Constants, s: os::State, base: nat, pte: PTE, vaddr: int, size: int)
    requires
        no_overlaps(s.applied_mappings()),
        s.applied_mappings().contains_key(base),
        s.applied_mappings()[base] == pte,
        base <= vaddr,
        size >= 0,
        vaddr + size <= base + pte.frame.size,

        base + pte.frame.size <= s.interp_vmem(c).len(),
        pte.frame.base + pte.frame.size <= s.mmu@.phys_mem.len(),

    ensures ({
        let paddr = pte.frame.base + vaddr - base;
        s.interp_vmem(c).subrange(vaddr, vaddr + size)
            == s.mmu@.phys_mem.subrange(paddr, paddr + size)
    })
{
    let paddr = pte.frame.base + vaddr - base;

    vstd::seq_lib::assert_seqs_equal!(
        s.interp_vmem(c).subrange(vaddr, vaddr + size),
        s.mmu@.phys_mem.subrange(paddr, paddr + size),
        idx => {
            let v = vaddr + idx;
            let p = paddr + idx;

            let (base0, pte0) = os::State::base_and_pte_for_vaddr(s.applied_mappings(), vaddr);

            assert(s.applied_mappings().contains_pair(base, pte));
            assert(between(v as nat, base, base + pte.frame.size));

            assert(s.applied_mappings().contains_pair(base0, pte0)
              && between(v as nat, base0, base0 + pte0.frame.size));

            assert(base0 == base);
            assert(pte0 == pte);

            assert(s.interp_vmem(c)[v] == s.mmu@.phys_mem[p]);
        }
    );
}

proof fn interp_vmem_update_range(c: os::Constants, s: os::State, base: nat, pte: PTE, vaddr: int, size: int, new: Seq<u8>,)
    requires
        no_overlaps(s.applied_mappings()),
        no_overlaps_pmem(s.applied_mappings()),
        bounds(c, s.applied_mappings()),
        s.mmu@.phys_mem.len() == c.common.range_mem.1,
        s.applied_mappings().contains_key(base),
        s.applied_mappings()[base] == pte,
        base <= vaddr,
        size >= 0,
        vaddr + size <= base + pte.frame.size,

        base + pte.frame.size <= s.interp_vmem(c).len(),
        pte.frame.base + pte.frame.size <= s.mmu@.phys_mem.len(),

        size == new.len(),

    ensures ({
        let paddr = pte.frame.base + vaddr - base;
        update_range(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem), vaddr, new)
          == os::State::vmem_apply_mappings(s.applied_mappings(), update_range(s.mmu@.phys_mem, paddr, new))
    })
{
    let paddr = pte.frame.base + vaddr - base;

    let b1 = update_range(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem), vaddr, new);
    let b2 = os::State::vmem_apply_mappings(s.applied_mappings(), update_range(s.mmu@.phys_mem, paddr, new));

    assert(b1.len() == b2.len());

    vstd::assert_seqs_equal!(b1, b2, idx => {
        let (base0, pte0) = os::State::base_and_pte_for_vaddr(s.applied_mappings(), idx);

        if base <= idx < base + pte.frame.size {
            assert(s.applied_mappings().contains_pair(base, pte));
            assert(between(idx as nat, base, base + pte.frame.size));

            assert(s.applied_mappings().contains_pair(base0, pte0)
              && between(idx as nat, base0, base0 + pte0.frame.size));

            assert(base == base0);
            assert(pte == pte0);

            assert(b1[idx] == b2[idx]);
        } else {
            if os::State::has_base_and_pte_for_vaddr(s.applied_mappings(), idx) {
                assert(base != base0);
                let p_idx = pte0.frame.base + idx - base0;
                assert(!(vaddr <= idx < vaddr + new.len()));

                assert(pte0.frame.base + pte0.frame.size <= s.mmu@.phys_mem.len());

                assert(base0 <= idx < base0 + pte0.frame.size);
                assert(pte0.frame.base <= p_idx < pte0.frame.base + pte0.frame.size);

                assert(base <= vaddr <= vaddr + new.len() <= base + pte.frame.size);
                assert(s.applied_mappings().contains_key(base));
                assert(s.applied_mappings().contains_key(base0));
                assert(pte.frame.base <= paddr <= paddr + new.len() <= pte.frame.base + pte.frame.size);

                // need physical ranges of the mappings don't overlap
                assert(!(paddr <= p_idx < paddr + new.len()));

                assert(paddr + new.len() <= s.mmu@.phys_mem.len());
                assert(0 <= p_idx < s.mmu@.phys_mem.len());

                assert(b1[idx] == os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem)[idx]);
                assert(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem)[idx]
                    == s.mmu@.phys_mem[p_idx]);
                assert(s.mmu@.phys_mem[p_idx]
                    == update_range(s.mmu@.phys_mem, paddr, new)[p_idx]);

                assert(b1[idx] == b2[idx]);
            } else {
                assert(b1[idx] == b2[idx]);
            }
        }
    });
}

proof fn relevant_mem_preserved(c: os::Constants, s1: os::State, s2: os::State)
    requires
        s1.inv(c), s1.sound,
        s2.inv(c), s2.sound,
        s1.applied_mappings().submap_of(s2.applied_mappings()),
        s1.mmu@.phys_mem == s2.mmu@.phys_mem,
    ensures
        forall|mem_vaddr: nat| #![auto]
            hlspec::is_in_mapped_region(c.common.phys_mem_size, s1.interp(c).mappings, mem_vaddr)
            ==> s2.interp(c).mem[mem_vaddr as int] === s1.interp(c).mem[mem_vaddr as int]
{
    assert forall|mem_vaddr: nat| #![auto]
            hlspec::is_in_mapped_region(c.common.phys_mem_size, s1.interp(c).mappings, mem_vaddr)
            implies s2.interp(c).mem[mem_vaddr as int] === s1.interp(c).mem[mem_vaddr as int]
    by {
        let mappings = s1.interp(c).mappings;
        let (base, pte) = choose |base: nat, pte: PTE|
            mappings.contains_pair(base, pte)
            && between(mem_vaddr, base, base + pte.frame.size)
            && pte.frame.base + (mem_vaddr - base) < c.common.phys_mem_size;
        assert(mappings.contains_pair(base, pte));
        assert(s1.applied_mappings().contains_key(base));

        assert(s2.applied_mappings().contains_key(base));
        assert(s2.applied_mappings()[base].frame == pte.frame);

        assert(os::State::has_base_and_pte_for_vaddr(s1.applied_mappings(), mem_vaddr as int));
        assert(os::State::has_base_and_pte_for_vaddr(s2.applied_mappings(), mem_vaddr as int));

        no_overlaps_applied_mappings(c, s1);
        no_overlaps_applied_mappings(c, s2);

        // let (base1, pte1) = os::State::base_and_pte_for_vaddr(s1.applied_mappings(), mem_vaddr as int);
        // let (base2, pte2) = os::State::base_and_pte_for_vaddr(s2.applied_mappings(), mem_vaddr as int);

        bounds_applied_mappings(c, s1);
        x86_arch_spec_upper_bound();
        assert(mem_vaddr < MAX_BASE);
    }
}

proof fn step_MapStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_MapStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_MapStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let ult_id = lbl->MapStart_thread_id;
    let vaddr = lbl->MapStart_vaddr;
    let pte = lbl->MapStart_pte;

    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    assert(hlspec::step_Map_enabled(s1.interp(c).thread_state.values(), s1.interp(c).mappings, vaddr, pte));
    assert(hl_c.valid_thread(ult_id));
    assert(s1.interp(c).thread_state[ult_id] === hlspec::ThreadState::Idle);
    lemma_map_soundness_equality(c, s1, vaddr, pte);

    if hlspec::step_Map_sound(s1.interp(c).mappings, s1.interp(c).thread_state.values(), vaddr, pte) {
        assert(hl_s1.sound == hl_s2.sound);
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        ));
        lemma_map_insert_values_equality(
            hl_s1.thread_state,
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        );
        assert(hl_s2.thread_state.values().insert(hlspec::ThreadState::Idle)
            =~= hl_s1.thread_state.values().insert(hlspec::ThreadState::Map { vaddr, pte }));
        assert(s1.interp_pt_mem() == s2.interp_pt_mem());
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
        assert forall|base| s1.inflight_unmap_vaddr().contains(base) implies s2.inflight_unmap_vaddr().contains(base) by {
            let threadstate = choose|thread_state|
                {
                    &&& s1.interp_thread_state(c).values().contains(thread_state)
                    &&& s1.interp_pt_mem().contains_key(base)
                    &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                    &&& vaddr === base
                };
            assert(s2.interp_thread_state(c).values().contains(threadstate));
        }
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
        assert(s1.inflight_mapunmap_vaddr() =~= s2.inflight_mapunmap_vaddr()) by {
            assert(s2.inflight_mapunmap_vaddr().subset_of(s1.inflight_mapunmap_vaddr()));
            assert forall|v| s1.inflight_mapunmap_vaddr().contains(v) implies s2.inflight_mapunmap_vaddr().contains(v) by {
                    if !s1.inflight_unmap_vaddr().contains(v) {
                        let map_core = choose|core| s1.core_states.contains_key(core) && s1.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:v, result: Ok(()), .. };
                        assert(s2.core_states.contains_key(map_core));
                        assert(s2.interp_pt_mem().contains_key(v));
                    }
                }
            assert(s1.inflight_mapunmap_vaddr().subset_of(s2.inflight_mapunmap_vaddr()));
        }
        assert(s1.effective_mappings() =~= s2.effective_mappings()) by {
            assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
                assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                    <==> s2.is_inflight_protect_vaddr_core(va, core));
            };
        };
        assert(hl_s2.mappings === hl_s1.mappings);
        assert(hlspec::state_unchanged_besides_thread_state_and_mem(
            hl_s1,
            hl_s2,
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        ));

        if candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte) {
            extra_mappings_preserved_for_overlap_map(c, s2, s1, core);
            assert(hl_s1.mem == hl_s2.mem);
        } else {
            extra_mappings_submap(c, s1, s2, core);
            relevant_mem_preserved(c, s1, s2);
        }

    } else {
        assert(!s2.sound);
        assert(hlspec::unsound_state(hl_s1, hl_s2));
    };
}

proof fn step_MapOpChange_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, paddr: usize, value: usize,  lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_MapOpChange(c, s1, s2, core, paddr, value, lbl),
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c), lbl)
{
    broadcast use to_rl1::next_refines;
    //interpretations
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    //corestate
    assert(s1.core_states[core] is MapExecuting);
    let ult_id = s1.core_states[core]->MapExecuting_ult_id;
    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
    let pte = s1.core_states[core]->MapExecuting_pte;

    //First goal prove soundess
    assert(hl_s2.sound);

    //Second goal: prove  //assert(hl_s1.thread_state === hl_s2.thread_state);
    assert(s1.core_states[core] is MapExecuting);
    assert(hl_s1.thread_state.dom() === hl_s2.thread_state.dom());
    assert forall|key| #[trigger]
        hl_s1.thread_state.contains_key(key) implies hl_s1.thread_state[key] == hl_s2.thread_state[key] by {
        assert(c.valid_ult(key));
        assert(hl_s2.thread_state.contains_key(key));
        let core_of_key = c.ult2core[key];
        assert(c.valid_core(core));
        assert(s1.core_states[core].is_in_crit_sect());
        assert(c.valid_core(core_of_key));
        if s1.core_states[core_of_key].is_in_crit_sect() {
            assert(core_of_key === core);
        } else {
            assert(!(core_of_key === core));
            assert(!s1.core_states[core_of_key].is_in_crit_sect());
            assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
            assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            if s1.core_states.index(core_of_key) is UnmapWaiting {
                let vaddr_of_key = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                if vaddr_of_key == vaddr {
                    assert(overlap(
                        MemRegion {
                            base: s2.core_states[core_of_key].vaddr(),
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                        },
                    ));
                }
            } else if s1.core_states.index(core_of_key) is ProtectWaiting {
                let vaddr_of_key = s1.core_states[core_of_key]->ProtectWaiting_vaddr;
                if vaddr_of_key == vaddr {
                    assert(overlap(
                        MemRegion {
                            base: s2.core_states[core_of_key].vaddr(),
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                        },
                    ));
                }
            }
        }
    }
    assert(hl_s1.thread_state =~= hl_s2.thread_state);

    //third goal: prove
    //(hl_s2.mappings === hl_s1.mappings);
    //(hl_s2.mem === hl_s1.mem); follows directly

    assert(s1.effective_mappings() =~= s2.effective_mappings()) by {
        assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
            assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                ==> s2.is_inflight_protect_vaddr_core(va, core));
            assert forall|va, core| s2.is_inflight_protect_vaddr_core(va, core)
                implies s1.is_inflight_protect_vaddr_core(va, core)
            by {
                // XXX: easy, inflight protect and map don't overlap, so this mapping can't
                // have been created by the MapOpChange step
                // (same proof also needed in os_invariant)
                assume(s1.interp_pt_mem().contains_key(va));
            };
        };
        // ==> direction
        assert(!s1.interp_pt_mem().contains_key(vaddr));
        assert(!s1.effective_mappings().contains_key(vaddr));
        assert(s2.interp_pt_mem().remove(vaddr) =~= s1.interp_pt_mem());
        assert(s1.effective_mappings().dom().subset_of(s2.effective_mappings().dom()));

        // <== direction
        assert(s2.interp_pt_mem().contains_key(vaddr) && s2.core_states.contains_key(core) &&
                s2.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:vaddr, result: Ok(()), .. });
        assert(s2.inflight_mapunmap_vaddr().contains(vaddr));
        assert forall |v| s2.effective_mappings().contains_key(v) implies s1.effective_mappings().contains_key(v) by {
            if (v == vaddr || !s1.inflight_mapunmap_vaddr().contains(v)) {
                assert(!s2.effective_mappings().contains_key(vaddr));
            } else {
                assert(s1.inflight_unmap_vaddr().contains(v));
                let unmap_core = choose|cr|
                    s1.core_states.contains_key(cr) && match s1.core_states[cr] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === v
                        },
                        _ => false,
                    };
                assert(s2.interp_pt_mem().contains_key(v));
                // assert(!(unmap_core == core));
                assert(s2.core_states.contains_key(unmap_core));
                // assert(s1.core_states[unmap_core] == s2.core_states[unmap_core]);
                assert(s2.inflight_unmap_vaddr().contains(v));
            }
        }
    }

    extra_mappings_removed(c, s1, s2, core, vaddr, ult_id, pte);
    assert(s1.applied_mappings() =~= s2.applied_mappings());
}

proof fn step_MapEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_MapEnd(c, s1, s2, core, lbl),
    ensures
        hlspec::step_MapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl)
{
    //interpretation
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    //label
    let vaddr = lbl->MapEnd_vaddr;
    let thread_id = lbl->MapEnd_thread_id;
    //core_state
    let ult_id = s1.core_states[core]->MapDone_ult_id;
    let vaddr2 = s1.core_states[core]->MapDone_vaddr;
    let pte = s1.core_states[core]->MapDone_pte;
    let result = s1.core_states[core]->MapDone_result;

    assert(hl_s2.thread_state === hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Idle));

    assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
        assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
            <==> s2.is_inflight_protect_vaddr_core(va, core));
    };
    assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());

    if result is Ok {
        //proofgoal: ! os overlap => ! hl overlap
        //by inv_overlap_of_mapped_maps-invariant we know:
        assert(!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem().remove(vaddr), vaddr, pte));
        //thereby follows as effective mappings is always a subset of interp_pt_mem and vaddr not being in effective mappings:
        assert(!candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte)) by {
            assert(s1.core_states.contains_key(core));
            assert(s1.inflight_mapunmap_vaddr().contains(vaddr));
            assert(!s1.effective_mappings().contains_key(vaddr));
            assert(s1.effective_mappings().dom().subset_of(s2.interp_pt_mem().remove(vaddr).dom()));
        }

        //proofgoal (1/4): (result is Ok);
        assert ( result is Ok);

        //proofgoal (2/4): ( hl_s2.mappings === hl_s1.mappings.insert(vaddr, pte))
        assert(s1.interp_pt_mem().contains_pair(vaddr, pte));
        assert(!s1.inflight_unmap_vaddr().contains(vaddr)) by {
            let unmap_vaddr = vaddr;
            if (s1.inflight_unmap_vaddr().contains(vaddr)) {
                let unmap_core = choose |c: Core|
                s1.core_states.contains_key(c) && match s1.core_states[c] {
                    os::CoreState::UnmapWaiting { ult_id, vaddr }
                    | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                        vaddr == unmap_vaddr
                    },
                    _ => false,
                };
                assert(s1.core_states[unmap_core] is UnmapWaiting);
                assert(s1.interp_pt_mem().contains_key(vaddr));
                assert(s1.core_states[unmap_core].pte_size(s1.interp_pt_mem()) == s1.interp_pt_mem()[vaddr].frame.size);
                assert(s1.interp_pt_mem()[vaddr].frame.size > 0);
                assert(c.valid_core(core));
                assert(c.valid_core(unmap_core));
                assert(s1.core_states[core] !is Idle);
                assert(s1.core_states[unmap_core] !is Idle);
                assert(overlap(
                    MemRegion {
                        base: s1.core_states[core].vaddr(),
                        size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[unmap_core].vaddr(),
                        size: s1.core_states[unmap_core].pte_size(s1.interp_pt_mem()),
                    }));
                assert(core != unmap_core);
                // contradiction to inflight_map_no_overlap_inflight_vmem
                assert(false);
            }
        }
        assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
        assert(!s1.inflight_unmap_vaddr().contains(vaddr));
        assert forall|idx|
            s1.inflight_unmap_vaddr().contains(
                idx,
            ) implies s2.inflight_unmap_vaddr().contains(idx) by {
            if s1.inflight_unmap_vaddr().contains(idx) {
                assert(s1.interp_pt_mem().contains_key(idx));
                let unmap_core = choose|unmap_core|
                    s1.core_states.contains_key(unmap_core)
                        && match s1.core_states[unmap_core] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === idx
                        },
                        _ => false,
                    };
                if unmap_core != core {
                    assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                    assert(s2.interp_pt_mem().contains_key(idx));
                    assert(s2.core_states.contains_key(unmap_core));
                    assert(s1.core_states[unmap_core] === s2.core_states[unmap_core]);
                }
            }
        };
        assert forall|idx| s2.inflight_unmap_vaddr().contains(idx)
            implies s1.inflight_unmap_vaddr().contains(idx)
        by {
            if s2.inflight_unmap_vaddr().contains(idx) {
                assert(s2.interp_pt_mem().contains_key(idx));
                let unmap_core = choose|unmap_core|
                    s2.core_states.contains_key(unmap_core)
                        && match s1.core_states[unmap_core] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === idx
                        },
                        _ => false,
                    };
                if idx != vaddr {
                    if unmap_core != core {
                        assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                        assert(s2.interp_pt_mem().contains_key(idx));
                        assert(s2.core_states.contains_key(unmap_core));
                        assert(s1.core_states[unmap_core] === s2.core_states[unmap_core]);
                    }
                } else {
                    assert(s1.core_states[core] !is Idle
                        && s1.core_states[unmap_core] !is Idle && overlap(
                        MemRegion {
                            base: s1.core_states[core].vaddr(),
                            size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s1.core_states[unmap_core].vaddr(),
                            size: s1.core_states[unmap_core].pte_size(
                                s1.interp_pt_mem(),
                            ),
                        },
                    ));
                }
            }
        };
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
        assert(!s2.inflight_mapunmap_vaddr().contains(vaddr));
        assert(s1.inflight_mapunmap_vaddr() =~= s1.inflight_unmap_vaddr().insert(vaddr));
        assert(s2.interp_pt_mem().union_prefer_right(s2.inflight_protect_params())
                =~= s1.interp_pt_mem().union_prefer_right(s1.inflight_protect_params()));

        assert forall|core2| !s1.is_inflight_protect_vaddr_core(vaddr, core2) by {
            assert_by_contradiction!(!s1.is_inflight_protect_vaddr_core(vaddr, core2), {
                assert(core != core2);
                assert(s1.core_states.values().contains(s1.core_states[core2]));
                // contradicts inv_inflight_map_no_overlap_inflight_vmem
                assert(overlap(
                        MemRegion {
                            base: s1.core_states[core].vaddr(),
                            size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s1.core_states[core2].vaddr(),
                            size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                        }));
            });
        };
        assert(hl_s2.mappings =~= hl_s1.mappings.insert(vaddr, pte));

        extra_mappings_preserved_effective_mapping_inserted(c, s1, s2, core);
    } else {
        //proofgoal: os overlap => hl overlap
        assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
        assert(candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte)) by {
            let os_overlap_vaddr = choose|b: nat| #![auto] {
                &&& s1.interp_pt_mem().contains_key(b)
                &&& overlap(
                    MemRegion { base: vaddr, size: pte.frame.size },
                    MemRegion { base: b, size: s1.interp_pt_mem()[b].frame.size },
                )
            };
            if s1.inflight_mapunmap_vaddr().contains(os_overlap_vaddr) {
                assert(s1.inflight_unmap_vaddr().contains(os_overlap_vaddr));
                let os_overlap_core = choose |core: Core|
                s1.core_states.contains_key(core) && match s1.core_states[core] {
                    os::CoreState::UnmapWaiting { ult_id, vaddr }
                    | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
                    | os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                        vaddr === os_overlap_vaddr
                    },
                    _ => false,
                };
                assert(c.valid_core(core));
                assert(c.valid_core(os_overlap_core));
                assert(s1.core_states[core] !is Idle);
                assert(s1.core_states[os_overlap_core] !is Idle);
                assert(overlap(
                    MemRegion {
                        base: s1.core_states[core].vaddr(),
                        size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[os_overlap_core].vaddr(),
                        size: s1.core_states[os_overlap_core].pte_size(s1.interp_pt_mem()),
                    }));
                assert(core != os_overlap_core);
                // contradiction to inflight_map_no_overlap_inflight_vmem
                assert(false);
            } else {
                assert(s1.effective_mappings().contains_key(os_overlap_vaddr));
            }
        }

        //proofgoal (1/3) result is Err
        assert(result is Err);

        //proofgoal (2/3) s2.mappings === s1.mappings
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr()) by {
            assert(s2.inflight_unmap_vaddr().subset_of(s1.inflight_unmap_vaddr()));
            assert(s1.core_states[core] is MapDone);
            assert(s1.core_states.remove(core) =~= s2.core_states.remove(core));
            assert(s1.inflight_unmap_vaddr().subset_of(s2.inflight_unmap_vaddr()));
        };
        assert(s1.inflight_unmap_vaddr() =~= s1.inflight_mapunmap_vaddr());
        assert(s1.inflight_mapunmap_vaddr() =~= s2.inflight_mapunmap_vaddr());
        assert(s2.effective_mappings() =~= s1.effective_mappings());

        extra_mappings_preserved(c, s1, s2);

        //proofgoal (3/3) s2.mem === s1.mem
        assert(hl_s1.mem =~= hl_s2.mem);
    }
}

proof fn step_UnmapStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    //label
    let vaddr = lbl->UnmapStart_vaddr;
    let ult_id = lbl->UnmapStart_thread_id;

    //interpretation
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let pte = if s1.interp_pt_mem().contains_key(vaddr) { Some(s1.interp_pt_mem()[vaddr]) } else { None };
    let hl_pte = if hl_s1.mappings.contains_key(vaddr) { Some(hl_s1.mappings[vaddr]) } else { None };

    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };

    lemma_unmap_soundness_equality(c, s1, vaddr, pte_size);

    assert forall|va| s1.inflight_mapunmap_vaddr().contains(va) implies s2.inflight_mapunmap_vaddr().contains(va) by {
        let core2 = s1.inflight_mapunmap_vaddr_choose_core(va);
        assert(core2 != core);
        assert(s2.core_states.contains_key(core2));
    }

    assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
        assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
            <==> s2.is_inflight_protect_vaddr_core(va, core));
    };

    if pte == hl_pte {
        if hlspec::step_Unmap_sound(hl_s1, vaddr, pte_size) {
            assert(hl_s1.sound == hl_s2.sound);
            assert(c.valid_core(c.ult2core[ult_id]));
            assert(hl_s2.thread_state =~= hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Unmap { vaddr, pte }));
            if pte is None {
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert(hl_s2.mappings === hl_s1.mappings);
                extra_mappings_preserved(c, s1, s2);
                assert(hl_s1.mappings =~= hl_s1.mappings.remove(vaddr));
                assert(hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            } else {
                lemma_map_insert_value(s1.core_states, core, os::CoreState::UnmapWaiting { ult_id, vaddr });
                assert(s2.inflight_mapunmap_vaddr() =~= s1.inflight_mapunmap_vaddr().insert(vaddr));
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert(pte is Some);
                assert(s2.interp(c).mappings == s1.interp(c).mappings.remove(vaddr));

                extra_mappings_preserved_effective_mapping_removed(c, s1, s2, core);
                assert(hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            }
        }
    } else {
        assert(pte is Some);
        if s1.effective_mappings().contains_key(vaddr) {
            assert(s1.effective_mappings()[vaddr] != s1.interp_pt_mem()[vaddr]);
            assert(s1.inflight_protect_params().contains_key(vaddr));
            let prot_core = s1.choose_inflight_protect_vaddr_core(vaddr);
            assert(s1.is_inflight_protect_vaddr_core(vaddr, prot_core));
            let ult_id = s1.core_states[prot_core].ult_id();
            assert(s1.interp_thread_state(c).contains_key(ult_id));
            assert(s1.interp_thread_state(c).values().contains(s1.interp_thread_state(c)[ult_id]));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), vaddr, 0));
        } else {
            assert(s1.inflight_mapunmap_vaddr().contains(vaddr));
            let mapunmap_core = s1.inflight_mapunmap_vaddr_choose_core(vaddr);
            let ult_id = s1.core_states[mapunmap_core].ult_id();
            assert(s1.interp_thread_state(c).contains_key(ult_id));
            assert(s1.interp_thread_state(c).values().contains(s1.interp_thread_state(c)[ult_id]));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), vaddr, 0));
        }
        assert(!hlspec::step_Unmap_sound(hl_s1, vaddr, 0));
    }
}

proof fn step_ProtectStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_ProtectStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_ProtectStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    //label
    let vaddr = lbl->ProtectStart_vaddr;
    let flags = lbl->ProtectStart_flags;
    let ult_id = lbl->ProtectStart_thread_id;

    //interpretation
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let pte = if s1.interp_pt_mem().contains_key(vaddr) { Some(s1.interp_pt_mem()[vaddr]) } else { None };
    let hl_pte = if hl_s1.mappings.contains_key(vaddr) { Some(hl_s1.mappings[vaddr]) } else { None };

    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };

    lemma_protect_soundness_equality(c, s1, vaddr, pte_size);

    assert(s1.inflight_mapunmap_vaddr() =~= s2.inflight_mapunmap_vaddr()) by {
        assert forall|va| s1.inflight_mapunmap_vaddr().contains(va) implies s2.inflight_mapunmap_vaddr().contains(va) by {
            let core2 = s1.inflight_mapunmap_vaddr_choose_core(va);
            assert(s2.core_states.contains_key(core2));
        }
    };
    assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());

    if pte == hl_pte {
        if hlspec::step_Protect_sound(hl_s1, vaddr, pte_size) {
            assert(hl_s1.sound == hl_s2.sound);
            assert(c.valid_core(c.ult2core[ult_id]));
            assert(hl_s2.thread_state =~= hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Protect { vaddr, flags, pte }));
            if pte is None {
                assert(!s1.interp_pt_mem().contains_key(vaddr));
                assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                    <==> s2.is_inflight_protect_vaddr_core(va, core));
                assert(s2.effective_mappings() =~= s1.effective_mappings());
                extra_mappings_preserved(c, s1, s2);
                assert(hl_s1.mappings =~= hl_s1.mappings.remove(vaddr));
                assert(hlspec::step_ProtectStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            } else {
                let new_pte = PTE { frame: pte->Some_0.frame, flags };
                assert(s2.effective_mappings() =~= s1.effective_mappings().insert(vaddr, new_pte)) by {
                    assert(forall|va, core| va != vaddr ==>
                        (s1.is_inflight_protect_vaddr_core(va, core) <==> s2.is_inflight_protect_vaddr_core(va, core)));
                    assert forall|core2| !s1.is_inflight_protect_vaddr_core(vaddr, core2) by {
                        assert_by_contradiction!(!s1.is_inflight_protect_vaddr_core(vaddr, core2), {
                            assert(core != core2);
                            assert(s1.core_states.values().contains(s1.core_states[core2]));
                            assert(overlap(os::inflight_vmem_region(s1.interp_pt_mem(), s1.core_states[core2]),
                                MemRegion { base: vaddr, size: pte_size }));
                            assert(os::candidate_mapping_overlaps_inflight_vmem(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte_size));
                        });
                    };
                    assert(s2.is_inflight_protect_vaddr_core(vaddr, core));

                    assert(s2.inflight_protect_params() =~= s1.inflight_protect_params().insert(vaddr, new_pte));
                };
                extra_mappings_preserved_effective_mapping_inserted_protect(c, s1, s2, core);
                assert(hlspec::step_ProtectStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            }
        }
    } else {
        assert(pte is Some);
        if s1.effective_mappings().contains_key(vaddr) {
            assert(s1.effective_mappings()[vaddr] != s1.interp_pt_mem()[vaddr]);
            assert(s1.inflight_protect_params().contains_key(vaddr));
            let prot_core = s1.choose_inflight_protect_vaddr_core(vaddr);
            assert(s1.is_inflight_protect_vaddr_core(vaddr, prot_core));
            let ult_id = s1.core_states[prot_core].ult_id();
            assert(s1.interp_thread_state(c).contains_key(ult_id));
            assert(s1.interp_thread_state(c).values().contains(s1.interp_thread_state(c)[ult_id]));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), vaddr, 0));
        } else {
            assert(s1.inflight_mapunmap_vaddr().contains(vaddr));
            let mapunmap_core = s1.inflight_mapunmap_vaddr_choose_core(vaddr);
            let ult_id = s1.core_states[mapunmap_core].ult_id();
            assert(s1.interp_thread_state(c).contains_key(ult_id));
            assert(s1.interp_thread_state(c).values().contains(s1.interp_thread_state(c)[ult_id]));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), vaddr, 0));
        }
        assert(!hlspec::step_Unmap_sound(hl_s1, vaddr, 0));
    }
}

proof fn step_ProtectEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_ProtectEnd(c, s1, s2, core, lbl),
    ensures
        s1.core_states[core] is ProtectOpDone || s1.core_states[core] is ProtectShootdownWaiting,
        hlspec::step_ProtectEnd(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    match s1.core_states[core] {
        os::CoreState::ProtectShootdownWaiting { ult_id, result, vaddr, .. }
        | os::CoreState::ProtectOpDone { result, ult_id, vaddr, .. } => {
            assert(hl_s2.thread_state === hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Idle));
            // assert(!s1.interp_pt_mem().contains_key(vaddr));
            // assert(!s2.interp_pt_mem().contains_key(vaddr));
            // lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
            // lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
            //assert(s1.inflight_unmap_vaddr().subset_of(s2.inflight_unmap_vaddr()));
            assume(s2.inflight_mapunmap_vaddr() =~= s1.inflight_mapunmap_vaddr());

            // XXX: Not enough info here: inflight_protect_core_get_pte is only for successful but
            // in this case we're also proving for unsuccessful, in which case inflight stuff is
            // unchanged
            assume(s1.interp_pt_mem().contains_key(vaddr));
            assert(s1.is_inflight_protect_vaddr_core(vaddr, core));
            assert(!s2.is_inflight_protect_vaddr_core(vaddr, core));

            assert forall|core2| core2 != core implies !s1.is_inflight_protect_vaddr_core(vaddr, core2) by {
            };
            assert_by_contradiction!(!s2.is_inflight_protect_vaddr(vaddr), {
                let core2 = s2.choose_inflight_protect_vaddr_core(vaddr);
                assert(s1.is_inflight_protect_vaddr_core(vaddr, core2));
            });
            assert(s2.inflight_protect_params() =~= s1.inflight_protect_params().remove(vaddr)) by {
                assert(forall|va, core2| va != vaddr ==> (s2.is_inflight_protect_vaddr_core(va, core2)
                    <==> s1.is_inflight_protect_vaddr_core(va, core2)));
            };
            // XXX: no overlap with mapunmap
            assume(s1.effective_mappings().contains_key(vaddr));
            assert(s2.effective_mappings().contains_key(vaddr));
            assume(s1.inflight_protect_core_get_pte(core) == s1.interp_pt_mem()[vaddr]);
            assert(s1.inflight_protect_params()[vaddr] == s1.interp_pt_mem()[vaddr]);
            assert(s1.effective_mappings()[vaddr] == s1.interp_pt_mem()[vaddr]);
            assert(s2.effective_mappings() =~= s1.effective_mappings());

            // // XXX: needs tlb inv
            // assume(hl_s2.mappings === hl_s1.mappings);

            extra_mappings_preserved(c, s2, s1);
            assert(hl_s2.mem == hl_s1.mem);
            // relevant_mem_preserved(c, s2, s1);

            assert(hlspec::step_ProtectEnd(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        _ => {
            assert(false);
        },
    };
}


proof fn step_UnmapOpChange_refines(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapOpChange(c, s1, s2, core, paddr, value, lbl),
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    to_rl1::next_refines(s1.mmu, s2.mmu, c.common, mmu::Lbl::Write(core, paddr, value));
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    assert(s1.core_states[core] is UnmapExecuting);
    let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;

    assert(hl_s1.thread_state.dom() === hl_s2.thread_state.dom());
    assert forall|key| #[trigger] hl_s1.thread_state.contains_key(key)
        implies hl_s1.thread_state[key] == hl_s2.thread_state[key]
    by {
        assert(c.valid_ult(key));
        assert(hl_s2.thread_state.contains_key(key));
        let core_of_key = c.ult2core[key];
        assert(c.valid_core(core));
        assert(s1.core_states[core].is_in_crit_sect());
        assert(c.valid_core(core_of_key));
        if s1.core_states[core_of_key].is_in_crit_sect() {
            assert(core_of_key === core);
        } else {
            assert(!(core_of_key === core));
            assert(!s1.core_states[core_of_key].is_in_crit_sect());
            assert(s1.core_states.index(core_of_key) == s2.core_states.index(core_of_key));
            assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            if s1.core_states[core_of_key] is UnmapWaiting {
                let vaddr_of_key = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                if vaddr_of_key == vaddr {
                    assert(overlap(
                        MemRegion {
                            base: s2.core_states[core_of_key].vaddr(),
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                        },
                    ));
                }
            } else if s1.core_states[core_of_key] is ProtectWaiting {
                let vaddr_of_key = s1.core_states[core_of_key]->ProtectWaiting_vaddr;
                if vaddr_of_key == vaddr {
                    assert(overlap(
                        MemRegion {
                            base: s2.core_states[core_of_key].vaddr(),
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                        },
                    ));
                }
            }
        }
    }
    assert(hl_s1.thread_state =~= hl_s2.thread_state);
    assert(s1.interp_pt_mem().remove(vaddr) =~= s2.interp_pt_mem());
    if s1.interp_pt_mem().contains_key(vaddr) {
        assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
            assert forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                implies s2.is_inflight_protect_vaddr_core(va, core)
            by {
                // XXX: easy, inflight protect and unmap don't overlap, so this mapping can't
                // have been removed by the UnmapOpChange step
                // (do we know s2.sound here?)
                assume(s2.interp_pt_mem().contains_key(va));
            };
            assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                <==> s2.is_inflight_protect_vaddr_core(va, core));
        };
        assert(s1.core_states.contains_key(core));
        assert(s1.inflight_mapunmap_vaddr().contains(vaddr));
        assert forall|ids|
            s1.inflight_mapunmap_vaddr().contains(ids)
            implies #[trigger] s2.inflight_mapunmap_vaddr().insert(vaddr).contains(ids) by {
            if s1.inflight_mapunmap_vaddr().contains(ids) {
                if ids === vaddr {
                } else {
                    assert(s1.interp_pt_mem().contains_key(ids));
                    assert(s2.interp_pt_mem().contains_key(ids));
                    let critical_core = choose|cr|
                        s1.core_states.contains_key(cr) && match s1.core_states[cr] {
                            os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. }
                            |os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === ids
                            },
                            _ => false,
                        };
                    assert(critical_core != core);
                    assert(s2.core_states.contains_key(critical_core));
                }
            }
        }
        assert(s1.inflight_mapunmap_vaddr() =~= s2.inflight_mapunmap_vaddr().insert(vaddr));

    } else {
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert forall|ids| s1.inflight_mapunmap_vaddr().contains(ids) implies s2.inflight_mapunmap_vaddr().contains(ids) by {
            if s1.inflight_mapunmap_vaddr().contains(ids) {
                assert(!(ids === vaddr));
                assert(s1.interp_pt_mem().contains_key(ids));
                assert(s2.interp_pt_mem().contains_key(ids));
                let unmap_core = choose|cr|
                    s1.core_states.contains_key(cr) && match s1.core_states[cr] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === ids
                        },
                        _ => false,
                    };
                assert(unmap_core != core);
                assert(s2.core_states.contains_key(unmap_core));
            }
        }
        assert(s1.inflight_mapunmap_vaddr() =~= s2.inflight_mapunmap_vaddr());
    }
    assert(s1.effective_mappings() =~= s2.effective_mappings());

    let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
    extra_mappings_inserted(c, s1, s2, core, vaddr, ult_id);
    assert(s1.applied_mappings() =~= s2.applied_mappings());
}

proof fn step_UnmapEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapEnd(c, s1, s2, core, lbl),
    ensures
        s1.core_states[core] is UnmapOpDone || s1.core_states[core] is UnmapShootdownWaiting,
        hlspec::step_UnmapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    match s1.core_states[core] {
        os::CoreState::UnmapShootdownWaiting { ult_id, result, vaddr, .. }
        | os::CoreState::UnmapOpDone { result, ult_id, vaddr, .. } => {
            assert(hl_c.valid_thread(ult_id));
            assert(hl_s2.sound == hl_s1.sound);
            assert(hl_s2.thread_state === hl_s1.thread_state.insert(
                ult_id,
                hlspec::ThreadState::Idle,
            ));
            assert(!s1.interp_pt_mem().contains_key(vaddr));
            assert(!s2.interp_pt_mem().contains_key(vaddr));
            lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
            lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
            //assert(s1.inflight_unmap_vaddr().subset_of(s2.inflight_unmap_vaddr()));
            assert(s1.inflight_mapunmap_vaddr() =~= s1.inflight_unmap_vaddr());
            assert(s2.inflight_mapunmap_vaddr() =~= s2.inflight_unmap_vaddr());

            assert(s1.inflight_protect_params() =~= s2.inflight_protect_params()) by {
                assert(forall|va, core| s1.is_inflight_protect_vaddr_core(va, core)
                    <==> s2.is_inflight_protect_vaddr_core(va, core));
            };
            assert forall|key| s2.effective_mappings().contains_key(key)
                implies s1.effective_mappings().contains_key(key)
            by {
                assert(s2.interp_pt_mem().contains_key(key));
                assert(s1.interp_pt_mem().contains_key(key));
                if key == vaddr {
                    assert(false);
                } else {
                    if s1.inflight_mapunmap_vaddr().contains(key) {
                        let threadstate = choose|thread_state| {
                                &&& s1.interp_thread_state(c).values().contains(thread_state)
                                &&& s1.interp_pt_mem().contains_key(key)
                                &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                                &&& vaddr === key
                            };
                        let ult_id2 = choose|id|
                            #![auto] s1.interp_thread_state(c).contains_key(id)
                            && s1.interp_thread_state(c)[id] == threadstate;
                        assert(ult_id2 != ult_id);
                        assert(s2.interp_thread_state(c).values().contains(threadstate));
                    }
                }
            }

            assert(hl_s2.mappings === hl_s1.mappings);

            extra_mappings_submap(c, s2, s1, core);
            relevant_mem_preserved(c, s2, s1);

            assert(hlspec::step_UnmapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        _ => {
            assert(false);
        },
    };
}

} // verus!
