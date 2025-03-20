use vstd::prelude::*;

use crate::spec_t::mmu::translation::{ PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::spec_t::mmu::defs::{ PTE, bitmask_inc, WORD_SIZE, bit };
use crate::spec_t::mmu::{ Walk, WalkResult };

verus! {

// TODO: memory size
pub struct PTMem {
    pub mem: Map<usize, usize>,
    pub pml4: usize,
}

impl PTMem {
    pub open spec fn write(self, addr: usize, value: usize) -> PTMem {
        PTMem {
            mem: self.mem.insert(addr, value),
            pml4: self.pml4,
        }
    }

    pub open spec fn read(self, addr: usize) -> usize {
        self.mem[addr]
    }

    /// Sequentially apply a sequence of writes. (Used to apply a whole store buffer.)
    pub open spec fn write_seq(self, writes: Seq<(usize, usize)>) -> Self {
        writes.fold_left(self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1))
    }

    // We reason about page table writes as non-negative and non-positive.
    // Non-positivity/non-negativity is easy to determine based on the present bit of the old and
    // new value. On the other hand, determining accurately when a write is positive or negative is
    // very hard because it depends on the current page table in memory and also on the inflight
    // page table walks. E.g. in-memory a certain memory location may not be reachable anymore but
    // there may still be inflight walks which will read that location. Additionally, whether or
    // not a value in memory decodes to a valid or invalid entry depends on how it's interpreted.
    // E.g. a layer 3 page mapping has different reserved bits than a layer 0 directory mapping.

    /// A present bit of 0 guarantees that this is not currently a valid entry.
    /// I.e. this write can be:
    /// - Invalid -> Valid
    /// - Invalid -> Invalid
    ///
    /// The second conjunct guarantees that we write at most once to each address.
    pub open spec fn is_nonneg_write(self, addr: usize, value: usize) -> bool {
        &&& self.read(addr) & 1 == 0
        &&& value & 1 == 1
    }

    /// Writing a present bit of 1 guarantees that this is not currently a valid entry.
    /// I.e. this write can be:
    /// - Valid -> Invalid
    /// - Invalid -> Invalid
    ///
    /// The second conjunct guarantees that we write at most once to each address.
    pub open spec fn is_nonpos_write(self, addr: usize, value: usize) -> bool {
        &&& self.read(addr) & 1 == 1
        &&& value & 1 == 0
    }

    pub open spec fn pt_walk(self, vaddr: usize) -> Walk {
        let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
        let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
        let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
        let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
        let l0_addr = add(self.pml4, l0_idx);
        let l0e = PDE { entry: self.read(l0_addr), layer: Ghost(0) };
        match l0e@ {
            GPDE::Directory { addr: l1_daddr, .. } => {
                let l1_addr = add(l1_daddr, l1_idx);
                let l1e = PDE { entry: self.read(l1_addr), layer: Ghost(1) };
                match l1e@ {
                    GPDE::Directory { addr: l2_daddr, .. } => {
                        let l2_addr = add(l2_daddr, l2_idx);
                        let l2e = PDE { entry: self.read(l2_addr), layer: Ghost(2) };
                        match l2e@ {
                            GPDE::Directory { addr: l3_daddr, .. } => {
                                let l3_addr = add(l3_daddr, l3_idx);
                                let l3e = PDE { entry: self.read(l3_addr), layer: Ghost(3) };
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)],
                                    complete: true,
                                }
                            },
                            _ => {
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)],
                                    complete: true,
                                }
                            },
                        }
                    },
                    _ => {
                        Walk { vaddr, path: seq![(l0_addr, l0e@), (l1_addr, l1e@)], complete: true }
                    },
                }
            },
            _ => {
                Walk { vaddr, path: seq![(l0_addr, l0e@)], complete: true }
            },
        }
    }

    //pub open spec fn pt_walk(self, vaddr: usize) -> Walk {
    //    let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
    //    let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
    //    let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
    //    let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
    //    let l0_addr = add(self.pml4, l0_idx);
    //    let l0e = PDE { entry: self.read(l0_addr), layer: Ghost(0) };
    //    let path = 
    //        seq![(l0_addr, l0e@)].add(
    //            match l0e@ {
    //                GPDE::Directory { addr: l1_daddr, .. } => {
    //                    let l1_addr = add(l1_daddr, l1_idx);
    //                    let l1e = PDE { entry: self.read(l1_addr), layer: Ghost(1) };
    //                    seq![(l1_addr, l1e@)].add(
    //                        match l1e@ {
    //                            GPDE::Directory { addr: l2_daddr, .. } => {
    //                                let l2_addr = add(l2_daddr, l2_idx);
    //                                let l2e = PDE { entry: self.read(l2_addr), layer: Ghost(2) };
    //                                seq![(l2_addr, l2e@)].add(
    //                                    match l2e@ {
    //                                        GPDE::Directory { addr: l3_daddr, .. } => {
    //                                            let l3_addr = add(l3_daddr, l3_idx);
    //                                            let l3e = PDE { entry: self.read(l3_addr), layer: Ghost(3) };
    //                                            seq![(l3_addr, l3e@)]
    //                                        },
    //                                        _ => seq![],
    //                                    })
    //                            },
    //                            _ => seq![],
    //                        })
    //                },
    //                _ => seq![],
    //            });
    //    Walk { vaddr, path, complete: true }
    //}

    pub broadcast proof fn lemma_pt_walk(mem: PTMem, va: usize)
        ensures #![trigger mem.pt_walk(va)]
            mem.pt_walk(va).complete,
            0 < mem.pt_walk(va).path.len() <= 4,
            forall|i| 0 <= i < mem.pt_walk(va).path.len() - 1
                ==> #[trigger] mem.pt_walk(va).path[i].1 is Directory
                            && mem.read(mem.pt_walk(va).path[i].0) & 1 == 1,
            !(mem.pt_walk(va).path.last().1 is Directory),
            forall|i| 0 <= i < mem.pt_walk(va).path.len()
                ==> (#[trigger] mem.pt_walk(va).path[i].1)
                        == (PDE {
                            entry: mem.read(mem.pt_walk(va).path[i].0),
                            layer: Ghost(i as nat),
                        }@),
            mem.pt_walk(va).result() is Valid ==> mem.read(mem.pt_walk(va).path.last().0) & 1 == 1,
    {
        assert(bit!(0usize) == 1) by (bit_vector);
    }

    pub proof fn lemma_pt_walk_agrees_in_frame(self, vbase: usize, vaddr: usize)
        requires
            self.is_base_pt_walk(vbase),
            vbase <= vaddr < vbase + self.pt_walk(vbase).result()->pte.frame.size,
        ensures
            self.pt_walk(vaddr).result() is Valid
    {
        assert(sub(vbase, vbase % (4096) as usize) == vbase
            && vbase <= vaddr < vbase + 4096
            ==> l0_bits!(vaddr) == l0_bits!(vbase)
             && l1_bits!(vaddr) == l1_bits!(vbase)
             && l2_bits!(vaddr) == l2_bits!(vbase)
             && l3_bits!(vaddr) == l3_bits!(vbase)
        ) by(bit_vector);
        assert(sub(vbase, vbase % (512 * 4096) as usize) == vbase
            && vbase <= vaddr < vbase + 512 * 4096
            ==> l0_bits!(vaddr) == l0_bits!(vbase)
             && l1_bits!(vaddr) == l1_bits!(vbase)
             && l2_bits!(vaddr) == l2_bits!(vbase)
        ) by(bit_vector);
        assert(sub(vbase, vbase % (512 * (512 * 4096)) as usize) == vbase
            && vbase <= vaddr < vbase + 512 * (512 * 4096)
            ==> l0_bits!(vaddr) == l0_bits!(vbase)
             && l1_bits!(vaddr) == l1_bits!(vbase)
        ) by(bit_vector);
        /*assert(sub(vbase, vbase % (512 * (512 * (512 * 4096))) as usize) == vbase
            && vbase <= vaddr < vbase + 512 * (512 * (512 * 4096))
            ==> l0_bits!(vaddr) == l0_bits!(vbase)
        ) by(bit_vector);*/

        /*let path = self.pt_walk(vbase).path;
        if path.last().1 is Page {
            if path.len() == 2 {
                assert(self.pt_walk(vbase).result()->pte.frame.size == L1_ENTRY_SIZE);
                assert(self.pt_walk(vbase).result()->pte.frame.size == 512 * (512 * 4096));
                assert(crate::spec_t::mmu::defs::align_to_usize(vbase, (512 * (512 * 4096)) as usize) == vbase);
                //assert(vbase % (512 * (512 * 4096)) as usize == 0);
                assert(l0_bits!(vaddr) == l0_bits!(vbase));
                assert(self.pt_walk(vaddr).path.last().1 is Page);
            } else if path.len() == 3 {
                assert(self.pt_walk(vaddr).path.last().1 is Page);
            } else if path.len() == 4 {
                assert(self.pt_walk(vbase).result()->pte.frame.size == L3_ENTRY_SIZE);

                assert(l0_bits!(vaddr) == l0_bits!(vbase));

                assert(self.pt_walk(vaddr).path.len() == 4);
                assert(self.pt_walk(vaddr).path.last().1 is Page);
            } else {
                assert(false);
            }
        } else {
            assert(false);
        }*/
    }

    pub open spec fn is_base_pt_walk(self, vaddr: usize) -> bool {
        &&& self.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }
        &&& vbase == vaddr
    }

    /// Making this opaque so `pt_walk` isn't immediately visible in all the OS state machine
    /// proofs.
    #[verifier(opaque)]
    pub open spec fn view(self) -> Map<usize,PTE> {
        Map::new(
            |va| self.is_base_pt_walk(va),
            |va| self.pt_walk(va).result()->pte
        )
    }

    pub broadcast proof fn lemma_write_seq_idle(self, writes: Seq<(usize, usize)>, addr: usize)
        requires forall|i| 0 <= i < writes.len() ==> (#[trigger] writes[i]).0 != addr
        ensures #[trigger] self.write_seq(writes).read(addr) == self.read(addr)
        decreases writes.len()
    {
        if writes.len() == 0 {
        } else {
            broadcast use PTMem::lemma_write_seq;
            self.lemma_write_seq_idle(writes.drop_last(), addr)
        }
    }

    pub proof fn lemma_write_seq_push(self, writes: Seq<(usize, usize)>, addr: usize, value: usize)
        ensures
            self.write_seq(writes.push((addr, value)))
                == (PTMem {
                    pml4: self.pml4,
                    mem: self.write_seq(writes).mem.insert(addr, value),
                }),
        decreases writes.len()
    {
        broadcast use PTMem::lemma_write_seq;
        lemma_fold_left_push(writes, (addr, value), self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1));
    }

    pub broadcast proof fn lemma_write_seq_first(m: PTMem, writes: Seq<(usize, usize)>)
        requires writes.len() > 0,
        ensures m.write_seq(writes) == #[trigger] m.write(writes[0].0, writes[0].1).write_seq(writes.drop_first())
    {
        let f = |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1);
        let new_m = m.write(writes[0].0, writes[0].1);
        writes.lemma_fold_left_alt(m, f);
        writes.subrange(1, writes.len() as int).lemma_fold_left_alt(new_m, f);
    }

    pub broadcast proof fn lemma_write_seq(self, writes: Seq<(usize, usize)>)
        ensures #![trigger self.write_seq(writes)]
            self.write_seq(writes).pml4 == self.pml4,
            self.mem.dom().subset_of(self.write_seq(writes).mem.dom()),
        decreases writes.len()
    {
        if writes.len() == 0 {
        } else {
            self.lemma_write_seq(writes.drop_last())
        }
    }

    pub proof fn lemma_write_seq_read(self, writes: Seq<(usize, usize)>, i: int)
        requires
            0 <= i < writes.len(),
            forall|j| #![auto] 0 <= j < writes.len() && writes[j].0 == writes[i].0 ==> i == j,
        ensures
            self.write_seq(writes).mem[writes[i].0] == writes[i].1
        decreases writes.len()
    {
        if writes.len() == 0 {
        } else {
            if i == writes.len() - 1 {
            } else {
                self.lemma_write_seq_read(writes.drop_last(), i);
            }
        }
    }
}

proof fn lemma_fold_left_push<A,B>(s: Seq<A>, a: A, b: B, f: spec_fn(B, A) -> B)
    ensures s.push(a).fold_left(b, f) == f(s.fold_left(b, f), a)
{
    assert(s.push(a).drop_last() == s);
}

} // verus!
