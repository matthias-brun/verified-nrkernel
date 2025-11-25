use vstd::prelude::*;


use vstd::map::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ aligned, bit, bitmask_inc };
use crate::spec_t::mmu::translation::{ MASK_NEG_PROT_FLAGS, MASK_NEG_DIRTY_ACCESS };


verus! {

pub proof fn lemma_bits_prot()
    ensures
        forall|v1: usize, v2: usize, b: usize|
            ((v1 & MASK_NEG_PROT_FLAGS) == #[trigger] (v2 & MASK_NEG_PROT_FLAGS))
                && b < 64 && b != 1 && b != 2 && b != 63
                ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b),
        forall|v1: usize, v2: usize, b1: usize, b2: usize|
            (#[trigger] (v1 & MASK_NEG_PROT_FLAGS) == #[trigger] (v2 & MASK_NEG_PROT_FLAGS))
                && 2 < b1 <= b2 < 63
                // The line below is just bitmask_inc!(b1, b2) but we can't trigger on that directly
                // (due to arith/non-arith mixing rules).
                ==> (v1 & ((!(!0usize << #[trigger] (((b2+1usize)-b1) as usize))) << b1))
                    == v2 & bitmask_inc!(b1,b2),
        forall|v1: usize, v2: usize, mw: usize| #![auto]
            v1 & MASK_NEG_PROT_FLAGS == v2 & MASK_NEG_PROT_FLAGS && 32 <= mw <= 52
            ==> v1 & bitmask_inc!(mw, 51) == v2 & bitmask_inc!(mw, 51),
{
        assert(forall|v1: usize, v2: usize, b: usize|
            ((v1 & MASK_NEG_PROT_FLAGS) == #[trigger] (v2 & MASK_NEG_PROT_FLAGS))
                && b < 64 && b != 1 && b != 2 && b != 63
                ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b)) by (bit_vector);
        assert(forall|v1: usize, v2: usize, b1: usize, b2: usize|
            (#[trigger] (v1 & MASK_NEG_PROT_FLAGS) == #[trigger] (v2 & MASK_NEG_PROT_FLAGS))
                && 2 < b1 <= b2 < 63
                // The line below is just bitmask_inc!(b1, b2) but we can't trigger on that directly
                // (due to arith/non-arith mixing rules).
                ==> (v1 & ((!(!0usize << #[trigger] (((b2+1usize)-b1) as usize))) << b1))
                    == v2 & bitmask_inc!(b1,b2)) by (bit_vector);
        assert(forall|v1: usize, v2: usize, mw: usize| #![auto]
            v1 & MASK_NEG_PROT_FLAGS == v2 & MASK_NEG_PROT_FLAGS && 32 <= mw <= 52
            ==> v1 & bitmask_inc!(mw, 51) == v2 & bitmask_inc!(mw, 51)) by (bit_vector);
}

pub proof fn lemma_bits_misc()
    ensures
        bit!(0usize) == 1,
        forall|v: usize| v & bit!(0) == #[trigger] (v & MASK_NEG_DIRTY_ACCESS & bit!(0)),
        forall|v1: usize, v2: usize| #![auto]
            (v2 & 1) != (v1 & 1) ==> v2 & MASK_NEG_PROT_FLAGS != v1 & MASK_NEG_PROT_FLAGS,
{
        assert(bit!(0usize) == 1) by (bit_vector);
        assert(forall|v: usize| v & bit!(0) == #[trigger] (v & MASK_NEG_DIRTY_ACCESS & bit!(0))) by (bit_vector);
        assert(forall|v1: usize, v2: usize| #![auto] (v2 & 1) != (v1 & 1) ==>
            v2 & !(bit!(63usize) | bit!(2usize) | bit!(1usize)) !=
            v1 & !(bit!(63usize) | bit!(2usize) | bit!(1usize))) by (bit_vector);
}


pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), c > 0
    ensures aligned(a + b, c)
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int, b as int, c as int);
    assert(0nat % c == (a + b) % c);
}

pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) by (nonlinear_arith)
    requires aligned(a, b * c), b > 0, c > 0
    ensures aligned(a, b)
{
    broadcast use vstd::arithmetic::div_mod::lemma_mod_mod, vstd::arithmetic::div_mod::lemma_mod_breakdown;
    assert((a % (b * c)) % b == 0);
}

pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), a <= b, c > 0
    ensures aligned((b - a) as nat, c)
{
    let a = a as int; let b = b as int; let c = c as int;
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(b, a, c);
    assert(((b % c) - (a % c)) % c == (b - a) % c);
    assert(0int % c == (b - a) % c);
}

pub proof fn leq_add_aligned_less(a: nat, b: nat, c: nat) by (nonlinear_arith)
    requires 0 < b, a < c, aligned(a, b), aligned(c, b),
    ensures a + b <= c,
{
    assert(a == b * (a / b) + a % b);
    assert(c == b * (c / b) + c % b);
}

pub proof fn aligned_transitive_auto()
    ensures forall|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) ==> aligned(a, c),
{
    assert forall|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) implies aligned(a, c) by {
        aligned_transitive(a, b, c);
    }
}

pub proof fn lemma_subset_is_finite<A>(
    a: Set<A>,
    b: Set<A>,
)
    requires 
        a.finite(),
        b.subset_of(a),
    ensures
        b.finite(),
{   let c = a.difference(b);   
    assert (a.difference(c).finite());
    assert (a.difference(c) === b);
}

pub proof fn lemma_set_of_first_n_nat_is_finite( n: nat, )
    requires
    ensures Set::new(|i: nat| i < n).finite()
    decreases n
{   
    let b = Set::new(|i: nat| i < n);
    if (n == 0) {    
        assert(Set::new(|i: nat| i < 0) === Set::empty());
        assert(Set::new(|i: nat| i < 0).finite());
    } else {
        lemma_set_of_first_n_nat_is_finite((n - 1) as nat);
        let c = Set::new(|i: nat| i < n - 1).insert((n - 1) as nat);
        assert(c.finite());
        assert(c === b);
        assert(b.finite());
    }
}

pub proof fn lemma_aligned_iff_eq_mul_div(a: nat, b: nat)
    requires b > 0
    ensures aligned(a, b) <==> a == b * (a / b)
{
    assert(a % b == 0 ==> a == b * (a / b)) by (nonlinear_arith)
        requires b > 0;
    assert(a == b * (a / b) ==> a % b == 0) by (nonlinear_arith)
        requires b > 0;
}

pub proof fn aligned_transitive(a: nat, b: nat, c: nat)
    requires
        0 < b,
        0 < c,
        aligned(a, b),
        aligned(b, c),
    ensures aligned(a, c)
{
    lemma_aligned_iff_eq_mul_div(a, b);
    lemma_aligned_iff_eq_mul_div(b, c);
    lemma_aligned_iff_eq_mul_div(a, c);
    let i = a / b; let j = b / c;
    assert((c * j) * i == c * (j * i)) by (nonlinear_arith);
    assert(a / c == j * i) by (nonlinear_arith)
        requires 0 < c, a == c * (j * i);
}

#[verifier(nonlinear)]
pub proof fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[verifier(nonlinear)]
pub proof fn aligned_zero()
    ensures
        forall|a:nat| a != 0 ==> aligned(0, a)
{ }

#[verifier(nonlinear)]
pub proof fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[verifier(nonlinear)]
pub proof fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}

#[verifier(nonlinear)]
pub proof fn div_mul_cancel(a: nat, b: nat) {
    requires([
             aligned(a, b),
             b != 0
    ]);
    ensures(a / b * b == a);
}

#[verifier(nonlinear)]
pub proof fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono_both(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b <= d,
    ensures
        // Including `0 <=` here because it's used in a place where this is part of an overflow VC
        // and non-nonlinear z3 can't even deal with that.
        0 <= a * b <= c * d
{ }

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both1(a: nat, b: nat, c: nat, d: nat)
    requires
        a < c,
        b <= d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d
{ }

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both2(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b < d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d
{ }


pub proof fn assert_maps_equal_contains_pair<K,V>(m1: Map<K,V>, m2: Map<K,V>)
    requires
        forall|k:K,v:V| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k:K,v:V| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2
{
    assert forall|k|
        m1.dom().contains(k)
        implies m2.dom().contains(k) by
    { assert(m2.contains_pair(k, m1.index(k))); };
    assert forall|k|
        m2.dom().contains(k)
        implies m1.dom().contains(k) by
    { assert(m1.contains_pair(k, m2.index(k))); };
    assert forall|k|
        m1.dom().contains(k) && m2.dom().contains(k)
        implies #[trigger] m2.index(k) === #[trigger] m1.index(k) by
    {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    };
    assert_maps_equal!(m1, m2);
}

// FIXME: Something like these functions should probably be added to vstd. One problem with that:
// May want exec versions of the functions but can't give them the same name.
pub open spec(checked) fn result_map_ok<A,B,C>(res: Result<A,B>, f: spec_fn(A) -> C) -> Result<C,B> {
    match res {
        Ok(a)  => Ok(f(a)),
        Err(b) => Err(b),
    }
}

pub open spec(checked) fn result_map<A,B>(res: Result<A,A>, f: spec_fn(A) -> B) -> Result<B,B> {
    match res {
        Ok(a)  => Ok(f(a)),
        Err(a) => Err(f(a)),
    }
}

}
