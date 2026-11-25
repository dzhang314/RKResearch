module

public import RKCert.ReviewedNative.PrimitiveDyadicNodal
public import RKCert.ReviewedNative.DyadicFourShiftRows

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The final balanced mod-four family, uniformly rather than by 81 decisions -/

namespace RKResearch.Certified.DyadicFourShift

open Polynomial RKResearch.Certified.RationalPrimeCut
open scoped BigOperators Polynomial Classical

/-- Linearization in a square-zero ideal. Distinct marked factors never
contribute a second perturbation to the product. -/
theorem prod_add_pairmul_zero {ι R : Type*} [CommRing R]
    (S : Finset ι) (x : R) (δ : ι → R)
    (nil : ∀ i ∈ S, ∀ j ∈ S, δ i*δ j = 0) :
    (∏ i ∈ S, (x+δ i)) = x^S.card + (∑ i ∈ S, δ i)*x^(S.card-1) := by
  revert nil
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert i S hi ih =>
    intro nil
    have inner : ∀ a ∈ S, ∀ b ∈ S, δ a*δ b = 0 := fun a ha b hb =>
      nil a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, ih inner]
    by_cases he : S.card = 0
    · have hS := Finset.card_eq_zero.mp he
      subst S
      simp [add_comm]
    · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero he
      let v := ∑ j ∈ S, δ j
      have z : δ i * v = 0 := by
        dsimp only [v]
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun j hj =>
          nil i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
      rw [hn]
      change (x+δ i)*(x^(n+1)+v*x^n) = x^(n+1+1)+(δ i+v)*x^(n+1)
      calc
        _ = x*x^(n+1)+(δ i+v)*(x*x^n)+(δ i*v)*x^n := by
          rw [pow_succ' x n]
          ring
        _ = _ := by simp only [z, zero_mul, add_zero, pow_succ']

private theorem residue_four_even_lift (z : ZMod 4) (h : dyadicReduce4to2 z = 0) :
    ∃ u : ZMod 4, z = 2*u := by
  have hz : ((z.val : ℕ) : ZMod 2) = 0 := by
    simpa only [map_natCast] using
      (congrArg dyadicReduce4to2 (ZMod.natCast_zmod_val z)).trans h
  obtain ⟨u,hu⟩ := (ZMod.natCast_eq_zero_iff z.val 2).mp hz
  refine ⟨(u : ZMod 4),?_⟩
  calc
    _ = (z.val : ZMod 4) := (ZMod.natCast_zmod_val _).symm
    _ = _ := by rw [hu, Nat.cast_mul, Nat.cast_ofNat]

private theorem two_sq_zero_four : (2 : ZMod 4)*2 = 0 := by
  change ((2 : ℕ) : ZMod 4)*((2 : ℕ) : ZMod 4) = 0
  rw [← Nat.cast_mul]
  exact ZMod.natCast_self 4

private theorem residue_four_even_mul_zero {u v : ZMod 4}
    (hu : dyadicReduce4to2 u = 0) (hv : dyadicReduce4to2 v = 0) : u*v = 0 := by
  obtain ⟨i,hi⟩ := residue_four_even_lift u hu
  obtain ⟨j,hj⟩ := residue_four_even_lift v hv
  calc
    _ = ((2 : ZMod 4)*2)*(i*j) := by rw [hi,hj]; ring
    _ = _ := by rw [two_sq_zero_four,zero_mul]

private theorem residue_four_odd_square {u : ZMod 4}
    (h : dyadicReduce4to2 u = 1) : u*u = 1 := by
  have z : dyadicReduce4to2 (u-1) = 0 := by simp only [map_sub,map_one,h,sub_self]
  obtain ⟨v,hv⟩ := residue_four_even_lift (u-1) z
  have he : u=1+2*v := (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)
  calc
    _ = 1+((2 : ZMod 4)*2)*(v+v*v) := by rw [he]; ring
    _ = _ := by rw [two_sq_zero_four,zero_mul,add_zero]

private theorem equal_four_nat_residue (a b : ℕ) (h : a%4=b%4) :
    (a : ZMod 4) = (b : ZMod 4) := by
  rw [← ZMod.natCast_mod a 4, ← ZMod.natCast_mod b 4, h]

private theorem coeff_pattern_four (m n k : ℕ) (h : m ≤ k) :
    (((X : (ZMod 4)[X])^m*(X+1)^n).coeff k) = (n.choose (k-m) : ZMod 4) := by
  rw [coeff_X_pow_mul', if_pos h, coeff_X_add_one_pow]

/-- The balanced case is a single symbolic relation. Odd slope
units only scale the original coefficients and cannot remove it. -/
theorem dyadicBalanced_coeffs_ne_zero (T : Finset ℚ) (hm : T.card ≤ 16)
    (ht : dyadicDenCount T = 16) (hu : dyadicEvenCount T = 8) :
    ¬ (((integralRationalNodalHull T).coeff 12 : ZMod 4) = 0 ∧
      ((integralRationalNodalHull T).coeff 14 : ZMod 4) = 0) := by
  intro hbad
  have hcard : T.card = 16 := by
    have hle := dyadicDenCount_le_card T
    omega
  have hfilter : T.filter denOdd = T :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      change T.card ≤ dyadicDenCount T
      omega)
  have hd (r : ℚ) (hr : r ∈ T) : (r.den : ZMod 2) = 1 := by
    have hp : r ∈ T.filter denOdd := by rwa [hfilter]
    exact (zmodTwo_choices (r.den : ZMod 2)).resolve_left (Finset.mem_filter.mp hp).2
  let d : ℚ → ZMod 4 := fun r => (r.den : ZMod 4)
  let z : ℚ → ZMod 4 := fun r => d r * (-(r.num : ZMod 4))
  let U : ZMod 4 := ∏ r ∈ T, d r
  let S := T.filter numEven
  let O := T.filter fun r => ¬numEven r
  let e : ZMod 4 := ∑ r ∈ S, z r
  let o : ZMod 4 := ∑ r ∈ O, (z r-1)
  let Q : (ZMod 4)[X] := ∏ r ∈ T, (X+C (z r))
  have hs : S.card = 8 := hu
  have ho : O.card = 8 := by
    have h := Finset.card_filter_add_card_filter_not (s := T) numEven
    change S.card+O.card=T.card at h
    omega
  have dz (r : ℚ) (hr : r ∈ T) : d r*d r=1 := by
    apply residue_four_odd_square
    simpa only [d,map_natCast] using hd r hr
  have mz (r : ℚ) (hr : r ∈ T) : dyadicReduce4to2 (z r) = (r.num : ZMod 2) := by
    simp only [z,d,map_mul,map_natCast,map_neg,map_intCast,hd r hr,one_mul]
    rcases zmodTwo_choices (r.num : ZMod 2) with h | h <;> simp only [h,neg_zero,zmodTwo_neg_one]
  have me (r : ℚ) (hr : r ∈ S) : dyadicReduce4to2 (z r) = 0 := by
    exact (mz r (Finset.mem_filter.mp hr).1).trans (Finset.mem_filter.mp hr).2
  have mo (r : ℚ) (hr : r ∈ O) : dyadicReduce4to2 (z r-1) = 0 := by
    have h1 := (zmodTwo_choices (r.num : ZMod 2)).resolve_left (Finset.mem_filter.mp hr).2
    rw [map_sub, map_one, mz r (Finset.mem_filter.mp hr).1, h1, sub_self]
  have ez : dyadicReduce4to2 e = 0 := by
    rw [show e = ∑ r ∈ S,z r from rfl, map_sum]
    exact Finset.sum_eq_zero me
  have oz : dyadicReduce4to2 o = 0 := by
    rw [show o = ∑ r ∈ O,(z r-1) from rfl, map_sum]
    exact Finset.sum_eq_zero mo
  have Uunit : U*U=1 := by
    unfold U
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one dz
  have mP : (integralRationalNodalHull T).map (Int.castRingHom (ZMod 4)) = C U*Q := by
    simp only [integralRationalNodalHull, Polynomial.map_prod, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
      Int.cast_natCast, Int.cast_neg]
    change (∏ r ∈ T, (C (d r)*X+C (-(r.num : ZMod 4)))) = C U*Q
    calc
      _ = ∏ r ∈ T, C (d r)*(X+C (z r)) := by
        apply Finset.prod_congr rfl
        intro r hr
        rw [mul_add, ← map_mul]
        have same : d r*z r = -(r.num : ZMod 4) := by
          change d r * (d r * -(r.num : ZMod 4)) = -(r.num : ZMod 4)
          rw [← mul_assoc, dz r hr, one_mul]
        rw [same]
      _ = _ := by simp only [U,Q, Finset.prod_mul_distrib, map_prod]
  have eprod : (∏ r ∈ S, (X+C (z r) : (ZMod 4)[X])) = X^8+C e*X^7 := by
    have hh := prod_add_pairmul_zero S (X : (ZMod 4)[X]) (fun r => C (z r))
      (fun i hi j hj => by
        rw [← map_mul, residue_four_even_mul_zero (me i hi) (me j hj), map_zero])
    simpa only [hs, show (8 : ℕ)-1=7 by decide, e, map_sum] using hh
  have oprod : (∏ r ∈ O, (X+C (z r) : (ZMod 4)[X])) = (X+1)^8+C o*(X+1)^7 := by
    have hh := prod_add_pairmul_zero O (X+1 : (ZMod 4)[X]) (fun r => C (z r-1))
      (fun i hi j hj => by
        rw [← map_mul, residue_four_even_mul_zero (mo i hi) (mo j hj), map_zero])
    calc
      _ = ∏ r ∈ O, ((X+1 : (ZMod 4)[X])+C (z r-1)) := by
        apply Finset.prod_congr rfl
        intro r _
        rw [map_sub, map_one]
        ring
      _ = _ := by simpa only [ho, show (8 : ℕ)-1=7 by decide, o, map_sum] using hh
  have qForm : Q = X^8*(X+1)^8+C e*(X^7*(X+1)^8)+C o*(X^8*(X+1)^7) := by
    have zz : (C e : (ZMod 4)[X])*C o = 0 := by
      rw [← map_mul, residue_four_even_mul_zero ez oz, map_zero]
    calc
      _ = (X^8+C e*X^7)*((X+1)^8+C o*(X+1)^7) := by
        rw [← eprod, ← oprod]
        exact (Finset.prod_filter_mul_prod_filter_not T numEven (fun r => (X+C (z r)))).symm
      _ = X^8*(X+1)^8+C e*(X^7*(X+1)^8)+C o*(X^8*(X+1)^7)+
          (C e*C o)*(X^7*(X+1)^7) := by ring
      _ = _ := by rw [zz,zero_mul,add_zero]
  have q12 : Q.coeff 12 = 2+3*o := by
    rw [qForm, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_pattern_four 8 8 12 (by decide), coeff_pattern_four 7 8 12 (by decide),
      coeff_pattern_four 8 7 12 (by decide)]
    rw [show Nat.choose 8 (12-8)=70 by decide, show Nat.choose 8 (12-7)=56 by decide,
      show Nat.choose 7 (12-8)=35 by decide,
      equal_four_nat_residue 70 2 (by decide), equal_four_nat_residue 56 0 (by decide),
      equal_four_nat_residue 35 3 (by decide)] <;> simp only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero, mul_comm o]
  have q14 : Q.coeff 14 = 3*o := by
    rw [qForm, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      coeff_pattern_four 8 8 14 (by decide), coeff_pattern_four 7 8 14 (by decide),
      coeff_pattern_four 8 7 14 (by decide)]
    rw [show Nat.choose 8 (14-8)=28 by decide, show Nat.choose 8 (14-7)=8 by decide,
      show Nat.choose 7 (14-8)=7 by decide,
      equal_four_nat_residue 28 0 (by decide), equal_four_nat_residue 8 0 (by decide),
      equal_four_nat_residue 7 3 (by decide)] <;> simp only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero, zero_add, mul_comm o]
  have cancel (k : ℕ) (h : ((integralRationalNodalHull T).coeff k : ZMod 4)=0) :
      Q.coeff k = 0 := by
    have z : U*(Q.coeff k)=0 := by
      change (Int.castRingHom (ZMod 4)) ((integralRationalNodalHull T).coeff k) = 0 at h
      rw [← coeff_map, mP, coeff_C_mul] at h
      exact h
    calc
      _ = (U*U)*(Q.coeff k) := by rw [Uunit,one_mul]
      _ = U*(U*(Q.coeff k)) := by rw [mul_assoc]
      _ = _ := by rw [z,mul_zero]
  have d12 := cancel 12 hbad.1
  have d14 := cancel 14 hbad.2
  rw [q12, ← q14, d14, add_zero] at d12
  have v := congrArg ZMod.val d12
  change 2 = 0 at v
  omega

end RKResearch.Certified.DyadicFourShift
