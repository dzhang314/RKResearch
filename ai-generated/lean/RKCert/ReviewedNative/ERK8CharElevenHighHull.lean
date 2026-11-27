module

public import RKCert.ReviewedNative.ERK8CharElevenTailSupport

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The literal seven-off hull residue in characteristic eleven
The pure quadrature of its three-anchor vanishing polynomial and the
earned nonzero weight law determine the hull residue. The quotient
identities below are over the coefficient field even when the
exceptional quadratic does not split. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem quadratic_exact_degree : (exceptionalQuadratic : K[X]).natDegree=2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero exceptionalQuadratic_degree
  simp [exceptionalQuadratic,coeff_X_pow,coeff_X]

theorem low_quadratic_multiple_eq_zero {R : K[X]} (rd : R.natDegree≤1)
    (dvd : (exceptionalQuadratic : K[X])∣R) : R=0 := by
  by_contra h
  have e := Polynomial.natDegree_le_of_dvd dvd h
  rw [quadratic_exact_degree] at e
  omega

theorem coeff_last_barycentric (S : Finset K) (P : K[X]) (Pd : P.natDegree < S.card) :
    P.coeff (S.card-1) = ∑ x∈S, P.eval x/(nodalHull (S.erase x)).eval x := by
  have h : P.degree < (S.card : WithBot ℕ) :=
    P.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr Pd)
  have e := Lagrange.coeff_eq_sum (s:=S) (v:=id) (Set.injOn_id _) h
  simpa only [id_eq,nodalHull,eval_prod,eval_sub,eval_X,eval_C] using e

theorem natDegree_le_of_last_coeff_zero {P : K[X]} {k : ℕ}
    (d : P.natDegree≤k+1) (z : P.coeff (k+1)=0) : P.natDegree≤k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases e : n=k+1
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (d.trans_lt (by omega))

theorem polynomial_hull_of_test_zeros (S : Finset K) (P : K[X]) (hd : P.natDegree≤S.card)
    (h : ∀ x∈S, P.eval x=0) : ∃ a : K, P=C a*nodalHull S := by
  have dvd : nodalHull S ∣ P := by
    unfold nodalHull
    apply Finset.prod_dvd_of_coprime
    · intro x hx y hy ne
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
    · intro x hx
      exact dvd_iff_isRoot.mpr (h x hx)
  obtain ⟨R,he⟩ := dvd
  by_cases hR : R=0
  · exact ⟨0,by simp [he,hR]⟩
  have hdeg := natDegree_mul (monic_nodalHull S).ne_zero hR
  rw [←he,natDegree_nodalHull] at hdeg
  have hc : R=C (R.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  exact ⟨R.coeff 0,by rw [he,hc,mul_comm,coeff_C_zero]⟩

noncomputable def highAnchorHull : K[X] := X*(X-C 6)*(X-C 1)

theorem highAnchorHull_degree : (highAnchorHull : K[X]).natDegree≤3 := by
  unfold highAnchorHull
  exact natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (natDegree_X_sub_C_le _))
    (natDegree_X_sub_C_le _)

theorem highAnchorHull_zero {x : K} (hx : x∈({0,1,6} : Finset K)) :
    (highAnchorHull : K[X]).eval x=0 := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with h|h|h <;> simp [highAnchorHull,h]

theorem paid_anchor_probe_zero (ho : HasOrder 8 A b) (p : (11:K)=0) :
    probe A b 0 (evalNodes A highAnchorHull)=0 := by
  have eq := probe_evalNodes ho (highAnchorHull : K[X]) 0 (by
    have d := highAnchorHull_degree (K:=K)
    omega)
  rw [pow_zero,one_mul] at eq
  have pol : (highAnchorHull : K[X])=monomial 1 6 + monomial 2 (-7)+monomial 3 1 := by
    simp only [highAnchorHull,←C_mul_X_pow_eq_monomial,pow_one,map_ofNat,map_neg,map_one,one_mul]
    ring
  have exactPrimitive : (primitive (highAnchorHull : K[X])).eval 1=(6:K)/2+(-7)/3+1/4 := by
    rw [pol]
    simp only [map_add,primitive_monomial,eval_add,eval_monomial,one_pow,mul_one,Nat.reduceAdd,
      Nat.cast_ofNat]
  rw [exactPrimitive] at eq
  have n2 := ERK8PaidField.two_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have e₂ := div_mul_cancel₀ (6:K) n2
  have e₃ := div_mul_cancel₀ (-7:K) n3
  have e₄ := div_mul_cancel₀ (1:K) n4
  have h : (3:K)*4*(probe A b 0 (evalNodes A highAnchorHull))=0 := by
    linear_combination 12*eq+6*e₂+4*e₃+3*e₄+p
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero n3 n4)

theorem polynomial_char11 (p : (11:K)=0) : (11:K[X])=0 := by
  have h := congrArg (C : K→+*K[X]) p
  simpa only [map_ofNat,map_zero] using h

theorem highAnchorHull_remainder (p : (11:K)=0) :
    (highAnchorHull : K[X])=exceptionalQuadratic*(X-C 6)+(C 4+C 3*X) := by
  have pP := polynomial_char11 p
  simp only [highAnchorHull,exceptionalQuadratic,map_one,map_ofNat]
  linear_combination (4-(X:K[X]))*pP

/-- The actual seven-off hull has the nonzero remainder \(4+3X\),
up to a field-unit scale. -/
theorem seven_off_paid_hull_remainder
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3) :
    ∃ gamma : K, gamma≠0 ∧ ∃ W : K[X],
      nodalHull (offKnots A) = C gamma*(C 4+C 3*X)+exceptionalQuadratic*W := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  obtain ⟨lambda,ll,weights⟩ := seven_off_literal_barycentric_weights ha ho p seven three
  let S := offKnots A
  let D := nodalHull S
  let L : K[X] := highAnchorHull
  let q : K[X] := exceptionalQuadratic
  let d (x : K) := offCofactor A x
  let B := (Finset.univ : Finset (Fin 10)).filter (fun j => g A j≠0)
  let val (x : K) := L.eval x/q.eval x
  let U := Lagrange.interpolate S id val
  have Ud : U.natDegree≤6 := by
    by_cases un : U=0
    · simp [un]
    have dn := (natDegree_lt_iff_degree_lt un).mpr
      (Lagrange.degree_interpolate_lt val (Set.injOn_id _) (s:=S))
    change U.natDegree < (offKnots A).card at dn
    omega
  have evalU (x : K) (hx : x∈S) : U.eval x=val x :=
    Lagrange.eval_interpolate_at_node val (Set.injOn_id _) hx
  have R0 := paid_anchor_probe_zero ho p
  have all : (∑ j : Fin 10,b j*L.eval (nodes A j))=0 := by
    simpa only [L,probe,row_apply,dotProduct,pow_zero,mul_one,evalNodes_apply] using R0
  have offSum : (∑ j∈B, b j*L.eval (nodes A j))=0 := by
    change (∑ j ∈ (Finset.univ : Finset (Fin 10)).filter (fun j => g A j≠0),
      b j*L.eval (nodes A j))=0
    rw [Finset.sum_filter]
    convert all using 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases gi : g A i=0
    · have ci := mem_cleanKnots.mpr ⟨i,gi,rfl⟩
      rw [high_clean_clock_anchors ha ho three H] at ci
      simp [gi,show L.eval (nodes A i)=0 from highAnchorHull_zero ci]
    · simp [gi]
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have onB : Set.InjOn (nodes A) (B : Set (Fin 10)) := by
    intro i hi j hj e
    exact inj i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 e
  have weight_sum : lambda*(∑ x∈S, U.eval x/d x)=0 := by
    rw [Finset.mul_sum]
    change (∑ x∈B.image (nodes A),lambda*(U.eval x/d x))=0
    rw [Finset.sum_image onB]
    convert offSum using 1
    apply Finset.sum_congr rfl
    intro i hi
    have gi := (Finset.mem_filter.mp hi).2
    have xi : nodes A i∈S := mem_offKnots.mpr ⟨i,gi,rfl⟩
    rw [evalU _ xi,weights i gi]
    simp only [val,q,d,div_eq_mul_inv]
    ring
  have zero := (mul_eq_zero.mp weight_sum).resolve_left ll
  have Utop : U.coeff 6=0 := by
    have dd : U.natDegree < S.card := by
      change U.natDegree < (offKnots A).card
      omega
    have pp := coeff_last_barycentric S U dd
    change U.coeff ((offKnots A).card-1) = _ at pp
    rw [seven,show 7-1=6 by decide] at pp
    exact pp.trans zero
  have U5 := natDegree_le_of_last_coeff_zero (k:=5) Ud Utop
  have dQL : (q*U-L).natDegree≤S.card := by
    change (q*U-L).natDegree≤(offKnots A).card
    rw [seven]
    exact natDegree_sub_le_of_le
      (natDegree_mul_le_of_le exceptionalQuadratic_degree U5) ((highAnchorHull_degree (K:=K)).trans (show 3≤7 by decide))
  have vanish (x : K) (hx : x∈S) : (q*U-L).eval x=0 := by
    obtain ⟨i,gi,ci⟩ := mem_offKnots.mp hx
    have qn : q.eval x≠0 := ci ▸ exceptional_quadratic_ne_off H gi
    rw [eval_sub,eval_mul,evalU _ hx]
    change q.eval x*(L.eval x/q.eval x)-L.eval x=0
    rw [mul_div_cancel₀ _ qn,sub_self]
  obtain ⟨alpha,e⟩ := polynomial_hull_of_test_zeros S (q*U-L) dQL vanish
  change q*U-L=C alpha*D at e
  have rem : L=q*(X-C 6)+(C 4+C 3*X) := highAnchorHull_remainder p
  have an : alpha≠0 := by
    intro ae
    rw [ae,map_zero,zero_mul] at e
    have div : q∣(C 4+C 3*X : K[X]) := by
      refine ⟨U-(X-C 6),?_⟩
      linear_combination -e-rem
    have deg : (C 4+C 3*X : K[X]).natDegree≤1 :=
      natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
    have r := low_quadratic_multiple_eq_zero deg div
    have c := congrArg (fun Q : K[X] => Q.coeff 1) r
    have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
    exact n3 (by simpa [coeff_C_mul,coeff_C,coeff_X] using c)
  have inv : C alpha⁻¹*C alpha=(1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ an,map_one]
  have hD : D=C alpha⁻¹*(q*U-L) := by rw [e,←mul_assoc,inv,one_mul]
  refine ⟨-alpha⁻¹,neg_ne_zero.mpr (inv_ne_zero an),C alpha⁻¹*(U-(X-C 6)),?_⟩
  change D=_
  rw [hD,rem,map_neg]
  ring

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_paid_hull_remainder
