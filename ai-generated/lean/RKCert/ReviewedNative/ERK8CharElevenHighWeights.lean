module

public import RKCert.ReviewedNative.ERK8CharElevenOmittedHead

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual high-off weights are a nonzero barycentric profile
The profile is earned using only order-eight probes. Its native proof
uses a five-degree cut dropping two off clocks, rather than assuming a
quadratic-field splitting or imposing an independent rank hypothesis. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Module Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- The derivative of the off hull at an off knot, written as the
evaluation of its erase-one factor to simplify exact two-point cuts. -/
noncomputable def offCofactor (A : Matrix (Fin 10) (Fin 10) K) (x : K) : K :=
  (nodalHull ((offKnots A).erase x)).eval x

theorem offCofactor_ne (A : Matrix (Fin 10) (Fin 10) K) (x : K) : offCofactor A x ≠ 0 :=
  nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)

/-- Dropping two off knots leaves a degree-five cut; comparing its two
surviving terms gives equal weighted cofactor products. -/
theorem seven_off_cofactor_products (ho : HasOrder 8 A b)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {i k : Fin 10} (gi : g A i≠0) (gk : g A k≠0) :
    b i*g A i*offCofactor A (nodes A i) = b k*g A k*offCofactor A (nodes A k) := by
  classical
  by_cases ik : i=k
  · rw [ik]
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  let S := offKnots A
  let a := nodes A i
  let c := nodes A k
  have ac : a≠c := fun e => ik (inj i k gi gk e)
  have ma : a∈S := mem_offKnots.mpr ⟨i,gi,rfl⟩
  have mc : c∈S := mem_offKnots.mpr ⟨k,gk,rfl⟩
  have mca : c∈S.erase a := Finset.mem_erase.mpr ⟨ac.symm,mc⟩
  have mac : a∈S.erase c := Finset.mem_erase.mpr ⟨ac,ma⟩
  let T := (S.erase a).erase c
  let P := nodalHull T
  have hd : P.natDegree≤5 := by
    have n1 := Finset.card_erase_add_one ma
    have n2 := Finset.card_erase_add_one mca
    rw [show P.natDegree=T.card from natDegree_nodalHull _]
    change T.card + 1 = (S.erase a).card at n2
    change S.card=7 at seven
    omega
  let v := diag (g A) (evalNodes A P)
  have mem : v∈zeroSpace A 7 := band_le A 5 (band_iff.mpr ⟨P,hd,rfl⟩)
  have pay : probe A b 0 v=0 := probe_zeroSpace ho (j:=7) (k:=0) (by decide) mem
  let term (j : Fin 10) : K := b j*(g A j*P.eval (nodes A j))
  have sum : (∑ j, term j)=0 := by
    simpa only [term,v,probe,row_apply,dotProduct,pow_zero,mul_one,diag_apply,evalNodes_apply] using pay
  have van (j : Fin 10) (ji : j≠i) (jk : j≠k) : term j=0 := by
    by_cases gj : g A j=0
    · simp [term,gj]
    · have ja : nodes A j≠a := fun e => ji (inj j i gj gi e)
      have jc : nodes A j≠c := fun e => jk (inj j k gj gk e)
      have jm : nodes A j∈S := mem_offKnots.mpr ⟨j,gj,rfl⟩
      have jT : nodes A j∈T := Finset.mem_erase.mpr ⟨jc,Finset.mem_erase.mpr ⟨ja,jm⟩⟩
      simp [term,show P.eval (nodes A j)=0 from nodalHull_eval_of_mem jT]
  have sub : (∑ j∈({i,k} : Finset (Fin 10)), term j) = ∑ j, term j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ jn
    have ji : j≠i := fun e => jn (by simp [e])
    have jk : j≠k := fun e => jn (by simp [e])
    exact van j ji jk
  have pp : b i*(g A i*P.eval a)+b k*(g A k*P.eval c)=0 := by
    have e := sub.trans sum
    simpa [Finset.sum_pair ik,term,a,c] using e
  have f1 : offCofactor A a=(a-c)*P.eval a := by
    change (nodalHull (S.erase a)).eval a=_
    rw [nodalHull_erase_factor (S.erase a) mca,eval_mul,eval_sub,eval_X,eval_C]
  have f2 : offCofactor A c=(c-a)*P.eval c := by
    change (nodalHull (S.erase c)).eval c=_
    rw [nodalHull_erase_factor (S.erase c) mac,Finset.erase_right_comm,eval_mul,eval_sub,eval_X,eval_C]
  change b i*g A i*offCofactor A a=b k*g A k*offCofactor A c
  rw [f1,f2]
  linear_combination (a-c)*pp

private theorem clean_three_grid (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (three : (cleanKnots A).card=3) {theta : K} (H : ExceptionalHead A theta) :
    cleanKnots A = ({0,1,6} : Finset K) := by
  have cz := zero_mem_cleanKnots (s:=9) ha
  have c1 : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 9,H.terminal_clean,H.terminal_clock⟩
  have n6 : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have n61 : (6:K)≠1 := fun e => n5 (by linear_combination e)
  have card : ({0,1,6} : Finset K).card=3 := by
    simp [Finset.card_insert_of_notMem,zero_ne_one,n6.symm,n61.symm]
  have sub : ({0,1,6} : Finset K) ⊆ cleanKnots A := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h|h|h
    · exact h.symm ▸ cz
    · exact h.symm ▸ c1
    · exact h.symm ▸ H.center_mem
  exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm

/-- The common scale is nonzero: otherwise the actual quadrature lives
on 0, 6, 1, which contradicts its paid integral of X²(X−6)(X−1). -/
theorem seven_off_literal_nonzero_cofactor_scale
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3) :
    ∃ lambda : K, lambda≠0 ∧ ∀ i, g A i≠0 →
      b i*g A i*offCofactor A (nodes A i)=lambda := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  have grid := clean_three_grid ha ho three H
  obtain ⟨x,mx⟩ := Finset.card_pos.mp (by omega : 0<(offKnots A).card)
  obtain ⟨k,gk,_⟩ := mem_offKnots.mp mx
  let lambda := b k*g A k*offCofactor A (nodes A k)
  have eq (i : Fin 10) (gi : g A i≠0) :
      b i*g A i*offCofactor A (nodes A i)=lambda :=
    seven_off_cofactor_products ho seven three gi gk
  refine ⟨lambda,?_,eq⟩
  intro lm
  have bout (i : Fin 10) (gi : g A i≠0) : b i=0 := by
    have z := (eq i gi).trans lm
    exact (mul_eq_zero.mp ((mul_eq_zero.mp z).resolve_right
      (offCofactor_ne A _))).resolve_right gi
  let L : K[X] := monomial 2 6 + monomial 3 (-7) + monomial 4 1
  have Ld : L.natDegree≤4 := by
    apply natDegree_add_le_of_degree_le
    · exact natDegree_add_le_of_degree_le ((show ((monomial 2 (6:K))).natDegree≤2 from natDegree_monomial_le _).trans (by decide))
        ((show ((monomial 3 (-7:K))).natDegree≤3 from natDegree_monomial_le _).trans (by decide))
    · exact natDegree_monomial_le _
  have leval (u : K) : L.eval u=u^2*(u-6)*(u-1) := by
    simp only [L,eval_add,eval_monomial]
    ring
  have van : probe A b 0 (evalNodes A L)=0 := by
    simp only [probe,row_apply,dotProduct,pow_zero,mul_one,evalNodes_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases gi : g A i=0
    · have ci := mem_cleanKnots.mpr ⟨i,gi,rfl⟩
      rw [grid] at ci
      simp only [Finset.mem_insert,Finset.mem_singleton] at ci
      rw [leval]
      rcases ci with z|z|z <;> simp [z]
    · simp [bout i gi]
  have v := probe_evalNodes ho L 0 (by omega)
  rw [van,pow_zero,one_mul] at v
  simp only [L,map_add,primitive_monomial,eval_add,eval_monomial,one_pow,mul_one,Nat.reduceAdd,
    Nat.cast_ofNat] at v
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have u3 := div_mul_cancel₀ (6:K) n3
  have u4 := div_mul_cancel₀ (-7:K) n4
  have u5 := div_mul_cancel₀ (1:K) n5
  exact one_ne_zero (by linear_combination 120*v+40*u3+30*u4+24*u5+5*p : (1:K)=0)

/-- Normalized to the exceptional quadratic, these are the actual
nonzero high-off weights in the standard nodal cofactor form. -/
theorem seven_off_literal_barycentric_weights
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3) :
    ∃ lambda : K, lambda≠0 ∧ ∀ i, g A i≠0 →
      b i=lambda/((exceptionalQuadratic : K[X]).eval (nodes A i)*offCofactor A (nodes A i)) := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  obtain ⟨lambda,nl,w⟩ := seven_off_literal_nonzero_cofactor_scale ha ho p seven three
  refine ⟨lambda/theta,div_ne_zero nl H.scale_ne,?_⟩
  intro i gi
  have qn : (exceptionalQuadratic : K[X]).eval (nodes A i) ≠ 0 := by
    intro e
    exact gi (by rw [←H.fit i gi,e,mul_zero])
  have r := w i gi
  rw [←H.fit i gi] at r
  apply (eq_div_iff (mul_ne_zero qn (offCofactor_ne A _))).mpr
  apply (eq_div_iff H.scale_ne).mpr
  linear_combination r

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_literal_nonzero_cofactor_scale

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_literal_barycentric_weights
