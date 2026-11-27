module

public import RKCert.ReviewedNative.ERK8FourOffNodalTransfer
public import RKCert.ReviewedNative.ERK8CharElevenFourEarlyNewton

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid top Newton rows of the actual four-off tableau
Only the literal first three off senders are interpolated. The only
possible additional input is the true first nonzero clean coordinate. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch LobattoEight ERK8CharEleven OneOff ERKTaggedHorizon FourOffPhysical
open ERK8PaidField RKCert.Endpoint
open scoped Classical BigOperators Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
variable {P : K[X]} {dup k : Fin 10}

def earlyZoneOff (k : Fin 10) : Finset (Fin 10) :=
  Finset.univ.filter fun i=>0 < i ∧ i < 6 ∧ i≠k

def fourthEarlyOff (k : Fin 10) : Fin 10 := if k=4 then 5 else 4

theorem mem_earlyZoneOff {k i : Fin 10} :
    i∈earlyZoneOff k ↔ 0 < i ∧ i < 6 ∧ i≠k := by simp [earlyZoneOff]

theorem early_off_fourth_layout (hk : k=4∨k=5) :
    earlyZoneOff k=insert (fourthEarlyOff k) (earlyRows 3) ∧
      fourthEarlyOff k∉earlyRows 3 := by
  rcases hk with rfl|rfl <;> decide

theorem early_off_on_zone (M : Placement A b P dup k) {j : Fin 10} (hj : j∈earlyZoneOff k) :
    g A j≠0 := by
  obtain ⟨j0,j6,jk⟩ := mem_earlyZoneOff.mp hj
  exact fun g=>jk (M.onlyCleanInMiddle j j0 j6 g)

theorem early_off_inj_on_zone (M : Placement A b P dup k) :
    Set.InjOn (nodes A) (earlyZoneOff k : Set (Fin 10)) := by
  intro i hi j hj e
  exact FourOff.early_off_distinct_of_placement M i j
    (mem_earlyZoneOff.mp hi).2.1 (mem_earlyZoneOff.mp hj).2.1
    (early_off_on_zone M hi) (early_off_on_zone M hj) e

theorem early_off_three_in_zone (hk : k=4∨k=5) :
    earlyRows 3⊆earlyZoneOff k := by
  rw [(early_off_fourth_layout hk).1]
  exact Finset.subset_insert _ _

theorem early_off_image (M : Placement A b P dup k) :
    (earlyZoneOff k).image (nodes A)=offKnots A := by
  ext x
  constructor
  · rintro hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact mem_offKnots.mpr ⟨j,early_off_on_zone M hj,rfl⟩
  · rintro hx
    obtain ⟨j,h0,h6,gj,hc⟩ := M.offSenders x hx
    refine Finset.mem_image.mpr ⟨j,mem_earlyZoneOff.mpr ⟨h0,h6,?_⟩,hc⟩
    exact fun e=>gj (e.symm ▸ M.firstClean)

theorem early_off_three_count (M : Placement A b P dup k) : (earlyNodes A 3).card=3 := by
  rw [earlyNodes,Finset.card_image_of_injOn,earlyRows_card (by decide)]
  exact (early_off_inj_on_zone M).mono (early_off_three_in_zone M.firstAtFourOrFive)

theorem early_off_insert (M : Placement A b P dup k) :
    offKnots A=insert (nodes A (fourthEarlyOff k)) (earlyNodes A 3) ∧
      nodes A (fourthEarlyOff k)∉earlyNodes A 3 := by
  obtain ⟨lay,notin⟩ := early_off_fourth_layout M.firstAtFourOrFive
  refine ⟨?_,?_⟩
  · rw [←early_off_image M,lay,Finset.image_insert,earlyNodes]
  · intro e
    obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp e
    have z := early_off_inj_on_zone M (early_off_three_in_zone M.firstAtFourOrFive hj)
      (lay.symm ▸ Finset.mem_insert_self _ _) eq
    exact notin (z ▸ hj)

noncomputable def physicalTop (A : Matrix (Fin 10) (Fin 10) K) (k : Fin 10) (v : Fin 10→K) : K :=
  ∑ j∈earlyZoneOff k, (v j/g A j)/nodalCofactor (offKnots A) (nodes A j)

theorem physicalTop_congr {v w : Fin 10→K} (H : ∀ j∈earlyZoneOff k,v j=w j) :
    physicalTop A k v=physicalTop A k w := by
  unfold physicalTop
  exact Finset.sum_congr rfl fun j hj=>by rw [H j hj]

theorem physicalTop_add (A : Matrix (Fin 10) (Fin 10) K) (k : Fin 10) (v w : Fin 10→K) :
    physicalTop A k (v+w)=physicalTop A k v+physicalTop A k w := by
  simp only [physicalTop,Pi.add_apply,add_div,Finset.sum_add_distrib]

theorem physicalTop_sub (A : Matrix (Fin 10) (Fin 10) K) (k : Fin 10) (v w : Fin 10→K) :
    physicalTop A k (v-w)=physicalTop A k v-physicalTop A k w := by
  simp only [physicalTop,Pi.sub_apply,sub_div,Finset.sum_sub_distrib]

theorem physicalTop_smul (A : Matrix (Fin 10) (Fin 10) K) (k : Fin 10) (a : K) (v : Fin 10→K) :
    physicalTop A k (a • v)=a*physicalTop A k v := by
  simp only [physicalTop,Pi.smul_apply,smul_eq_mul,mul_div_assoc,Finset.mul_sum]

theorem physicalTop_pure (M : Placement A b P dup k) (G : K[X]) :
    physicalTop A k (evalNodes A G)=nodalMeasure P (offKnots A) G := by
  unfold physicalTop nodalMeasure
  rw [←early_off_image M,Finset.sum_image (early_off_inj_on_zone M)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [early_off_image M,evalNodes_apply,M.rankData.fit j (early_off_on_zone M hj)]

theorem physicalTop_band_zero (M : Placement A b P dup k) {v : Fin 10→K} (B : v∈band A 2) :
    physicalTop A k v=0 := by
  obtain ⟨G,gd,rfl⟩ := band_iff.mp B
  have row : physicalTop A k (diag (g A) (evalNodes A G)) =
      ∑ x∈offKnots A,G.eval x/nodalCofactor (offKnots A) x := by
    unfold physicalTop
    rw [←early_off_image M,Finset.sum_image (early_off_inj_on_zone M)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [diag_apply,evalNodes_apply]
    rw [mul_comm (g A j),mul_div_cancel_right₀ _ (early_off_on_zone M hj)]
  have coeff := coeff_last_barycentric (offKnots A) G (by rw [M.rankData.offCard]; omega)
  rw [M.rankData.offCard,show (4-1:ℕ)=3 by decide,coeff_eq_zero_of_natDegree_lt (gd.trans_lt (by decide))] at coeff
  exact row.trans coeff.symm

private theorem prior_off_sits_first_three (hk : k=4∨k=5) {i j : Fin 10}
    (hj : j∈earlyZoneOff k) (lt : i < j) (ipos : 0 < i) (ik : i≠k) :
    i∈earlyRows 3 := by
  obtain ⟨_,bound,_⟩ := mem_earlyZoneOff.mp hj
  rw [mem_earlyRows]
  rcases hk with rfl|rfl <;> omega

theorem paid_newton_physical
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (M : Placement A b P dup k) :
    ∃ δ tap gain : K,
      (k=5 → tap=0) ∧
      ∀ r : ℕ, 1≤r → r≤3 →
        let L₃ := nodalMeasure P (earlyNodes A 3) (X^r)
        let L₄ := nodalMeasure P (offKnots A) (X^(r+1))
        (δ*L₃+tap*(nodes A k)^r=L₄/((r+1:ℕ):K)) ∧
          (k=4 → gain*L₃=(nodes A k)^(r+1)/((r+1:ℕ):K)) := by
  let S := earlyNodes A 3
  let h := nodes A k
  let gn := diag (g A) (evalNodes A (X^2))
  let u : Fin 10→K := Pi.single k 1
  let δ := physicalTop A k (mat A gn)
  let tap := physicalTop A k (mat A u)
  let gain := mat A gn k
  have tap5 (k5 : k=5) : tap=0 := by
    unfold tap physicalTop
    apply Finset.sum_eq_zero
    intro j hj
    have nz (l : Fin 10) (lt : l < j) : u l=0 := by
      have j6 := (mem_earlyZoneOff.mp hj).2.1
      have eq : l≠k := fun e=>by subst l; omega
      simp [u,Pi.single_eq_of_ne eq]
    rw [causal_mat ha j u nz,zero_div,zero_div]
  refine ⟨δ,tap,gain,tap5,?_⟩
  intro r r1 r3
  dsimp only
  let G : K[X] := X^r
  let U := nodalDivide P S G
  let α := U.coeff 2
  let V := U-C α*X^2
  have ud : U.natDegree≤2 := nodalDivide_degree P S G (early_off_three_count M)
  have vd : V.natDegree≤1 := by
    apply natDegree_le_of_last_coeff_zero (k:=1)
    · exact natDegree_sub_le_of_le ud ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _))
    · simp [V,α,coeff_C_mul,coeff_X_pow]
  have αf : α=nodalMeasure P S G := (nodalMeasure_top P S G (early_off_three_count M)).symm
  have split : diag (g A) (evalNodes A U)=diag (g A) (evalNodes A V)+α • gn := by
    ext j
    simp only [V,gn,diag_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,
      eval_sub,eval_mul,eval_C]
    ring
  have pure0 : G.eval (nodes A 0)=0 := by
    simp [G,M.rankData.clockZero,zero_pow (Nat.ne_of_gt r1)]
  have input (i : Fin 10) (hi : i∈earlyRows 3) :
      G.eval (nodes A i)=g A i*U.eval (nodes A i) := by
    have gi := early_off_on_zone M (early_off_three_in_zone M.firstAtFourOrFive hi)
    rw [nodalDivide_eval P S G (Finset.mem_image.mpr ⟨i,hi,rfl⟩),M.rankData.fit i gi,
      mul_div_cancel₀ _ gi]
  have eq (j : Fin 10) (hj : j∈earlyZoneOff k) :
      mat A (evalNodes A G) j=
        mat A (diag (g A) (evalNodes A U)+h^r • u) j := by
    apply causal_action_eq ha
    intro i ij
    simp only [evalNodes_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply]
    by_cases i0 : i=0
    · subst i
      have k0 : (0:Fin 10)≠k := by have c := M.firstAtFourOrFive; omega
      simp [pure0,M.rankData.cleanZero,u,Pi.single_eq_of_ne k0]
    by_cases ik : i=k
    · subst i
      simp [M.firstClean,u,h,G]
    have pos : 0 < i := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm i0)
    have mem := prior_off_sits_first_three M.firstAtFourOrFive hj ij pos ik
    simp [u,Pi.single_eq_of_ne ik,input i mem]
  have mine : diag (g A) (evalNodes A V)∈zeroSpace A 3 :=
    band_le A 1 (band_iff.mpr ⟨V,vd,rfl⟩)
  have im := mat_zeroSpace ho 3 (by decide) mine
  have imband : mat A (diag (g A) (evalNodes A V))∈band A 2 := M.rankData.bandFour ▸ im
  have top : physicalTop A k (mat A (evalNodes A G))=
      δ*nodalMeasure P S G+tap*h^r := by
    rw [physicalTop_congr eq,split,map_add,map_add,map_smul,map_smul,physicalTop_add,physicalTop_add,
      physicalTop_smul,physicalTop_smul,physicalTop_band_zero M imband,zero_add,αf]
    change _*δ+_*tap=_
    ring
  have pd : G.natDegree≤3 := (natDegree_X_pow_le _).trans r3
  have paid := primitive_defect_paid ho G pd (by decide : 3+1≤8)
  have pr : primitive G=C (1/((r+1:ℕ):K))*X^(r+1) := by
    have gm : G=monomial r (1:K) := by simp [G,←C_mul_X_pow_eq_monomial]
    rw [gm,primitive_monomial,←C_mul_X_pow_eq_monomial]
  have lhs := physicalTop_band_zero M (M.rankData.bandFour ▸ paid)
  rw [physicalTop_sub,top,physicalTop_pure M,pr,nodalMeasure_Cmul,sub_eq_zero] at lhs
  refine ⟨?_,?_⟩
  · simpa [G,S,h,div_eq_mul_inv,mul_comm] using lhs
  · intro k4
    have eqC : mat A (evalNodes A G) k=mat A (diag (g A) (evalNodes A U)) k := by
      apply causal_action_eq ha
      intro j jk
      simp only [diag_apply,evalNodes_apply]
      by_cases j0 : j=0
      · subst j; simp [pure0,M.rankData.cleanZero]
      have mem : j∈earlyRows 3 := by
        rw [mem_earlyRows]
        omega
      exact input j mem
    have van := clean_four_vanish M.rankData.bandFour M.firstClean im
    have id := clean_four_vanish M.rankData.bandFour M.firstClean paid
    rw [Pi.sub_apply,eqC,split,map_add,map_smul,Pi.add_apply,Pi.smul_apply,van,zero_add,smul_eq_mul,αf,
      evalNodes_apply,pr,eval_mul,eval_C,eval_pow,eval_X,sub_eq_zero] at id
    simpa only [G,S,h,gain,div_eq_mul_inv,one_mul,mul_comm] using id

theorem paid_newton_clean_transfer
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4) (n : ∀ x∈S,P.eval x≠0) (p2 : P.natDegree=2)
    {R : K[X]} {sig : K} (sign : sig≠0)
    (terminal : nodalHull S+P*R=C sig*nodalHull (offKnots A)) :
    ∃ δ tap gain : K,
      (k=5 → tap=0) ∧
      ∀ r : ℕ, 1≤r → r≤3 →
        let Cᵣ := nodalMeasure P S (X^r)
        let Cₛ := nodalMeasure P S (X^(r+1))
        let e := nodes A (fourthEarlyOff k)
        (δ*(Cₛ-e*Cᵣ)+tap*(nodes A k)^r=Cₛ/((r+1:ℕ):K)) ∧
          (k=4 → gain*(Cₛ-e*Cᵣ)=(nodes A k)^(r+1)/((r+1:ℕ):K)) := by
  obtain ⟨δ,tap,gain,t5,eq⟩ := paid_newton_physical ha ho M
  obtain ⟨insertEq,notin⟩ := early_off_insert M
  let e := nodes A (fourthEarlyOff k)
  have nt (x : K) (hx : x∈offKnots A) : P.eval x≠0 := by
    obtain ⟨j,gj,rfl⟩ := mem_offKnots.mp hx
    rw [M.rankData.fit j gj]
    exact gj
  refine ⟨δ,tap/sig,gain*sig,fun h=>by simp [t5 h],?_⟩
  intro r r1 r3
  have d1 : (X^r : K[X]).natDegree≤4 := (natDegree_X_pow_le _).trans (by omega)
  have d2 : (X^(r+1) : K[X]).natDegree≤4 := (natDegree_X_pow_le _).trans (by omega)
  have t1 := nodalMeasure_transfer_four (G:=X^r) p2 d1 M.rankData.offCard Sc nt n terminal
  have t2 := nodalMeasure_transfer_four (G:=X^(r+1)) p2 d2 M.rankData.offCard Sc nt n terminal
  have cut := nodalMeasure_erase_pow P notin r
  rw [←insertEq,t1,t2] at cut
  obtain ⟨p,c⟩ := eq r r1 r3
  dsimp only at p c ⊢
  rw [cut,t2] at p
  refine ⟨?_,?_⟩
  · apply mul_left_cancel₀ sign
    have v := mul_div_cancel₀ tap sign
    have id := mul_div_assoc sig (nodalMeasure P S (X^(r+1))) (((r+1:ℕ):K))
    linear_combination p+(nodes A k)^r*v-id
  · intro k4
    have h := c k4
    rw [cut] at h
    linear_combination h

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.paid_newton_physical
#print axioms RKResearch.Certified.Graded.FourOffNewton.paid_newton_clean_transfer
