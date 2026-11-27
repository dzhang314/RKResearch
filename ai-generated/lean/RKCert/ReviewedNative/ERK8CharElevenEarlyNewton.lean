module

public import RKCert.ReviewedNative.ERK8CharElevenHighEarlySetup

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! ## Normalized top-coefficient action on an actual off prefix
The input is interpolated on the \(m-1\) actual preceding off rows.
Causality then identifies the physical A-image on the first \(m\) off
rows. Only the highest Newton coefficient can survive the paid low band
in the top-coefficient functional. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

def earlyRows (n : ℕ) : Finset (Fin 10) :=
  Finset.univ.filter fun j => 0<j.val ∧ j.val≤n

theorem mem_earlyRows {n : ℕ} {j : Fin 10} :
    j∈earlyRows n ↔ 0<j.val ∧ j.val≤n := by simp [earlyRows]

theorem earlyRows_card {n : ℕ} (n4 : n≤4) : (earlyRows n).card=n := by
  let j : Fin 10 := ⟨n,by omega⟩
  have e : earlyRows n=Finset.Icc (1:Fin 10) j := by
    ext i
    rw [mem_earlyRows,Finset.mem_Icc]
    change (0 < i.val ∧ i.val ≤ n) ↔ (1 ≤ i.val ∧ i.val ≤ n)
    omega
  rw [e,Fin.card_Icc]
  change n+1-1=n
  omega

noncomputable def earlyNodes (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) : Finset K :=
  (earlyRows n).image (nodes A)

theorem earlyRows_off (H : HighCenter A 5) {n : ℕ} (n4 : n≤4) {j : Fin 10}
    (hj : j∈earlyRows n) : g A j≠0 := by
  obtain ⟨pos,ub⟩ := mem_earlyRows.mp hj
  apply high_off_before_center H
  · exact pos
  · change j.val<5
    omega

theorem earlyNodes_inj (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {n : ℕ} (n4 : n≤4) :
    Set.InjOn (nodes A) (earlyRows n : Set (Fin 10)) := by
  intro i hi j hj e
  exact (order8_tag_injective_of_full_count (A:=A) (by omega)).2 i j
    (earlyRows_off H n4 hi) (earlyRows_off H n4 hj) e

theorem earlyNodes_card (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {n : ℕ} (n4 : n≤4) : (earlyNodes A n).card=n := by
  rw [earlyNodes,Finset.card_image_iff.mpr (earlyNodes_inj seven three H n4),earlyRows_card n4]

noncomputable def earlyCofactor (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (x : K) : K :=
  (nodalHull ((earlyNodes A n).erase x)).eval x

noncomputable def earlyTop (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (w : Fin 10→K) : K :=
  ∑ j∈earlyRows n, (w j/g A j)/earlyCofactor A n (nodes A j)

noncomputable def earlyBary (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (P : K[X]) : K :=
  ∑ x∈earlyNodes A n, (P.eval x/(exceptionalQuadratic : K[X]).eval x)/earlyCofactor A n x

theorem earlyTop_congr (A : Matrix (Fin 10) (Fin 10) K) {n : ℕ} {v w : Fin 10→K}
    (eq : ∀ j∈earlyRows n, v j=w j) : earlyTop A n v=earlyTop A n w := by
  unfold earlyTop
  exact Finset.sum_congr rfl (fun j hj => by rw [eq j hj])

theorem earlyTop_add (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (v w : Fin 10→K) :
    earlyTop A n (v+w)=earlyTop A n v+earlyTop A n w := by
  unfold earlyTop
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply,div_eq_mul_inv]
  ring

theorem earlyTop_sub (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (v w : Fin 10→K) :
    earlyTop A n (v-w)=earlyTop A n v-earlyTop A n w := by
  unfold earlyTop
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply,div_eq_mul_inv]
  ring

theorem earlyTop_smul (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (a : K) (v : Fin 10→K) :
    earlyTop A n (a • v)=a*earlyTop A n v := by
  unfold earlyTop
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem earlyBary_Cmul (A : Matrix (Fin 10) (Fin 10) K) (n : ℕ) (a : K) (P : K[X]) :
    earlyBary A n (C a*P)=a*earlyBary A n P := by
  unfold earlyBary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eval_mul,eval_C,div_eq_mul_inv]
  ring

theorem earlyTop_g_profile (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {n : ℕ} (n4 : n≤4) (P : K[X]) (deg : P.natDegree<n) :
    earlyTop A n (diag (g A) (evalNodes A P))=P.coeff (n-1) := by
  have inj := earlyNodes_inj seven three H n4
  have count := earlyNodes_card seven three H n4
  have concl := coeff_last_barycentric (earlyNodes A n) P (count.symm ▸ deg)
  rw [count] at concl
  rw [concl]
  change (∑ j∈earlyRows n, (((diag (g A)) (evalNodes A P)) j/g A j)/
    earlyCofactor A n (nodes A j)) =
      ∑ x∈(earlyRows n).image (nodes A), P.eval x/earlyCofactor A n x
  rw [Finset.sum_image inj]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [diag_apply,evalNodes_apply]
  rw [mul_comm (g A j),mul_div_cancel_right₀ _ (earlyRows_off H n4 hj)]

theorem earlyTop_band_zero (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {n k : ℕ} (n4 : n≤4) (h : k<n-1) {w : Fin 10→K} (wb : w∈band A k) :
    earlyTop A n w=0 := by
  obtain ⟨P,Pd,e⟩ := band_iff.mp wb
  rw [e,earlyTop_g_profile seven three H n4 P (by omega)]
  exact coeff_eq_zero_of_natDegree_lt (Pd.trans_lt h)

theorem earlyTop_pure_theta (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    (H : HighCenter A 5) {theta : K} (T : ExceptionalHead A theta) {n : ℕ} (n4 : n≤4)
    (P : K[X]) : earlyTop A n (theta • evalNodes A P)=earlyBary A n P := by
  unfold earlyTop earlyBary earlyNodes
  rw [Finset.sum_image (earlyNodes_inj seven three H n4)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply,smul_eq_mul,evalNodes_apply]
  rw [←T.fit j (earlyRows_off H n4 hj),mul_div_mul_left _ _ T.scale_ne]

theorem high_paid_band_three
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (seven : (offKnots A).card=7) :
    zeroSpace A 3=band A 1 := by
  obtain ⟨r3,_,_⟩ := order8_paid_ranks ha ho (order8_paid_even_horizon ha ho)
  have r := band_rank (A:=A) (q:=1) (by omega)
  refine (Submodule.eq_of_le_of_finrank_le (band_le A 1) ?_).symm
  rw [show (2+1:ℕ)=3 by decide,r3,r]

/-- Two leading-coefficient equations for the original physical first
three or four off rows. The common gain is earned, and is not assumed
to be nonzero. -/
theorem early_paid_newton_two
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {theta : K} (T : ExceptionalHead A theta) (H : HighCenter A 5)
    {m : ℕ} (m034 : m=3∨m=4) :
    ∃ gain : K, ∀ r : ℕ, 1≤r → r≤2 →
      ((r+1:ℕ):K)*gain*earlyBary A (m-1) (X^r)=earlyBary A m (X^(r+1)) := by
  have m3 : 3≤m := by omega
  have m4 : m≤4 := by omega
  have Mp : m-1≤4 := by omega
  have Mb : m-2≤4 := by omega
  have b3 := high_paid_band_three ha ho seven
  have bm : zeroSpace A m=band A (m-2) := by
    rcases m034 with rfl|rfl
    · exact b3
    · exact T.fourthBand
  let S := earlyNodes A (m-1)
  let Base := nodalHull (earlyNodes A (m-2))
  let gain := earlyTop A m (mat A (diag (g A) (evalNodes A Base)))
  have Sc : S.card=m-1 := earlyNodes_card seven three H Mp
  have Bd : Base.natDegree=m-2 :=
    (natDegree_nodalHull _).trans (earlyNodes_card seven three H Mb)
  have Bc : Base.coeff (m-2)=1 := by
    have t : Base.coeff Base.natDegree=1 := (monic_nodalHull _).coeff_natDegree
    rwa [Bd] at t
  refine ⟨gain,?_⟩
  intro r r1 r2
  let P : K[X] := X^r
  let q : K[X] := exceptionalQuadratic
  let values (x : K) := P.eval x/q.eval x
  let U := Lagrange.interpolate S id values
  have Ud : U.natDegree≤m-2 := by
    by_cases u : U=0
    · simp [u]
    have d := (natDegree_lt_iff_degree_lt u).mpr
      (Lagrange.degree_interpolate_lt values (Set.injOn_id _) (s:=S))
    change U.natDegree < S.card at d
    omega
  let alpha := U.coeff (m-2)
  have Ua (x : K) (hx : x∈S) : U.eval x=values x :=
    Lagrange.eval_interpolate_at_node values (Set.injOn_id _) hx
  have alphaEq : alpha=earlyBary A (m-1) P := by
    have lc := coeff_last_barycentric S U (by omega)
    rw [Sc,show m-1-1=m-2 by omega] at lc
    change alpha=(∑ x∈S,U.eval x/earlyCofactor A (m-1) x) at lc
    rw [lc]
    unfold earlyBary
    apply Finset.sum_congr rfl
    intro x hx
    rw [Ua x hx]
  let V := U-C alpha*Base
  have CBd : (C alpha*Base).natDegree≤m-2 := (natDegree_C_mul_le _ _).trans Bd.le
  have Vd : V.natDegree≤m-3 := by
    have w : V.natDegree≤m-2 := by simpa [V] using natDegree_sub_le_of_le Ud CBd
    have c : V.coeff (m-2)=0 := by simp [V,coeff_C_mul,Bc,alpha]
    apply natDegree_le_of_last_coeff_zero (k:=m-3)
    · exact w.trans (by omega)
    · convert c using 2; omega
  have input :
      diag (g A) (evalNodes A U)=
        diag (g A) (evalNodes A V)+alpha • diag (g A) (evalNodes A Base) := by
    ext j
    simp only [V,diag_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,eval_sub,eval_mul,eval_C]
    ring
  have eq (j : Fin 10) (hj : j∈earlyRows m) :
      mat A (theta • evalNodes A P) j=mat A (diag (g A) (evalNodes A U)) j := by
    apply causal_action_eq ha
    intro i ij
    simp only [Pi.smul_apply,smul_eq_mul,evalNodes_apply,diag_apply]
    by_cases i0 : i=0
    · subst i
      have z := (H.clean_iff 0).2 (Or.inl rfl)
      simp [z,P,H.origin_clock,zero_pow (Nat.ne_of_gt r1)]
    have pos : 0 < i.val := by
      by_contra! nz
      exact i0 (Fin.ext (by omega))
    have iP : i∈earlyRows (m-1) := by
      have jm := (mem_earlyRows.mp hj).2
      change i.val < j.val at ij
      exact mem_earlyRows.mpr ⟨pos,by omega⟩
    have hx : nodes A i∈S := Finset.mem_image.mpr ⟨i,iP,rfl⟩
    have gi := earlyRows_off H Mp iP
    have qi := exceptional_quadratic_ne_off T gi
    rw [Ua _ hx,←T.fit i gi]
    change theta*P.eval (nodes A i)=
      theta*q.eval (nodes A i)*(P.eval (nodes A i)/q.eval (nodes A i))
    rw [mul_assoc,mul_div_cancel₀ _ qi]
  have Vmem : diag (g A) (evalNodes A V)∈zeroSpace A (m-1) := by
    have z := band_le A (m-3) (band_iff.mpr ⟨V,Vd,rfl⟩)
    rw [show 2+(m-3)=m-1 by omega] at z
    exact z
  have AV : mat A (diag (g A) (evalNodes A V))∈band A (m-2) := by
    have z : mat A (diag (g A) (evalNodes A V))∈zeroSpace A (m-1+1) :=
      mat_zeroSpace ho (m-1) (by omega) Vmem
    rwa [show m-1+1=m by omega,bm] at z
  have lhs : earlyTop A m (mat A (theta • evalNodes A P))=alpha*gain := by
    rw [earlyTop_congr A eq,input,map_add,map_smul,earlyTop_add,earlyTop_smul,
      earlyTop_band_zero seven three H m4 (by omega) AV,zero_add]
  have Pd : P.natDegree≤2 := (natDegree_X_pow_le _).trans r2
  have ds := primitive_defect_paid ho P Pd (by decide : 2+1≤8)
  have dsm := (zeroSpace A 3).smul_mem theta ds
  rw [smul_sub,←map_smul,b3] at dsm
  have rhs := earlyTop_band_zero seven three H m4 (k:=1) (by omega) dsm
  rw [earlyTop_sub,lhs,earlyTop_pure_theta seven three H T m4,sub_eq_zero] at rhs
  have I : primitive P=C (1/((r+1:ℕ):K))*X^(r+1) := by
    have pmon : P=monomial r (1:K) := by simp [P,←C_mul_X_pow_eq_monomial]
    rw [pmon,primitive_monomial,←C_mul_X_pow_eq_monomial]
  rw [I,earlyBary_Cmul,alphaEq] at rhs
  have nz : (((r+1:ℕ):K))≠0 := (ho.natCast_isUnit (by omega) (by omega)).ne_zero
  have one := mul_div_cancel₀ (1:K) nz
  linear_combination (((r+1:ℕ):K))*rhs+earlyBary A m (X^(r+1))*one

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.early_paid_newton_two
