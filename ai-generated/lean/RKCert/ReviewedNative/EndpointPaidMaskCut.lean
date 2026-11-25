module

public import RKCert.ReviewedNative.NodalPaidHankel
public import RKCert.ReviewedNative.LocalVolterraCutNullity
public import RKCert.ReviewedNative.DIRKTerminalRank

@[expose] public section

/-! # The one-charge endpoint cuts over the original coefficient field

The mask X is the paid shift-two Cauchy block. The mask 1-X is the
adjacent difference of the ordinary moments, so a null vector would give
a constant ordinary Cauchy profile through one additional test. The
existing paid unanchored constant-Cauchy lemma kills that constant.
No inherited sign, characteristic-zero, or full-weight hypothesis.
-/

namespace RKResearch.Certified.Graded

open Module Polynomial FiniteRootedTree
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {s p k z : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem natDegree_endpoint_one : (1-X : K[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_sub]
  simpa only [map_one] using (natDegree_X_sub_C (1 : K))

private theorem probe_nodalColumn_coeff (ho : RKResearch.HasOrder p A b) {q k : ℕ}
    (Q : degreeLT K (q+1)) (pay : k+q+1 ≤ p) :
    probe A b k (nodalColumn A (Q : K[X])) =
       ∑ j : Fin (q+1), degreeLTEquiv K (q+1) Q j / ((k+j.val+1:ℕ):K) := by
  have h : nodalColumn A (Q : K[X]) = coeffEval A q (degreeLTEquiv K (q+1) Q) := by
    ext i
    rw [nodalColumn_apply,Polynomial.eval_eq_sum_degreeLTEquiv Q.property,coeffEval_apply]
    simp only [normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [h,probe_coeffEval ho pay]

private theorem probe_nodalColumn_X_mul (Q : K[X]) (k : ℕ) :
    probe A b k (nodalColumn A (X*Q)) = probe A b (k+1) (nodalColumn A Q) := by
  simp only [probe,row_apply,dotProduct,nodalColumn_apply,Polynomial.eval_mul,Polynomial.eval_X,pow_succ]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

private theorem probe_nodalColumn_one_sub_X_mul (Q : K[X]) (k : ℕ) :
    probe A b k (nodalColumn A ((1-X)*Q)) =
      probe A b k (nodalColumn A Q) - probe A b (k+1) (nodalColumn A Q) := by
  rw [sub_mul,one_mul,(nodalColumn A).map_sub,(probe A b k).map_sub,probe_nodalColumn_X_mul]

/-- The X Hankel is nonsingular at exactly the one-charge budget. -/
theorem nodalPaidHankelFull_X (ho : RKResearch.HasOrder p A b) :
    NodalPaidHankelFull A b (X : K[X]) p := by
  intro q hpay
  rw [natDegree_X] at hpay
  have hbudget : 2*q+2 ≤ p := by omega
  apply (injective_iff_map_eq_zero _).mpr
  intro Q hQ
  let a := degreeLTEquiv K (q+1) Q
  have tests (i : Fin (q+1)) : (∑ j : Fin (q+1), a j / ((i.val+j.val+2:ℕ):K)) = 0 := by
    have hi := i.isLt
    have ht := congrFun hQ i
    change probe A b i.val (nodalColumn A (X*(Q : K[X]))) = 0 at ht
    rw [probe_nodalColumn_X_mul,probe_nodalColumn_coeff ho (k := i.val+1) Q (by omega)] at ht
    have hs (j : Fin (q+1)) : i.val+1+j.val+1 = i.val+j.val+2 := by omega
    simpa only [hs,a] using ht
  have hz := moments_detect ho (n := q+1) (d := 2) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a tests
  apply (degreeLTEquiv K (q+1)).injective
  rw [map_zero]
  exact funext hz

/-- The 1-X Hankel is equally nonsingular, even over fields without an
ordering. The last ordinary test used costs exactly 2q+2. -/
theorem nodalPaidHankelFull_one_sub_X (ho : RKResearch.HasOrder p A b) :
    NodalPaidHankelFull A b (1-X : K[X]) p := by
  intro q hpay
  rw [natDegree_endpoint_one] at hpay
  have hbudget : 2*q+2 ≤ p := by omega
  apply (injective_iff_map_eq_zero _).mpr
  intro Q hQ
  let a := degreeLTEquiv K (q+1) Q
  let g (j : ℕ) : K := ∑ l : Fin (q+1), a l / ((j+l.val+1:ℕ):K)
  have hmom (j : ℕ) (hj : j ≤ q+1) : probe A b j (nodalColumn A (Q : K[X])) = g j :=
    probe_nodalColumn_coeff ho Q (by omega)
  have hstep (j : ℕ) (hj : j ≤ q) : g (j+1) = g j := by
    let i : Fin (q+1) := ⟨j,by omega⟩
    have ht := congrFun hQ i
    change probe A b j (nodalColumn A ((1-X)*(Q : K[X]))) = 0 at ht
    rw [probe_nodalColumn_one_sub_X_mul,hmom j (by omega),hmom (j+1) (by omega),sub_eq_zero] at ht
    exact ht.symm
  have hconstant (j : ℕ) : j ≤ q+1 → g j = g 0 := by
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      exact (hstep j (by omega)).trans (ih (by omega))
  have h0 : g 0 = 0 :=
    Reverse.paid_unanchored_constant_cauchy ho (n := q+1) (by omega) a (g 0)
      (fun i => hconstant i.val (by have := i.isLt; omega))
  have hz := moments_detect ho (n := q+1) (d := 1) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a
    (fun i => (hconstant i.val (by have := i.isLt; omega)).trans h0)
  apply (degreeLTEquiv K (q+1)).injective
  rw [map_zero]
  exact funext hz

/-- The same paid-polynomial cut works in both physical directions with
the actual counted-side kernel rank, no matter what happens on the
discarded side. The premises of the two implications are independent. -/
theorem oneCharge_mask_coordinate_cut (ho : RKResearch.HasOrder p A b)
    (S : Finset (Fin s)) (hS : (cutZeroSpace K S).map (volterra A) ≤ cutZeroSpace K S)
    (P : K[X]) (hpos : P.natDegree < p) (hH : NodalPaidHankelFull A b P p) :
    ((∀ i ∈ S, P.eval (nodes A i) = 0) →
      (finrank K (cutZeroSpace K S ⊓ (volterra A).ker : Submodule K (Fin s → K)) ≤ z) →
      localNullityCutFloor (p-P.natDegree) z ≤ s-S.card) ∧
    ((∀ i ∉ S, b i ≠ 0 → P.eval (nodes A i) = 0) →
      (finrank K ((cutZeroSpace K S).dualAnnihilator ⊓ (volterra A).dualMap.ker :
        Submodule K (ClockCovector K s)) ≤ z) →
      localNullityCutFloor (p-P.natDegree) z ≤ S.card) := by
  constructor
  · intro cover hz
    rw [← finrank_cutZeroSpace K S]
    apply nodalColumn_oneCharge_cut ho P hpos hH _ hS _ hz
    intro Q
    apply (mem_cutZeroSpace S _).mpr
    intro i hi
    simp only [nodalColumn_apply,Polynomial.eval_mul,cover i hi,zero_mul]
  · intro cover hz
    rw [← finrank_cutZeroSpace_annihilator K S]
    have hdual : (cutZeroSpace K S).dualAnnihilator.map (volterra A).dualMap ≤
        (cutZeroSpace K S).dualAnnihilator := by
      rintro _ ⟨f,hf,rfl⟩
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro v hv
      exact (Submodule.mem_dualAnnihilator _).mp hf _ (hS ⟨v,hv,rfl⟩)
    apply nodalRow_oneCharge_cut ho P hpos hH _ hdual _ hz
    intro Q
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    rw [nodalRow_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S
    · rw [(mem_cutZeroSpace S _).mp hv i hi,mul_zero]
    · by_cases hb : b i = 0
      · simp only [hb,zero_mul]
      · simp only [Polynomial.eval_mul,cover i hi hb,zero_mul,mul_zero]

private theorem endpoint_paidMask (ho : RKResearch.HasOrder p A b) {e : K}
    (he : e = 0 ∨ e = 1) :
    ∃ P : K[X], P.natDegree = 1 ∧ P.eval e = 0 ∧ NodalPaidHankelFull A b P p := by
  rcases he with h | h
  · subst e
    exact ⟨X,natDegree_X,eval_X,nodalPaidHankelFull_X ho⟩
  · subst e
    exact ⟨1-X,natDegree_endpoint_one,by simp,nodalPaidHankelFull_one_sub_X ho⟩

/-- A physical prefix at a single endpoint (zero or one) or a suffix
whose individually active clocks all equal one endpoint pays the
stronger effective order p−1. Only the counted zero diagonals enter. -/
theorem mixed_chronological_endpoint_clock_cut (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hp : 2 ≤ p) (hk : k ≤ s) :
    ((∃ e : K, (e = 0 ∨ e = 1) ∧ (∀ i ∈ chronologicalHead hk, nodes A i = e)) →
      localNullityCutFloor (p-1)
        (zeroDiagonalSites A (Finset.univ \ chronologicalHead hk)).card ≤ s-k) ∧
    ((∃ e : K, (e = 0 ∨ e = 1) ∧ (∀ i ∉ chronologicalHead hk, b i ≠ 0 → nodes A i = e)) →
      localNullityCutFloor (p-1)
        (zeroDiagonalSites A (chronologicalHead hk)).card ≤ k) := by
  let S := chronologicalHead hk
  have hs := cutZeroSpace_volterra_le ha S (chronologicalHead_downward hk)
  constructor
  · rintro ⟨e,he,cover⟩
    obtain ⟨P,hd,hzero,hH⟩ := endpoint_paidMask ho he
    have hz := volterra_column_cutKer_le_zeroSites ha S
    have cut := (oneCharge_mask_coordinate_cut ho S hs P (by omega) hH
      (z := (zeroDiagonalSites A (Finset.univ \ S)).card)).1
      (fun i hi => by rw [cover i hi,hzero]) hz
    simpa only [hd,S,chronologicalHead_card] using cut
  · rintro ⟨e,he,cover⟩
    obtain ⟨P,hd,hzero,hH⟩ := endpoint_paidMask ho he
    have hz := volterra_row_cutKer_le_zeroSites ha S
    have cut := (oneCharge_mask_coordinate_cut ho S hs P (by omega) hH
      (z := (zeroDiagonalSites A S).card)).2
      (fun i hi hb => by rw [cover i hi hb,hzero]) hz
    simpa only [hd,S,chronologicalHead_card] using cut

end
end RKResearch.Certified.Graded
