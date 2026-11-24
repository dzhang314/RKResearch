module

public import RKCert.ReviewedNative.OneOffCaseTwoScalars

@[expose] public section

/-! # Complete independent-square Case II on physical rows -/
namespace RKResearch.Certified.Graded.OneOff
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

private theorem case_two_no_exception (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    {a d v : K} {i₀ : Fin s} (O : Origin A a i₀) (D : CaseTwo A a d v)
    (eq : a=2*d) : False := by
  apply c4_support_two_impossible ha sep a d a (Or.inl rfl)
  · intro x
    rw [eq]
    ring
  · intro i na nd
    have gg : g A i=0 := by by_contra e; exact na (O.off_support i e)
    have hh := D.onH i gg nd
    have zz : zTwo A a i=0 := by simp [zTwo_apply,gg]
    exact ⟨gg,by rw [D.q2]; simp [gg,hh],by rw [D.q3]; simp [gg,hh,zz]⟩

private theorem case_two_confined (ha : ∀ i j, i ≤ j → A i j = 0) {a d v : K} {i₀ : Fin s}
    (O : Origin A a i₀) (D : CaseTwo A a d v) (ne : a≠2*d) :
    ∀ i, FourFeatures a d (twoHd a d) v (twoGam a d) (nodes A i) (g A i) (h A i) := by
  intro i
  refine wellFounded_lt.induction
    (C:=fun i=>FourFeatures a d (twoHd a d) v (twoGam a d) (nodes A i) (g A i) (h A i)) i ?_
  intro i ih
  have RQ := qres_of_four_sources ha i D.q2 D.q3 ih
  have RA := hres_of_four_sources ha i D.an D.dn D.da D.q2 D.hk ih
  by_cases G : g A i=0
  · have Z : zTwo A a i=0 := by simp [zTwo_apply,G]
    rw [G,Z] at RA RQ
    by_cases xd : nodes A i=d
    · rw [xd,two_q_clean_d a d v _ D.an] at RQ
      rw [xd,two_h_clean_d a d v _ D.an D.dn D.da] at RA
      have H : h A i=twoHd a d := by
        by_contra e
        have hd := sub_ne_zero.mpr e
        have p := (div_eq_zero_iff.mp RQ).resolve_right (mul_ne_zero (by norm_num) D.an)
        have q := (div_eq_zero_iff.mp RA).resolve_right (by norm_num)
        have p' : 2*a-d=0 := (mul_eq_zero.mp ((mul_eq_zero.mp p).resolve_right hd)).resolve_left
          (neg_ne_zero.mpr D.dn)
        have q' : a+d=0 := neg_eq_zero.mp ((mul_eq_zero.mp q).resolve_right hd)
        exact mul_ne_zero (by norm_num : (3:K)≠0) D.an (show 3*a=0 by linear_combination p'+q')
      exact Or.inl (Or.inr (Or.inr ⟨xd,G,H⟩))
    · have H := D.onH i G xd
      by_cases xn : nodes A i=0
      · exact Or.inl (Or.inl ⟨xn,G,H⟩)
      · rw [H,qres_clean] at RQ
        rw [H,two_h_clean a d v _ D.an D.dn D.da] at RA
        have qb : Btwo a d (nodes A i)=0 :=
          (mul_eq_zero.mp ((div_eq_zero_iff.mp RQ).resolve_right (by norm_num))).resolve_left
            (neg_ne_zero.mpr (pow_ne_zero 2 xn))
        have la : Ltwo a d (nodes A i)=0 :=
          (mul_eq_zero.mp ((div_eq_zero_iff.mp RA).resolve_right
            (mul_ne_zero (by norm_num) D.dn))).resolve_left (mul_ne_zero D.an (pow_ne_zero 2 xn))
        exact (two_linear_quadratic_exclusion _ _ _ D.an D.dn ne qb la).elim
  · have X := O.off_support i G
    have H := D.offH i G
    rw [X,H,zTwo_apply,two_q_off a d v _ D.an D.dn D.vn] at RQ
    have n := (div_eq_zero_iff.mp RQ).resolve_right (mul_ne_zero (by norm_num) D.vn)
    have pair := (mul_eq_zero.mp n).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr D.an) (sub_ne_zero.mpr ne))
    rcases mul_eq_zero.mp pair with f|f
    · have gg := sub_eq_zero.mp f
      have hh : h A i=0 := by rw [H,zTwo_apply,gg,sub_self,mul_zero,mul_zero]
      exact Or.inl (Or.inr (Or.inl ⟨X,gg,hh⟩))
    · have gg := sub_eq_zero.mp f
      have hh : h A i=twoGam a d*(v-baseAmp a) := by
        rw [H,zTwo_apply,gg,←mul_assoc,div_mul_cancel₀ _ D.vn]
      exact Or.inr ⟨X,gg,hh⟩

/-- An actual one-off tableau with the independent-square shape cannot
have its first nonzero (Ag) at an on row. Works already at p8. -/
theorem independent_square_on_first_impossible (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    {a lam : K} {i j : Fin s} (O : Origin A a i) (F : FirstH A a lam j)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A)
    (shape : IndependentShape A a lam i j) (on : g A j=0) : False := by
  let d := nodes A j
  obtain ⟨v,D⟩ := case_two_calibration ha sep O F Q2 shape on
  by_cases e : a=2*d
  · exact case_two_no_exception ha sep O D e
  · have all := case_two_confined ha O D e
    apply sep.knots_not_cover ({0,a,d}:Finset K)
      ((Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp))))
    intro r
    rcases four_features_clocks (all r) with e0|e1|e2
    · simp [e0]
    · simp [e1]
    · simp [e2,d]

end RKResearch.Certified.Graded.OneOff
