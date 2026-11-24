module

public import RKCert.ERKOrderNineOneOffCaseThreeScalars

@[expose] public section

/-! # Complete independent-square Case III on physical rows -/
namespace RKCert.Paired.OneOff
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Fin s→Fin s→K}

private theorem case_three_no_exception (ha : StrictLower A) (sep : Separated A 4)
    {a d v : K} {i₀ : Fin s} (O : Origin A a i₀) (D : CaseThree A a d v)
    (eq : d=2*a) : False := by
  apply c4_support_two_impossible ha sep a d d (Or.inr rfl)
  · intro x
    rw [eq]
    ring
  · intro i na nd
    have gg : g A i=0 := by by_contra e; exact na (O.off_support i e)
    have hh := D.onH i gg nd
    have zz : zThree A a v i=0 := by simp [zThree_apply,gg,hh]
    exact ⟨gg,by rw [D.q2]; simp [gg,hh],by rw [D.q3]; simp [gg,hh,zz]⟩

private theorem case_three_confined (ha : StrictLower A) {a d v : K} {i₀ : Fin s}
    (O : Origin A a i₀) (D : CaseThree A a d v) (ne : d≠2*a) :
    ∀ i, FourFeatures a d (threeHd a d) v (threeGam a) (nodes A i) (g A i) (h A i) := by
  intro i
  refine wellFounded_lt.induction
    (C:=fun i=>FourFeatures a d (threeHd a d) v (threeGam a) (nodes A i) (g A i) (h A i)) i ?_
  intro i ih
  have RQ := qres_of_four_sources ha i D.q2 D.q3 ih
  have RA := hres_of_four_sources ha i D.an D.dn D.da D.q2 D.hk ih
  by_cases G : g A i=0
  · have Z : zThree A a v i=(2*v/a)*h A i := by simp [zThree_apply,G]
    rw [G,Z] at RA RQ
    by_cases xd : nodes A i=d
    · rw [xd,three_q_clean_d a d v _ D.an D.vn D.dNorm] at RQ
      have H : h A i=threeHd a d := by
        have p := (div_eq_zero_iff.mp RQ).resolve_right (mul_ne_zero (by norm_num) D.dNorm)
        exact sub_eq_zero.mp ((mul_eq_zero.mp p).resolve_left
          (mul_ne_zero D.dn (sub_ne_zero.mpr (Ne.symm ne))))
      exact Or.inl (Or.inr (Or.inr ⟨xd,G,H⟩))
    · have H := D.onH i G xd
      by_cases xn : nodes A i=0
      · exact Or.inl (Or.inl ⟨xn,G,H⟩)
      · rw [H,mul_zero,qres_clean] at RQ
        rw [H,mul_zero,three_h_clean a d v _ D.dn D.da] at RA
        have qb : Btwo a d (nodes A i)=0 :=
          (mul_eq_zero.mp ((div_eq_zero_iff.mp RQ).resolve_right (by norm_num))).resolve_left
            (neg_ne_zero.mpr (pow_ne_zero 2 xn))
        have la : Lthree a d (nodes A i)=0 :=
          (mul_eq_zero.mp ((div_eq_zero_iff.mp RA).resolve_right (by norm_num))).resolve_left
            (neg_ne_zero.mpr (pow_ne_zero 2 xn))
        exact (three_linear_quadratic_exclusion _ _ _ D.an D.dn ne qb la).elim
  · have X := O.off_support i G
    have ⟨Z,H⟩ := D.off i G
    rw [X,H,Z,three_q_off a d v _ D.vn] at RQ
    rw [X,H,Z,three_h_off a d v _ D.dn D.da D.vn] at RA
    have pair : (g A i-baseAmp a)*(g A i-v)=0 := by
      by_contra e
      have q := (div_eq_zero_iff.mp RQ).resolve_right (mul_ne_zero (by norm_num) D.vn)
      have p := (div_eq_zero_iff.mp RA).resolve_right (mul_ne_zero (by norm_num) D.vn)
      have p' : a+d=0 := (mul_eq_zero.mp ((mul_eq_zero.mp p).resolve_right e)).resolve_left D.an
      have q' : a-2*d=0 := (mul_eq_zero.mp ((mul_eq_zero.mp q).resolve_right e)).resolve_left
        (neg_ne_zero.mpr D.an)
      exact mul_ne_zero (by norm_num : (3:K)≠0) D.an (show 3*a=0 by linear_combination 2*p'+q')
    rcases mul_eq_zero.mp pair with f|f
    · have gg := sub_eq_zero.mp f
      have hh : h A i=0 := by rw [H,gg,sub_self,mul_zero,mul_zero]
      exact Or.inl (Or.inr (Or.inl ⟨X,gg,hh⟩))
    · have gg := sub_eq_zero.mp f
      have hh : h A i=threeGam a*(v-baseAmp a) := by
        rw [H,gg,←mul_assoc,div_mul_cancel₀ _ D.vn]
      exact Or.inr ⟨X,gg,hh⟩

/-- An actual one-off tableau with the independent-square shape cannot
have its first nonzero (Ag) at an off row. Works already at p8. -/
theorem independent_square_off_first_impossible (ha : StrictLower A) (sep : Separated A 4)
    {a lam : K} {i j : Fin s} (O : Origin A a i) (F : FirstH A a lam j)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A)
    (shape : IndependentShape A a lam i j) (off : g A j≠0) : False := by
  obtain ⟨d,v,D⟩ := case_three_calibration ha sep O F Q2 shape off
  by_cases e : d=2*a
  · exact case_three_no_exception ha sep O D e
  · have all := case_three_confined ha O D e
    apply clocks_not_covered_by_four sep ({0,a,d}:Finset K)
      ((Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp))))
    intro r
    rcases four_features_clocks (all r) with h|h|h <;> simp [h]

end RKCert.Paired.OneOff
