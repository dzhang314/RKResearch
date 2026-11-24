module

public import RKCert.ReviewedNative.ERKGradeEightFrontier
public import RKCert.ReviewedNative.ERKGradeEightCubicChronology
public import RKCert.ReviewedNative.OrientedCubicMoment

@[expose] public section

/-! # The ordered grade-eight cubic branch closes -/
namespace RKResearch.Certified.Graded
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- In the actual thin grade-eight chart, no third-grade vector can escape
the intrinsic core. The proof evaluates a strictly positive cubic square
at the same nonzero physical clock where causality forces it to vanish. -/
theorem grade_eight_third_inside_core (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b p) (pay : 16≤p) {r : ℕ} {U : Submodule K (Fin (s+1)→K)}
    {w : Fin (s+1)→K} (H : FlatClockHead A 5 3 r U w) : zeroSpace A 3 ≤ U := by
  intro v hv
  by_contra out
  obtain ⟨stable,P,pn,pd,profile⟩ := grade_eight_grade_three_profile H hv out
  obtain ⟨k,nk,e⟩ := grade_eight_cubic_chronology ha ho pay H hv stable P pn pd profile
  have positive := primitive_x_cubic_square_pos P pd pn nk
  rw [formalPrimitive_eq_native,e] at positive
  exact (lt_irrefl _ positive)

/-- The only remaining flat grade-eight branches: a genuine grade-four
flat quartic chart, or a rank-three core equal to F4 and already closed
under pointwise multiplication. -/
theorem grade_eight_remaining_two_cases (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b p) (pay : 16≤p) (cap : finrank K (zeroSpace A 8)≤8) :
    (finrank K (zeroSpace A 4)=4 ∧ ∃ r U w, FlatClockHead A 4 4 r U w) ∨
    ∃ r U w, FlatClockHead A 5 3 r U w ∧ 2≤r ∧ finrank K U=3 ∧
      finrank K (zeroSpace A 3)=2 ∧ zeroSpace A 4=U ∧ ∀ u∈U, ∀ v∈U, u*v∈U := by
  rcases grade_eight_grade_four_split ha ho pay cap with f4 | quartic
  · obtain ⟨r,U,w,r2,f5,H⟩ := grade_eight_thin_head ha ho pay cap
    have e := grade_eight_core_eq_grade_four ha ho pay H r2 f5 f4
      (grade_eight_third_inside_core ha ho pay H)
    have dim : finrank K U=3 := e ▸ f4
    have f3lo : 2≤finrank K (zeroSpace A 3) := zeroSpace_finrank ha ho (n:=2) (by omega)
    have sep := explicit_coeff_separated ha ho (q:=8) pay
    have lo := zeroSpace_rank_interval_of_separation ha sep (j:=3) (d:=1) (by decide) (by decide)
    change finrank K (zeroSpace A 3)+1≤finrank K (zeroSpace A 4) at lo
    refine Or.inr ⟨r,U,w,H,r2,dim,by omega,e,?_⟩
    have band : zeroSpace A (4+4)≤chain (diag (nodes A)) U w (r+3) := (H.flags 3 (by decide)).le
    exact fun u hu v hv => HeadFiber.core_mul (j:=4) (k:=4) H.coreStable e.ge H.extraSites band hu (e.ge hv)
  · exact Or.inl quartic

end RKResearch.Certified.Graded
