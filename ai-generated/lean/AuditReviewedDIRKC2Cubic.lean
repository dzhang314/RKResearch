import RKCert.ReviewedNative.DIRKC2GradeSixHead
open RKResearch RKResearch.Certified.Graded
open scoped Matrix
#print axioms zeroSpace_three_of_C2
#print axioms dirk_grade_three_of_C2
#print axioms dirk_grade_six_C2_early_cubic_profile

example {ι : Type*} [Fintype ι] (A : Matrix ι ι (ℤ × ℤ))
    (h : monomialStageDefect A 1=0) :
    zeroSpace A 3 = (ℤ × ℤ) ∙ monomialStageDefect A 2 := zeroSpace_three_of_C2 A h
