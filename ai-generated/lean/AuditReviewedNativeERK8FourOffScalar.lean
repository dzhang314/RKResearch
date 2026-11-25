import RKCert.ReviewedNative.ERK8FourOffScalar

open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

section

variable {K : Type*} [Field K] [CharZero K]

example {h x z theta k d e t gain : K}
    (D : CleanClocks h x z) (hk : k ≠ 0)
    (hs : theta * cleanE h x z = k * cleanNumer h x)
    (off : EarlyRows (moment (shape h x z theta k) h x z) d e h t)
    (clean : FirstCleanRows (moment (shape h x z theta k) h x z) e h gain) : False :=
  firstCleanAt4_contradiction D hk hs off clean

example {h x z theta k d e : K}
    (D : CleanClocks h x z) (hk : k ≠ 0)
    (hs : theta * cleanE h x z = k * cleanNumer h x)
    (off : EarlyRows (moment (shape h x z theta k) h x z) d e h 0) : False :=
  firstCleanAt5_contradiction D hk hs off

end

#print axioms RKResearch.Certified.Graded.MultiOff.FourOff8Scalar.firstCleanAt4_contradiction
#print axioms RKResearch.Certified.Graded.MultiOff.FourOff8Scalar.firstCleanAt5_contradiction
