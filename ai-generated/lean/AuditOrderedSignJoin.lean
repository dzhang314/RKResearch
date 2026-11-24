import RKCert.ReviewedNative.OrderedAlternationDegree

open Polynomial RKCert.ReviewedNative.FiniteOrderedSigns

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K[X]} {a b c : K} {m n : ℕ}
    (ab : a ≤ b) (bc : b ≤ c)
    (left : HasAlternationsOn P (Set.Ioo a b) m)
    (right : HasAlternationsOn P (Set.Ioo b c) n) :
    m + n ≤ P.natDegree :=
  (left.add_open right ab le_rfl bc).le_natDegree

#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.exists_alternating_subsequence
#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.AlternatingSamples.exists_join
#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.HasAlternationsOn.add_open
#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.HasAlternationsOn.le_natDegree
