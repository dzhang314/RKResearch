import RKCert.ReviewedNative.MixedTwoTerminal

open RKResearch.Certified.MixedTwoTerminal

example {K : Type*} [Field K] [CharZero K] (a b u v : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hu : u ≠ 0)
    (h0 : u*prim0 a b a+v*prim0 a b b=0)
    (h1 : u*prim1 a b a+v*prim1 a b b=0) : False :=
  no_two_terminal_cancellation a b u v ha hb hab hu h0 h1

#print axioms no_two_terminal_cancellation
