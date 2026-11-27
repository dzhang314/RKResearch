import RKCert.ReviewedNative.DIRKOrderTenEightDirtyScalar

open Lean.Grind
open RKResearch.Certified.Graded.EightDirtyCleanScalar

#check clean_diag_numerator_ne
#check exists_coeffs_of_localRead
#check no_clean_scalar_reads
#check no_anchored_quartics

#print axioms clean_diag_numerator_ne
#print axioms exists_coeffs_of_localRead
#print axioms no_clean_scalar_reads
#print axioms no_anchored_quartics

universe u

example {K : Type u} [Field K] (y : K) (f g : K×K×K) (hy : clock y=0)
    (h2 : (2:K)≠0) (h3 : (3:K)≠0) (h5 : (5:K)≠0) (h7 : (7:K)≠0)
    (hresultant : (62969:K)*(112249:K)≠0)
    (hf : f.1≠0 ∨ f.2.1≠0 ∨ f.2.2≠0) (hg : g.1≠0 ∨ g.2.1≠0 ∨ g.2.2≠0)
    (fLocal : localRead y f=0) (gLocal : localRead (1-y) g=0)
    (h0 : low f g-42*(7+42*rho y)*point y f*point (1-y) g=0)
    (h1 : high f g-y*low f g=0)
    (h2' : prim f g-(5+42*rho y)*low f g=0) : False :=
  no_anchored_quartics y f g hy h2 h3 h5 h7 hresultant hf hg fLocal gLocal h0 h1 h2'
