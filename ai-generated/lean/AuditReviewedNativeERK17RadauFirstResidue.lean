import RKCert.ReviewedNative.ERK17RadauFirstResidueNative

open Polynomial RKResearch.Certified.Graded
open RKResearch.Certified.Graded.NativeReciprocal
open RKResearch.Certified.ERK17 RKCert.ReviewedNative.WeightXEight

example {K : Type*} [Field K] [CharZero K] : RadauFirstGate K :=
  native_radau_first_gate_of_residue

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (Q N : K[X]) (u : K) (qn : Q≠0) (qd : Q.natDegree≤5)
    (nn : N≠0) (nd : N.natDegree=3) (root : N.eval u=0) (un : u≠0)
    (test : ∀ k : Fin 8, (primitive (X^k.val*(X*(Q*N)))).eval 1=0) :
    (primitive (X*Q)).eval u≠0 :=
  native_radau_first_gate_of_residue Q N u qn qd nn nd root un test

#print axioms scaledReciprocal_isRoot_iff
#print axioms clearedFirst_of_primitive_zero
#print axioms chosen_root_cut_of_integral_reciprocal
#print axioms integralReciprocal_mod11
#print axioms residue_chosen_root
#print axioms native_radau_first_gate_of_residue
