import Lean.Elab.Tactic.Omega

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackPortable

/-- Integral coefficient determinant for the two cleared nodal
primitives. After the nonzero node powers are divided in a field,
their factors are 2v-u and 5v-3u; their coefficient rows are
unimodular. This portable lemma checks the exact integer part. -/
theorem primitive_pair_determinant : (-1 : Int)*5 - 2*(-3)=1 := by decide

theorem primitive_pair_integer (u v : Int)
    (h0 : 2*v-u=0) (h1 : 5*v-3*u=0) : u=0 ∧ v=0 := by omega

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackPortable
open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackPortable
#print axioms primitive_pair_determinant
#print axioms primitive_pair_integer
