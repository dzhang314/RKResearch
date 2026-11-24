module
public import RKCert.ERKOrderNineCompactPrime
public import RKCert.ReviewedNative.GradedPrimitives
@[expose] public section

/-! # Scalar theorems consumed by the multi-off census

The imported legacy files co-locate arithmetic and Tableau declarations.
Only polynomial/scalar theorems are used here; the finite-field rows are
consumed from their checked objects, never replayed. -/
namespace RKResearch.Certified.Graded.MultiOff
open Polynomial
variable {K : Type*} [Field K]

theorem scalar_primitive (P : K[X]) : RKCert.Paired.primitive P=primitive P := by
  ext n
  cases n with
  | zero => rw [RKCert.Paired.primitive_coeff_zero, primitive_coeff_zero]
  | succ n => rw [RKCert.Paired.primitive_coeff_succ, primitive_coeff_succ]

/-- No distinct-root (5,6) physical scalar witness can satisfy both
the compatibility and terminal equations. This is only the scalar side:
the physical inputs themselves must still be earned by the census. -/
theorem six_on_witness_impossible [CharZero K] {h u v l : K}
    (inj : Function.Injective (![h,2-l-h-u-v,u,v] : Fin 4→K))
    (roots : ∀ i : Fin 4, (RKCert.Paired.lobattoPencil l).eval (![h,2-l-h-u-v,u,v] i)=0)
    (k : RKCert.Paired.sixOnK8 h u v l=0)
    (terminal : RKCert.Paired.sixOnTerminalProduct h u v l=0) : False := by
  exact RKCert.CompactResidue.sixOn_atlas_impossible (roots 0) (roots 2) (roots 3)
    (fun e => (by decide : (2:Fin 4)≠0) (inj e))
    (fun e => (by decide : (3:Fin 4)≠0) (inj e))
    (fun e => (by decide : (3:Fin 4)≠2) (inj e)) k terminal
end RKResearch.Certified.Graded.MultiOff
