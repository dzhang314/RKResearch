module

public import RKCert.DirkClockRetraction

@[expose] public section

/-! # The exact graded costs of a full clock retraction -/
namespace RKCert.Paired.PivotProjection.ClockRetraction
open RKCert.OneEscape
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {c : Vec K s} {U : Submodule K (Vec K s)}
variable (P : ClockRetraction c U)

def contractedOp (N : Vec K s →ₗ[K] Vec K s) : Vec K s →ₗ[K] Vec K s :=
  P.projection.comp (N.comp P.projection)

theorem contractedOp_causal {N : Vec K s →ₗ[K] Vec K s} {d : Vec K s}
    (ha : CausalDiag (Equiv.refl (Fin s)) N d) :
    CausalDiag (Equiv.refl (Fin s)) (P.contractedOp N) (P.diagonal*(d*P.diagonal)) :=
  causal_comp P.causal (causal_comp ha P.causal)

theorem contractedOp_on_projection (N : Vec K s →ₗ[K] Vec K s) (x : Vec K s) :
    P.contractedOp N (P.projection x)=
      P.projection (N x)-P.projection (N (x-P.projection x)) := by
  change P.projection (N (P.projection (P.projection x)))=_
  rw [P.idempotent]
  simp only [map_sub]
  abel

/-- Every extra term belongs to a projection of NC, CN, or NN on the
eliminated grade. In particular the contracted operator does not get to
claim a primitive/commutator identity on a shortened RK tableau. -/
theorem contractedOp_commutator_error (N : Vec K s →ₗ[K] Vec K s) (x : Vec K s) :
    commutatorR (P.contractedOp N) (diag c) (P.projection x) -
      P.projection (commutatorR N (diag c) x) =
    (P.projection (N (diag c x-P.projection (diag c x))) -
      P.projection (diag c (N (x-P.projection x)))) +
      P.projection (N (N (x-P.projection x))) +
      P.projection (N (N (P.projection x)-P.projection (N (P.projection x)))) := by
  have h₁ : diag c (P.contractedOp N (P.projection x)) =
      P.projection (diag c (N x))-P.projection (diag c (N (x-P.projection x))) := by
    rw [P.contractedOp_on_projection,map_sub,P.clock,P.clock]
  have h₂ : P.contractedOp N (diag c (P.projection x)) =
      P.projection (N (diag c x))-P.projection (N (diag c x-P.projection (diag c x))) := by
    rw [←P.clock,P.contractedOp_on_projection]
  have h₃ : P.contractedOp N (P.contractedOp N (P.projection x)) =
      P.projection (N (N x))-P.projection (N (N (x-P.projection x))) -
      P.projection (N (N (P.projection x)-P.projection (N (P.projection x)))) := by
    have hop : P.contractedOp N (P.projection x)=P.projection (N (P.projection x)) := by
      change P.projection (N (P.projection (P.projection x)))=_
      rw [P.idempotent]
    rw [hop,P.contractedOp_on_projection]
    have tri : P.projection (N (N (P.projection x))) =
        P.projection (N (N x))-P.projection (N (N (x-P.projection x))) := by
      simp only [map_sub]
      abel
    rw [tri]
  simp only [commutatorR,LinearMap.sub_apply,LinearMap.comp_apply,h₁,h₂,h₃,map_sub]
  abel

end
end RKCert.Paired.PivotProjection.ClockRetraction
