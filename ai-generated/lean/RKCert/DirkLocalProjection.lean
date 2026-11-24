module
public import RKCert.DirkReversePivot
@[expose] public section
namespace RKCert.Paired.LocalProjection
open Polynomial RKCert.Endpoint RKCert.OneEscape Module
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

/-- Kill a chosen nonzero coordinate of a genuine local vector, retaining
all physical ambient coordinates to simplify grade-by-grade reasoning.
This is an oblique linear projection, not a new tableau of order p. -/
def kill (d:Vec K s) (h:Fin s) : Vec K s→ₗ[K]Vec K s :=
  LinearMap.id - (LinearMap.proj h).smulRight ((d h)⁻¹ • d)

theorem kill_eq (d z:Vec K s) (h:Fin s) : kill d h z=z-(z h/d h) • d := by
  ext i
  simp [kill,LinearMap.smulRight_apply,div_eq_mul_inv,mul_assoc]
@[simp] theorem kill_apply (d z:Vec K s) (h i:Fin s) :
    kill d h z i=z i-(z h/d h)*d i := by rw [kill_eq];rfl

theorem kill_self {d:Vec K s} {h:Fin s} (hd:d h≠0) : kill d h d=0 := by
  rw [kill_eq,div_self hd,one_smul,sub_self]

theorem kill_weighted (y d:Vec K s) (h:Fin s) (loc:∀i,d i≠0 → y i=y h) (v:Vec K s) (P:K[X]) :
    kill d h (weightedEval y v P)=weightedEval y (kill d h v) P := by
  ext i
  simp only [kill_apply,weightedEval_apply]
  by_cases hi:d i=0
  · simp [hi]
  · rw [loc i hi];ring

theorem kill_clock (y d:Vec K s) (h:Fin s) (loc:∀i,d i≠0 → y i=y h) (v:Vec K s) :
    kill d h (diag y v)=diag y (kill d h v) := by
  ext i
  simp only [kill_apply,diag_apply]
  by_cases hi:d i=0
  · simp [hi]
  · rw [loc i hi];ring

theorem kill_power (y d:Vec K s) (h:Fin s) (loc:∀i,d i≠0 → y i=y h) (v:Vec K s) (k:ℕ) :
    kill d h (((diag y)^k) v)=((diag y)^k) (kill d h v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
    rw [kill_clock y d h loc,ih]

theorem kill_chain (y d:Vec K s) (h:Fin s) (loc:∀i,d i≠0 → y i=y h) (dh:d h≠0)
    (w:Vec K s) (k:ℕ) : (chain (diag y) (K ∙ d) w k).map (kill d h) =
    chain (diag y) ⊥ (kill d h w) k := by
  induction k with
  | zero =>
    simp only [chain,Submodule.map_span,Set.image_singleton,kill_self dh]
    exact Submodule.span_singleton_eq_bot.mpr rfl
  | succ k ih =>
    rw [chain,Submodule.map_sup,ih,Submodule.map_span,Set.image_singleton,kill_power y d h loc,chain]

/-- The change in the primitive under projection is paid by precisely the
first genuine image of d. -/
theorem primitive_leak (N:Vec K s→ₗ[K]Vec K s) (d z:Vec K s) (h:Fin s) :
    (kill d h).comp N (kill d h z) - kill d h (N z) = -(z h/d h) • kill d h (N d) := by
  change kill d h (N (kill d h z))-kill d h (N z)=_
  rw [kill_eq d z h,map_sub,map_smul,map_sub,map_smul,neg_smul]
  abel

theorem preserves_sum (d z:Vec K s) (h:Fin s) (hd:row d 1=0) :
    row (kill d h z) 1=row z 1 := by
  change rowL (kill d h z) 1=rowL z 1
  rw [kill_eq,map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply]
  change row z 1-(z h/d h)*row d 1=row z 1
  rw [hd,mul_zero,sub_zero]

/-- Projection is causal in reversed *physical* order if its pivot is the
first surviving coordinate there. -/
theorem kill_causal (d:Vec K s) (h:Fin s) (pre:∀j,h < j → d j=0) (i:Fin s)
    (x y:Vec K s) (match':∀j,i≤j → x j=y j) : kill d h x i=kill d h y i := by
  rw [kill_apply,kill_apply,match' _ le_rfl]
  by_cases hi:i≤h
  · rw [match' _ hi]
  · rw [pre _ (lt_of_not_ge hi),mul_zero,mul_zero]

end
end RKCert.Paired.LocalProjection
