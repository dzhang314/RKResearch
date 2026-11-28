module

public import RKCert.ReviewedNative.DIRK12MidpointReversePhysicalLow
public import RKCert.ReviewedNative.DIRK12MidpointReverseProfile
public import RKCert.ReviewedNative.DIRK12MidpointReverseGhost
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

/-! Native actual reverse primitives of the full real matrix through
grade four. The fourth entering reflected degree is paid on ghosts
only in this module; its full quartic live identities are separate. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DualSupport12 DIRK12MidpointForward
open DIRK12MidpointRealInterval DirectedRatBox
open scoped BigOperators Matrix

section Actual

variable (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)

local notation "P" => (zeroHead x f)
local notation "D" => (exactData x f)
local notation "Areal" => (Feed.tableau (assembled x f))
local notation "Breal" => (Feed.b (assembled x f))

include hx hf hx0 hf0

theorem assembled_scalar :
    ∀ j < 12, ((j+1:Nat):ℝ)*row Breal ((nodes Areal)^j)=1 :=
  ordinary_scalar_with_physical_weights hx hf hx0 hf0 Areal (assembled_real_nodes x f)

theorem assembled_reverse_ghost (g : Fin 4) (j : Fin 4) :
    mat (Matrix.transpose Areal) (moment Areal Breal (j.val+1))
      (DIRK12MidpointForward.hidden g)=0 := by
  have e := installed_is_five x f (groupedAmplitude x f)
  change assembled x f=Opening.fiveFeed x f (assembled x f).live at e
  rw [e]
  exact real_reverse_ghost_read x f _ _ _ _ hx hf hx0 hf0 g j

theorem reverse_grade1 : reverse Areal Breal 0=0 := by
  have h := assembled_geom x f hx hf
  have q := assembled_scalar x f hx hf hx0 hf0
  have ht : Breal terminal≠0 := h.bNZ 9
  have t0 : row Breal (1:V15 ℝ)=1 := by simpa using q 0 (by decide)
  have t1 : 2*row Breal (assembled x f).clocks=1 := by
    rw [←(assembled x f).nodes_tableau]
    simpa using q 1 (by decide)
  have e := (assembled x f).paid_adjoint ht t0 t1
  simp only [reverse,Nat.zero_add,Nat.cast_one,one_smul,moment_zero]
  rw [e]
  simp [DualSupport12.moment,reflected,(assembled x f).nodes_tableau]

theorem reverse_unscaled_low (j : Fin 3) :
    Physical.error P D j=Physical.expected P D j := by
  apply Physical.error_vector P D (assembled_geom x f hx hf)
    (assembled_scalar x f hx hf hx0 hf0) j
  intro g
  let k : Fin 4 := ⟨j.val,by omega⟩
  have z := assembled_reverse_ghost x f hx hf hx0 hf0 g k
  change mat (Matrix.transpose Areal) (moment Areal Breal (j.val+1))
    (DIRK12MidpointForward.hidden g)=0 at z
  have b0 : Breal (DIRK12MidpointForward.hidden g)=0 :=
    (assembled_geom x f hx hf).ghost0 g
  simp only [Physical.error,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change mat (Matrix.transpose Areal) (moment Areal Breal (j.val+1))
    (DIRK12MidpointForward.hidden g)-(((j.val+2:Nat):ℝ)⁻¹)*
    moment Areal Breal (j.val+2) (DIRK12MidpointForward.hidden g)=0
  rw [z]
  simp [DualSupport12.moment,b0]

omit hx hf hx0 hf0 in
theorem scaled_low (j : Fin 3) :
    reverse Areal Breal (j.val+1)=((j.val+2:Nat):ℝ) • Physical.error P D j := by
  have nz : ((j.val+2:Nat):ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  unfold reverse Physical.error
  rw [smul_sub,smul_smul,mul_inv_cancel₀ nz,one_smul]
  rfl

theorem reverse_grade2 : reverse Areal Breal 1=0 := by
  have h := scaled_low x f (0:Fin 3)
  change reverse Areal Breal 1=((2:Nat):ℝ) • Physical.error P D 0 at h
  rw [h,reverse_unscaled_low x f hx hf hx0 hf0]
  simp [Physical.expected]

theorem reverse_grade3 : reverse Areal Breal 2=(3:ℝ) • profileG x f := by
  have h := scaled_low x f (1:Fin 3)
  change reverse Areal Breal 2=((3:Nat):ℝ) • Physical.error P D 1 at h
  rw [h,reverse_unscaled_low x f hx hf hx0 hf0]
  norm_num [Physical.expected,profileG]

theorem reverse_grade4 :
    reverse Areal Breal 3=(4:ℝ) •
      ((3*d x f/2) • profileG x f+Seed.lambda (r x f) • profileH x f) := by
  have h := scaled_low x f (2:Fin 3)
  change reverse Areal Breal 3=((4:Nat):ℝ) • Physical.error P D 2 at h
  rw [h,reverse_unscaled_low x f hx hf hx0 hf0]
  norm_num [Physical.expected,profileG,profileH,data,exactData]

/-- These are the true reverse rows required by the late forward
rank-three argument, not a scalar interpolation proxy. -/
theorem reverse_low_silent (j : Fin 3) (m : Nat) (hm : m≤7) :
    row (reverse Areal Breal (j.val+1)) ((nodes Areal)^m)=0 := by
  fin_cases j
  · exact (by
      change row (reverse Areal Breal 1) ((nodes Areal)^m)=0
      rw [reverse_grade2 x f hx hf hx0 hf0]
      simp)
  · exact (by
      change row (reverse Areal Breal 2) ((nodes Areal)^m)=0
      rw [reverse_grade3 x f hx hf hx0 hf0]
      simp [actual_G_silent x f hx hf])
  · exact (by
      change row (reverse Areal Breal 3) ((nodes Areal)^m)=0
      rw [reverse_grade4 x f hx hf hx0 hf0]
      simp [actual_G_silent x f hx hf,actual_H_silent x f hx hf m hm])

end Actual
end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_grade1
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_grade2
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_grade3
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_grade4
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.reverse_low_silent
