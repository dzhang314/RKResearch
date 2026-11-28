module

public import RKCert.ReviewedNative.DIRK12Midpoint21Checks
import Mathlib.Tactic.Ring

@[expose] public section

/-! A compact, actual sufficient flag for uniform midpoint branches.
A generator \(h_m^{2k}c^j\) has grade \(2k+j\) and \(k≥1\).
The only arithmetic action is the verified scalar primitive decomposition;
same-branch multiplication, clock-lift, and products are structural. -/
namespace RKResearch.Certified.DIRK12Midpoint21

open RKResearch Graded
open scoped Matrix BigOperators

def modeSet (d : Nat) : Set V :=
  {v | ∃ k j : Nat, 1≤k ∧ 2*k+j≤d ∧ v=gen k j}

noncomputable def band (d : Nat) : Submodule ℚ V :=
  Submodule.span ℚ (modeSet d)

theorem gen_mem {d k j : Nat} (hk : 1≤k) (h : 2*k+j≤d) :
    gen k j ∈ band d :=
  Submodule.subset_span ⟨k,j,hk,h,rfl⟩

theorem tail_mem (j : Nat) : tail j∈band (j+1) := by
  unfold tail
  apply Submodule.sum_mem
  intro r hr
  have h := Finset.mem_range.mp hr
  exact (band _).smul_mem _ (gen_mem (by omega) (by omega))

theorem gen_act_factor (k j : Nat) :
    mat matrix (gen k j)=hSq^k*mat matrix (clock^j) := by
  funext i
  simp only [gen,mat_apply,Matrix.mulVec_apply_eq_sum,Pi.mul_apply,Pi.pow_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rcases block i l with e|e
  · simp [e]
  · rw [e]
    ring

theorem gen_action (k j : Nat) (hj : j+1 < 12) :
    ((j+1:Nat):ℚ) • mat matrix (gen k j)=gen k (j+1)+
      ∑ r ∈ Finset.range ((j+1)/2), coeff j r • gen (k+(r+1)) (j+1-2*(r+1)) := by
  have sc (v : V) : ((j+1:Nat):ℚ) • (hSq^k*v)=hSq^k*(((j+1:Nat):ℚ) • v) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply]
    ring
  rw [gen_act_factor,sc,normal_read j hj,mul_add,tail,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  funext i
  simp only [gen,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.pow_apply,pow_add]
  ring

theorem action_gen_mem {d : Nat} (hd : d+1 < 12) (k j : Nat)
    (hk : 1≤k) (hj : 2*k+j≤d) : mat matrix (gen k j)∈band (d+1) := by
  have e : ((j+1:Nat):ℚ) • mat matrix (gen k j)∈band (d+1) := by
    rw [gen_action k j (by omega)]
    apply (band _).add_mem (gen_mem hk (by omega))
    apply Submodule.sum_mem
    intro r hr
    have h := Finset.mem_range.mp hr
    exact (band _).smul_mem _ (gen_mem (by omega) (by omega))
  have q := (band (d+1)).smul_mem (((j+1:Nat):ℚ)⁻¹) e
  rw [smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega)),one_smul] at q
  exact q

theorem band_stepA {d : Nat} (hd : d+1 < 12) {v : V} (hv : v∈band d) :
    mat matrix v∈band (d+1) := by
  have incl : band d≤(band (d+1)).comap (mat matrix) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,j,hk,hj,rfl⟩
    exact action_gen_mem hd k j hk hj
  exact incl hv

theorem clock_lift_gen (k j : Nat) : clock*gen k j=gen k (j+1) := by
  unfold gen
  rw [pow_succ]
  ring

theorem band_stepC {d : Nat} {v : V} (hv : v∈band d) :
    nodes matrix*v∈band (d+1) := by
  rw [node_eq]
  have incl : band d≤(band (d+1)).comap (diag clock) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,j,hk,hj,rfl⟩
    change clock*gen k j∈band (d+1)
    rw [clock_lift_gen]
    exact gen_mem hk (by omega)
  exact incl hv

theorem gen_product (k j l n : Nat) : gen k j*gen l n=gen (k+l) (j+n) := by
  unfold gen
  rw [pow_add,pow_add]
  ring

theorem band_mul {d e : Nat} {v w : V} (hv : v∈band d) (hw : w∈band e) :
    v*w∈band (d+e) := by
  have first : ∀ q∈modeSet e, v*q∈band (d+e) := by
    rintro _ ⟨l,n,hl,hn,rfl⟩
    have incl : band d≤(band (d+e)).comap (LinearMap.mulLeft ℚ (gen l n)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k,j,hk,hj,rfl⟩
      change gen l n*gen k j∈band (d+e)
      rw [gen_product]
      exact gen_mem (by omega) (by omega)
    have q := incl hv
    change gen l n*v∈band (d+e) at q
    rwa [mul_comm] at q
  have incl : band e≤(band (d+e)).comap (LinearMap.mulLeft ℚ v) :=
    Submodule.span_le.mpr first
  exact incl hw

theorem band_primitive (j : Nat) (hj : j+1 < 12) :
    ((j+1:Nat):ℚ) • mat matrix ((nodes matrix)^j)-(nodes matrix)^(j+1)∈band (j+1) := by
  rw [node_eq,normal_read j hj]
  have e : clock^(j+1)+tail j-clock^(j+1)=tail j := by ring
  rw [e]
  exact tail_mem j

theorem band_silent {d : Nat} (hd : d < 12) {v : V} (hv : v∈band d) :
    row weights v=0 := by
  have incl : band d≤(row weights).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,j,hk,hj,rfl⟩
    exact monomial_silent k j hk (by omega)
  exact incl hv

noncomputable def lowFlags : SufficientFlags 12 matrix weights where
  band := band
  stepA := by intro d hd v hv; exact band_stepA hd hv
  stepC := by intro d hd v hv; exact band_stepC hv
  mulBand := by intro d e hd v w hv hw; exact band_mul hv hw
  primitive := band_primitive
  silent := by intro d hd v hv; exact band_silent hd hv
  scalar := fun d hd => by rw [node_eq]; exact scalar_paid d hd

theorem rational_order_twelve : HasOrder 12 matrix weights :=
  lowFlags.hasOrder

end RKResearch.Certified.DIRK12Midpoint21

#print axioms RKResearch.Certified.DIRK12Midpoint21.gen_action
#print axioms RKResearch.Certified.DIRK12Midpoint21.rational_order_twelve
