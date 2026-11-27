module

public import RKCert.ReviewedNative.RowAnnihilator
public import RKCert.Research.SDIRKSevenPairedClean
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar and rank gates for a seven-active two-ghost chart -/

namespace RKResearch.Certified.SDIRKSevenTwoGhostScalar
open Module Graded Reverse
open SDIRKSevenPairedClean
noncomputable section

variable {K : Type*} [Field K]

/-- An isotropic defect space in the orthogonal complement of a
four-dimensional paid space on seven active coordinates has rank at most
one. The injective diagonal weights are the only coefficient hypothesis. -/
theorem seven_active_rank {b : Fin 7→K} (hb : ∀ i,b i≠0)
    {P W : Submodule K (Fin 7→K)} (p : finrank K P=4)
    (dis : Disjoint P W) (orth : W.map (diag b) ≤ annih (P⊔W)) :
    finrank K W≤1 := by
  let e : (Fin 7→K) ≃ₗ[K] (Fin 7→K) := LinearEquiv.ofBijective (diag b) ⟨
    fun x y h => funext fun i => by
      have ei := congrFun h i
      simp only [diag_apply] at ei
      exact mul_left_cancel₀ (hb i) ei,
    fun x => ⟨fun i => x i/b i, funext fun i => by
      simp only [diag_apply,mul_comm (b i)]
      exact div_mul_cancel₀ _ (hb i)⟩⟩
  have hm := e.finrank_map_eq W
  change finrank K (W.map (diag b))=finrank K W at hm
  have hs := Submodule.finrank_sup_add_finrank_inf_eq P W
  rw [dis.eq_bot,finrank_bot,add_zero,p] at hs
  have ha := finrank_annih (P⊔W)
  rw [Fintype.card_fin] at ha
  have hl := Submodule.finrank_mono orth
  omega

omit [Field K] in
theorem gram_kernel {R : Type*} [CommRing R] {a b c : R} (h : a*c-b^2=0) :
    a*(-b)+b*a=0 ∧ b*(-b)+c*a=0 := by
  constructor
  · ring
  · linear_combination h

/-- The even-radius solve in the centered symmetric arithmetic chart
never loses its affine coefficient over the rationals. -/
theorem centered_radius_pivot {A B r s : ℚ} (hb : B≠0)
    (h : A*momNum r s-B*momDen r s=0) :
    A*(s/3-1/5)-B*(s-1/3)≠0 := by
  intro d
  by_cases a : A=0
  · rw [a,zero_mul,zero_sub] at h d
    have g : B*(s-1/3)=0 := by linear_combination -d
    have s' : s=1/3 := sub_eq_zero.mp ((mul_eq_zero.mp g).resolve_left hb)
    rw [s'] at h
    have z : B*(4/45)=0 := by
      unfold momDen at h
      linear_combination -h
    exact (mul_ne_zero hb (by norm_num)) z
  · let η := B/A
    have e : A*η=B := by dsimp [η]; rw [mul_comm A,div_mul_cancel₀ _ a]
    have m : A*(momNum s η-momDen s η*r)=0 := by
      simp only [momDen,momNum] at h ⊢
      linear_combination h-(1/5-(r+s)/3+r*s)*e
    have p : momDen s η≠0 := moment_pivot ((mul_eq_zero.mp m).resolve_left a)
    have g : A*momDen s η=0 := by
      unfold momDen
      linear_combination -d+(s-1/3)*e
    exact (mul_ne_zero a p) g

theorem parity_det (a b m₀ m₂ m₄ : ℚ) :
    (a^2*m₀+b^2*m₂)*(a^2*m₂+b^2*m₄)-(2*a*b*m₂)^2 =
      a^4*m₀*m₂+a^2*b^2*(m₀*m₄-3*m₂^2)+b^4*m₂*m₄ := by ring

/-- The top three residue coefficients of multiplication by 1,X,X²
reduce the affine two-zero Gram determinant to this compact quadratic. -/
theorem crt_gram_det (s p u₄ v₀ v₁ : ℚ) :
    v₁*(u₄+s*v₀+(s^2-p)*v₁)-(v₀+s*v₁)^2 =
      v₁*u₄-v₀^2-s*v₀*v₁-p*v₁^2 := by ring

end
end RKResearch.Certified.SDIRKSevenTwoGhostScalar
