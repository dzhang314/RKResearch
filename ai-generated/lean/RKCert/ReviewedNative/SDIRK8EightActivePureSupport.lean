module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActivePureSupport

/-- The preimage of a column under an invertible-diagonal lower
triangular read vanishes before the first visible coordinate of that
column. This uses actual physical prefixes, not a trimmed tableau. -/
theorem preimage_zero_before {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (q : Fin n)
    (tri : ∀ i j, i < j → M i j = 0) (diag : ∀ i, M i i ≠ 0)
    (silent : ∀ i, i < q → M.mulVec v i = 0) : ∀ i, i < q → v i = 0 := by
  have aux (k : ℕ) : ∀ i : Fin n, i.val = k → i < q → v i = 0 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hiq
      have sm : M.mulVec v i = M i i * v i := by
        unfold Matrix.mulVec dotProduct
        apply Finset.sum_eq_single i
        · intro j _ hji
          change M i j * v j = 0
          rcases lt_or_gt_of_ne hji with hj | hj
          · have hjk := Fin.lt_def.mp hj
            rw [hi] at hjk
            rw [ih j.val hjk j rfl (lt_trans hj hiq), mul_zero]
          · rw [tri i j hj, zero_mul]
        · simp
      exact (mul_eq_zero.mp (sm.symm.trans (silent i hiq))).resolve_left (diag i)
  exact fun i hi => aux i.val i rfl hi

/-- The scalar portion of a pure supported preimage of grade two
is identically zero if it vanishes at three actual distinct clocks. -/
theorem quadratic_three_zeros {K : Type*} [Field K]
    (a b c p₀ p₁ p₂ : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : p₀+p₁*a+p₂*a^2=0) (hb : p₀+p₁*b+p₂*b^2=0)
    (hc : p₀+p₁*c+p₂*c^2=0) : p₀=0 ∧ p₁=0 ∧ p₂=0 := by
  have f₀ : (a-b)*(p₁+p₂*(a+b))=0 := by linear_combination ha-hb
  have f₁ : (a-c)*(p₁+p₂*(a+c))=0 := by linear_combination ha-hc
  have z₀ := (mul_eq_zero.mp f₀).resolve_left (sub_ne_zero.mpr hab)
  have z₁ := (mul_eq_zero.mp f₁).resolve_left (sub_ne_zero.mpr hac)
  have f₂ : p₂*(b-c)=0 := by linear_combination z₀-z₁
  have z₂ := (mul_eq_zero.mp f₂).resolve_right (sub_ne_zero.mpr hbc)
  rw [z₂, zero_mul, add_zero] at z₀
  simp [z₂,z₀] at ha
  exact ⟨ha,z₀,z₂⟩

/-- Three passive quadratic-zero predecessors would force the
preimage of an actually supported pure-four coordinate to vanish.
Only the nonzero quadratic defect at stage one is used. -/
theorem supportedPreimageEarly {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v c g : Fin n → K) (q f a b d : Fin n)
    (p₀ p₁ p₂ α : K)
    (tri : ∀ i j, i < j → M i j = 0) (diag : ∀ i, M i i ≠ 0)
    (silent : ∀ i, i < q → M.mulVec v i = 0)
    (reads : ∀ i, v i = p₀+p₁*c i+p₂*(c i)^2+α*g i)
    (hf : f < q) (ha : a < q) (hb : b < q) (hd : d < q)
    (hgf : g f ≠ 0) (hga : g a = 0) (hgb : g b = 0) (hgd : g d = 0)
    (hab : c a ≠ c b) (had : c a ≠ c d) (hbd : c b ≠ c d) :
    ∀ i, v i = 0 := by
  have H := preimage_zero_before M v q tri diag silent
  have ea := reads a; rw [H a ha,hga,mul_zero,add_zero] at ea
  have eb := reads b; rw [H b hb,hgb,mul_zero,add_zero] at eb
  have ed := reads d; rw [H d hd,hgd,mul_zero,add_zero] at ed
  obtain ⟨p0,p1,p2⟩ := quadratic_three_zeros _ _ _ _ _ _ hab had hbd
    ea.symm eb.symm ed.symm
  have ef := reads f
  rw [H f hf,p0,p1,p2,zero_mul,zero_mul,zero_add,zero_add,zero_add] at ef
  have hα := (mul_eq_zero.mp ef.symm).resolve_right hgf
  intro i
  simp [reads,p0,p1,p2,hα]

/-- Scalar kernel of the four paid quartic moment tests. The proof
uses fixed rational identities in characteristic zero, not Gaussian
root sorting or positivity. -/
theorem quartic_kernel {K : Type*} [Field K] [CharZero K]
    (s₀ s₁ s₂ s₃ s₄ : K)
    (m₀ : s₀+s₁/2+s₂/3+s₃/4+s₄/5=0)
    (m₁ : s₀/2+s₁/3+s₂/4+s₃/5+s₄/6=0)
    (m₂ : s₀/3+s₁/4+s₂/5+s₃/6+s₄/7=0)
    (m₃ : s₀/4+s₁/5+s₂/6+s₃/7+s₄/8=0) :
    ∀ x : K, s₀+s₁*x+s₂*x^2+s₃*x^3+s₄*x^4 =
      (s₄/70)*(70*x^4-140*x^3+90*x^2-20*x+1) := by
  have h₀ : s₀=s₄/70 := by
    linear_combination 16*m₀-120*m₁+240*m₂-140*m₃
  have h₁ : s₁= -2*s₄/7 := by
    linear_combination -120*m₀+1200*m₁-2700*m₂+1680*m₃
  have h₂ : s₂= 9*s₄/7 := by
    linear_combination 240*m₀-2700*m₁+6480*m₂-4200*m₃
  have h₃ : s₃= -2*s₄ := by
    linear_combination -140*m₀+1680*m₁-4200*m₂+2800*m₃
  intro x
  rw [h₀,h₁,h₂,h₃]
  ring

/-- The ordinary and reverse nodal numerators give the scalar
product at each actual active stage. This does not divide by a
possibly zero cubic defect or by the associated Legendre value. -/
theorem weightedNodalProduct {K : Type*} [CommRing K]
    (D b w h L T σ P : K)
    (hw : D*w=T) (hL : T*h=σ*L) (hp : b*h=P*w) :
    σ*(L*b*D)=P*T^2 := by
  linear_combination -b*D*hL + D*T*hp + P*T*hw

/-- A constant reverse nodal numerator and a constant Legendre
quotient translate the physical affine reverse read to the exact
ordinary signed weighted-defect numerator. -/
theorem constantNodalAffine {K : Type*} [CommRing K]
    (D b w h L x P₀ P₁ q τ : K)
    (hw : D*w=τ) (hL : L=q*h) (hp : b*h=(P₀+P₁*x)*w) :
    L*b*D=q*τ*(P₀+P₁*x) := by
  linear_combination b*D*hL + q*D*hp + q*(P₀+P₁*x)*hw

#print axioms preimage_zero_before
#print axioms supportedPreimageEarly
#print axioms quartic_kernel
#print axioms weightedNodalProduct
#print axioms constantNodalAffine

end RKCert.ReviewedNative.SDIRK8EightActivePureSupport
