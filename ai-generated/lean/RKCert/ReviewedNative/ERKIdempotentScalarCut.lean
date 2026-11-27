module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.Ring

@[expose] public section

/-! An idempotent scalar sees only its own coefficient component,
including through every ordinary rooted-tree recurrence. -/

namespace RKResearch.Certified.ERKIdempotentScalarCut
open RKResearch FiniteRootedTree
open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

def cond (A : Matrix ι ι R) (b : ι→R) (t : FiniteRootedTree) : R :=
  (t.factorial:R)*(b ⬝ᵥ Φ t A)

omit [Fintype ι] in
theorem cut_mul {e : R} (he : e*e=e) (v w : ι→R) :
    e • (v*w) = (e•v)*(e•w) := by
  funext j
  simp only [Pi.smul_apply,Pi.mul_apply,smul_eq_mul]
  calc
    e*(v j*w j) = (e*e)*(v j*w j) := by rw [he]
    _ = _ := by ring

theorem cut_mulVec {e : R} (he : e*e=e) (A : Matrix ι ι R) (v : ι→R) :
    e•(A *ᵥ v) = (e•A) *ᵥ (e•v) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, he]

theorem cut_Φ {e : R} (he : e*e=e) {A B : Matrix ι ι R}
    (hA : e•A=e•B) (t : FiniteRootedTree) :
    e•Φ t A = e•Φ t B := by
  induction t with
  | leaf => rfl
  | butcherProduct u v hu hv =>
    change e•(Φ u A * (A *ᵥ Φ v A)) = e•(Φ u B * (B *ᵥ Φ v B))
    simp only [cut_mul he,cut_mulVec he,hu,hv,hA]

theorem cut_condition {e : R} (he : e*e=e) {A B : Matrix ι ι R} {b w : ι→R}
    (hA : e•A=e•B) (hb : e•b=e•w) (t : FiniteRootedTree) :
    e*cond A b t = e*cond B w t := by
  have h (U : Matrix ι ι R) (v : ι→R) :
      e*cond U v t = (t.factorial:R)*((e•v) ⬝ᵥ (e•Φ t U)) := by
    simp only [cond,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    rw [←mul_assoc e e,he]
    ring
  rw [h A b,h B w,hb,cut_Φ he hA]

theorem cut_condition_self {e : R} {A : Matrix ι ι R} {b : ι→R}
    (hb : e•b=b) (t : FiniteRootedTree) :
    e*cond A b t=cond A b t := by
  have h : (e•b) ⬝ᵥ Φ t A = e*(b ⬝ᵥ Φ t A) := by rw [smul_dotProduct,smul_eq_mul]
  rw [hb] at h
  rw [cond,←mul_assoc,mul_comm e, mul_assoc,←h]

theorem scale_integer_condition (M : Matrix ι ι ℤ) (v : ι→ℤ) (d : R) (t : FiniteRootedTree) :
    cond (d • M.map (Int.castRingHom R)) (d • ((Int.castRingHom R) ∘ v)) t =
      ((cond M v t:ℤ):R)*d^(t.order:ℕ) := by
  let f := Int.castRingHom R
  have h : f (cond M v t) = cond (M.map f) (f ∘ v) t := by
    simp only [cond,map_mul,map_natCast,RingHom.map_dotProduct,RKResearch.map_Φ]
  change cond (d • M.map f) (d • (f ∘ v)) t = f (cond M v t)*d^(t.order:ℕ)
  rw [h]
  have hpos := t.order.pos
  have hs : (t.order:ℕ) = (t.order:ℕ)-1+1 := by omega
  simp only [cond,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  conv_rhs => rw [hs,pow_succ]
  ring

theorem scaled_order_value (M : Matrix ι ι ℤ) (v : ι→ℤ) (t : FiniteRootedTree)
    (D : ℤ) (d : R) (h : cond M v t = D^(t.order:ℕ)) :
    cond (d • M.map (Int.castRingHom R)) (d • ((Int.castRingHom R) ∘ v)) t =
      ((D:R)*d)^(t.order:ℕ) := by
  rw [scale_integer_condition,h,Int.cast_pow,←mul_pow]

theorem scaled_tenth_residual (M : Matrix ι ι ℤ) (v : ι→ℤ) (t : FiniteRootedTree)
    (D Q N : ℤ) (d : R) (hs : (t.order:ℕ)=10)
    (h : Q*cond M v t=(Q+N)*D^10) :
    (Q:R)*(cond (d • M.map (Int.castRingHom R)) (d • ((Int.castRingHom R) ∘ v)) t -
        ((D:R)*d)^10) = (N:R)*((D:R)*d)^10 := by
  rw [scale_integer_condition,hs]
  have H := congrArg (Int.castRingHom R) h
  change (((Q*cond M v t:ℤ):R))=((((Q+N)*D^10:ℤ):R)) at H
  simp only [Int.cast_mul,Int.cast_add,Int.cast_pow] at H
  calc
    _ = ((Q:R)*((cond M v t:ℤ):R))*d^10-(Q:R)*((D:R)*d)^10 := by ring
    _ = _ := by rw [H,mul_pow]; ring

end RKResearch.Certified.ERKIdempotentScalarCut
