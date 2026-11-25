module

public import RKCert.ReviewedNative.GradedPrefix
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Native row order characterizes clean physical receivers at clock one

Uses all reviewed (not just bushy) trees. The forward direction does not
need the clock-one hypothesis, strictness, a field, or division. -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]
variable {A : Matrix ι ι R} {i : ι} {q : ℕ}

private theorem normTree_one_of_row_hasOrder (h : HasOrder q A (A i))
    (t : FiniteRootedTree) (ht : (t.order:ℕ)≤q+1) : normTree A t i=1 := by
  induction t with
  | leaf => simp
  | butcherProduct t u ih _ =>
    have b := t.order.pos
    have c := u.order.pos
    simp only [order,PNat.add_coe] at ht
    have left := ih (by omega)
    have right := h u (by omega)
    have prod : normTree A (t ◂ u) i=
        normTree A t i * ((u.factorial:R)*(A i ⬝ᵥ Φ u A)) := by
      simp only [normTree,forestFactorial,factorial,Φ,Pi.smul_apply,smul_eq_mul,
        PNat.mul_coe,Nat.cast_mul,Pi.mul_apply,Matrix.mulVec]
      ac_rfl
    rw [prod,left,right,one_mul]

theorem zeroSpace_at_row_hasOrder (h : HasOrder q A (A i)) :
    ∀ x∈zeroSpace A q,x i=0 := by
  let V := LinearMap.ker (LinearMap.proj i : (ι→R) →ₗ[R] R)
  have into : zeroSpace A q≤V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,u,eq,ht,rfl⟩
    apply LinearMap.mem_ker.mpr
    change normTree A t i-normTree A u i=0
    rw [normTree_one_of_row_hasOrder h t ht,normTree_one_of_row_hasOrder h u (eq ▸ ht),sub_self]
  exact fun _ hx=>LinearMap.mem_ker.mp (into hx)

theorem row_hasOrder_of_clean_clock_one (one : nodes A i=1)
    (clean : ∀x∈zeroSpace A q,x i=0) : HasOrder q A (A i) := by
  intro t ht
  have z : (t.factorial:R)*(A*ᵥΦ t A) i=(nodes A i)^(t.order:ℕ) :=
    sub_eq_zero.mp (clean _ (zeroSpace_mono A ht (rootStageResidual_mem A t)))
  simpa only [one, one_pow, Matrix.mulVec] using z

theorem row_hasOrder_iff_clean_clock_one (one : nodes A i=1) :
    HasOrder q A (A i) ↔ ∀x∈zeroSpace A q,x i=0 :=
  ⟨zeroSpace_at_row_hasOrder,row_hasOrder_of_clean_clock_one one⟩

end RKResearch.Certified.Graded
