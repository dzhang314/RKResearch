module

public import RKCert.ReviewedNative.PaidStageAppend

@[expose] public section

/-!
# A physical null perturbation of a low-pure stage

The old numerical row may consume a low-grade-null contrast. Its first
possible error is then entirely unary and is exactly an old actual read.
This can enlarge the available polynomial responses without adding a
separate stage for the contrast.
-/
namespace RKResearch.Certified.TwoDonorDense

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
variable {A : Matrix ι ι K} {q : ℕ} {D : Matrix (Fin (q+1)) ι K}

/-- A perturbation killing all old trees through `q` leaves the actual
new row pure through `q+1`. -/
theorem null_perturbation_paid (hD : IsDecoder A q D) (x γ : K) (h : ι → K)
    (hn : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q → h ⬝ᵥ normalized A t = 0) :
    PaidShiftedJet A (pureFeed D x γ+h) x γ q := by
  intro t ht
  rw [add_dotProduct, hn t ht, add_zero]
  exact pureFeed_eval hD x γ t (by omega)

/-- At the first newly possible error, the childwise construction
forces a single unary error and no inaccurate branch product. -/
theorem null_perturbation_firstExcess (hD : IsDecoder A q D) (x γ : K) (h : ι → K)
    (hq : 1 ≤ q)
    (hn : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q → h ⬝ᵥ normalized A t = 0)
    (t u : FiniteRootedTree) (ht : ((t ◂ u).order : ℕ) ≤ q+2) :
    normalized (appendStage A (pureFeed D x γ+h) γ) (t ◂ u) (Sum.inr PUnit.unit) =
      x^(((t ◂ u).order : ℕ)-1) +
        (if (u.order : ℕ) ≤ q then 0 else (u.order : K)*(h ⬝ᵥ normalized A u)) := by
  let v := pureFeed D x γ+h
  let B := appendStage A v γ
  let i : ι ⊕ PUnit := Sum.inr PUnit.unit
  have hpay : PaidShiftedJet A v x γ q := null_perturbation_paid hD x γ h hn
  have hp : PureAt B i (q+1) := paid_append_pure hq hpay
  have hc : clocks B i = x := paid_append_clock hq hpay
  have hT := t.order.pos
  have hU := u.order.pos
  have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
  have hu : (u.order : ℕ) ≤ q+1 := by omega
  have htm : (t.order : ℕ) ≤ q+1 := by omega
  have he : ((t ◂ u).order : ℕ)-1 = ((t.order : ℕ)-1)+(u.order : ℕ) := by omega
  have hnu : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  change normalized B (t ◂ u) i = _
  rw [normalized_join]
  simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul]
  rw [hp t htm,hc]
  have hv : (B *ᵥ normalized B u) i =
      x^(u.order : ℕ)/(u.order : K) + h ⬝ᵥ normalized A u := by
    change (appendStage A v γ *ᵥ normalized B u) (Sum.inr PUnit.unit) = _
    rw [append_mulVec_new, show normalized B u ∘ Sum.inl = normalized A u by
      exact append_normalized_old A v γ u, show normalized B u (Sum.inr PUnit.unit) =
      x^((u.order : ℕ)-1) by rw [← hc]; exact hp u hu]
    rw [show v = pureFeed D x γ+h by rfl,add_dotProduct,pureFeed_eval hD x γ u hu]
    ring
  rw [hv,he,pow_add]
  by_cases hsmall : (u.order : ℕ) ≤ q
  · rw [if_pos hsmall, hn u hsmall,add_zero,add_zero]
    rw [mul_div_cancel₀ _ hnu]
  · have hzero : (t.order : ℕ)-1=0 := by omega
    rw [if_neg hsmall,hzero,pow_zero,one_mul,one_mul,mul_add,mul_div_cancel₀ _ hnu]

#print axioms null_perturbation_paid
#print axioms null_perturbation_firstExcess

end RKResearch.Certified.TwoDonorDense
