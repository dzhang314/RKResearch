module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

/-! # General finite-rank bookkeeping for a two-seed no-plateau input

The operator-specific forcing proof is an explicit argument. Neither this
module nor its theorem types involve a Runge–Kutta method or stage order. -/
namespace RKCert.ReviewedNative.RankFlags
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If equality of two successive spaces would trap both seeds and make
the lower space invariant, forcing the specifically excluded target,
then the inclusion is strict. The exclusion only needs the lower level. -/
theorem strict_of_two_seed_forcing
    {U W : Submodule K V} {N D : V →ₗ[K] V} {q₂ q₃ target : V}
    (relation : U≤W) (hn : U≤W.comap N) (hd : U≤W.comap D)
    (h₂ : q₂∈W) (h₃ : q₃∈W) (outside : target∉U)
    (force : ∀ S : Submodule K V, (∀ x∈S, N x∈S) → (∀ x∈S, D x∈S) →
      q₂∈S → q₃∈S → target∈S) : U<W := by
  refine lt_of_le_of_ne relation ?_
  intro e
  subst W
  exact outside (force U (fun _ hx => hn hx) (fun _ hx => hd hx) h₂ h₃)

/-- Each witnessed strict inclusion contributes one dimension, and the
initial rank is retained. Only the given interval is needed. -/
theorem finrank_gain_of_steps [FiniteDimensional K V] (F : ℕ → Submodule K V)
    {a b : ℕ} (ab : a≤b)
    (step : ∀ j, a≤j → j<b → F j<F (j+1)) :
    (b-a)+finrank K (F a) ≤ finrank K (F b) := by
  have lb (d : ℕ) (pay : a+d≤b) :
      d+finrank K (F a) ≤ finrank K (F (a+d)) := by
    induction d with
    | zero => simp
    | succ d ih =>
      have prev := ih (by omega)
      have cut := Submodule.finrank_lt_finrank_of_lt (step (a+d) (by omega) (by omega))
      have e : a+d.succ=a+d+1 := by omega
      calc
        d.succ+finrank K (F a) ≤ finrank K (F (a+d+1)) := by omega
        _ = finrank K (F (a+d.succ)) := congrArg (fun j => finrank K (F j)) e.symm
  have h : a+(b-a)=b := Nat.add_sub_of_le ab
  calc
    (b-a)+finrank K (F a) ≤ finrank K (F (a+(b-a))) := lb (b-a) h.le
    _ = finrank K (F b) := congrArg (fun j => finrank K (F j)) h

end RKCert.ReviewedNative.RankFlags
