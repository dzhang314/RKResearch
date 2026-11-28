/-! No algebraic axioms are required to insert erasing projections
when every actual unmodified prefix is silent on the omitted axes. -/

namespace RKResearch.Certified.ERK10TiltSilentErasure

def act {V : Type u} : List (V → V) → V → V
  | [], x => x
  | A :: L, x => A (act L x)

def trim {V : Type u} (P : V → V) : List (V → V) → V → V
  | [], x => P x
  | A :: L, x => P (A (trim P L x))

/-- The prefix hypothesis uses the original operators, not the
projected ones. Mathematically it follows from annihilating every
image W e_j of an erased coordinate at the relevant length. -/
theorem eraseSilentAxes {V : Type u} {F : Type v} (P : V → V)
    (L : List (V → V)) (w : V → F) (x : V)
    (silent : ∀ a b, a ++ b = L → ∀ y, w (act a (P y)) = w (act a y)) :
    w (act L x) = w (trim P L x) := by
  induction L generalizing w with
  | nil =>
    exact (silent [] [] rfl x).symm
  | cons A L ih =>
    have hs : ∀ a b, a ++ b = L → ∀ y,
        (w ∘ A) (act a (P y)) = (w ∘ A) (act a y) := by
      intro a b hab y
      exact silent (A :: a) b (congrArg (List.cons A) hab) y
    calc
      w (act (A :: L) x) = (w ∘ A) (act L x) := rfl
      _ = (w ∘ A) (trim P L x) := ih (w ∘ A) hs
      _ = w (trim P (A :: L) x) := (silent [] (A :: L) rfl (A (trim P L x))).symm

end RKResearch.Certified.ERK10TiltSilentErasure
#print axioms RKResearch.Certified.ERK10TiltSilentErasure.eraseSilentAxes
