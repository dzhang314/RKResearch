/-! The deterministic obstruction mask, independently of the coefficient atlas. -/
namespace RKResearch.ERK11FiniteAliasUnitMask
open Lean.Grind
variable {R : Type} [CommRing R]

def complementProduct (xs : List R) : R :=
  xs.foldr (fun x p => (1-x)*p) 1

def unitMask (xs : List R) : R :=
  1-complementProduct xs

theorem complementAllZero (xs : List R)
    (h : ∀ x, x ∈ xs → x=0) : complementProduct xs=1 := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    have hx : x=0 := h x (by simp)
    have ht : ∀ y, y ∈ tl → y=0 := fun y hy => h y (by simp [hy])
    change (1-x)*complementProduct tl=1
    rw [hx,ih ht]
    grind

theorem complementHasOne (xs : List R)
    (h : (1:R) ∈ xs) : complementProduct xs=0 := by
  induction xs with
  | nil => simp at h
  | cons x tl ih =>
    change (1-x)*complementProduct tl=0
    rcases List.mem_cons.mp h with h1 | ht
    · rw [←h1]
      grind
    · rw [ih ht]
      grind

theorem maskAllZero (xs : List R)
    (h : ∀ x, x ∈ xs → x=0) : unitMask xs=0 := by
  unfold unitMask
  rw [complementAllZero xs h]
  grind

theorem maskHasOne (xs : List R)
    (h : (1:R) ∈ xs) : unitMask xs=1 := by
  unfold unitMask
  rw [complementHasOne xs h]
  grind

end RKResearch.ERK11FiniteAliasUnitMask
#print axioms RKResearch.ERK11FiniteAliasUnitMask.maskAllZero
#print axioms RKResearch.ERK11FiniteAliasUnitMask.maskHasOne
