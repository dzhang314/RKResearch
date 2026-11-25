module

public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Order.Zorn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Proper square preorders extend to field orders

Draft. The only maximal object is a subsemiring of a fixed field, not an
ordered algebraic closure. Positivity of designated elements is kept.
-/
namespace RKCert.ReviewedNative.OrderedPreorderExtension

open Set

noncomputable section
variable {F : Type*} [Field F]

/-- The two ingredients of a proper field preordering. -/
def SquarePreorder (C : Subsemiring F) : Prop :=
  (∀ x : F, x^2∈C) ∧ (-1:F)∉C

/-- Form C+xC; closure pays just the one square x² in C. -/
private def adjoiningSign (C : Subsemiring F) (x : F) (sq : x^2∈C) : Subsemiring F where
  carrier := { y | ∃ a ∈ C, ∃ b ∈ C, y=a+x*b }
  zero_mem' := ⟨0,C.zero_mem,0,C.zero_mem,by ring⟩
  one_mem' := ⟨1,C.one_mem,0,C.zero_mem,by ring⟩
  add_mem' := by
    rintro y z ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    exact ⟨a+c,C.add_mem ha hc,b+d,C.add_mem hb hd,by ring⟩
  mul_mem' := by
    rintro y z ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    exact ⟨a*c+x^2*(b*d),C.add_mem (C.mul_mem ha hc) (C.mul_mem sq (C.mul_mem hb hd)),
      a*d+b*c,C.add_mem (C.mul_mem ha hd) (C.mul_mem hb hc),by ring⟩

private theorem le_adjoiningSign (C : Subsemiring F) (x : F) (sq : x^2∈C) :
    C ≤ adjoiningSign C x sq := by
  intro y hy
  exact ⟨y,hy,0,C.zero_mem,by ring⟩

private theorem mem_adjoiningSign (C : Subsemiring F) (x : F) (sq : x^2∈C) :
    x∈adjoiningSign C x sq :=
  ⟨0,C.zero_mem,1,C.one_mem,by ring⟩

/-- A maximal proper square preorder is pointed and spanning. -/
theorem extend_to_orderCone (P : Subsemiring F) (hp : SquarePreorder P) :
    ∃ C : Subsemiring F, P≤C ∧ C.toAddSubmonoid.IsPointed ∧ C.toAddSubmonoid.IsSpanning := by
  classical
  let admissible : Set (Subsemiring F) := {S | SquarePreorder S}
  have ub (chain : Set (Subsemiring F)) (sub : chain ⊆ admissible)
      (hc : IsChain (· ≤ ·) chain) (Y : Subsemiring F) (hy : Y∈chain) :
      ∃ D∈admissible, ∀ X∈chain, X≤D := by
    have hy' : SquarePreorder Y := sub hy
    have dir : DirectedOn (· ≤ ·) chain := hc.directedOn
    refine ⟨sSup chain,⟨?_,?_⟩,fun _ hx => le_sSup hx⟩
    · intro x
      exact le_sSup hy (hy'.1 x)
    · intro hn
      obtain ⟨Z,hz,hzn⟩ := (Subsemiring.mem_sSup_of_directedOn ⟨Y,hy⟩ dir).mp hn
      exact (show SquarePreorder Z from sub hz).2 hzn
  obtain ⟨C,hPC,hM⟩ := zorn_le_nonempty₀ admissible ub P hp
  have hC : SquarePreorder C := hM.1
  have pointed : C.toAddSubmonoid.IsPointed := by
    intro x hx hnx
    by_contra h0
    have hx2 := hC.1 (x⁻¹)
    have hneg : (-x)*x*(x⁻¹)^2 ∈ C := C.mul_mem (C.mul_mem hnx hx) hx2
    have heq : (-x)*x*(x⁻¹)^2 = -1 := by field_simp [h0] <;> ring
    exact hC.2 (heq ▸ hneg)
  have rejected (x : F) (hx : x∉C) :
      (-1:F) ∈ adjoiningSign C x (hC.1 x) := by
    by_contra hn
    have CD := le_adjoiningSign C x (hC.1 x)
    have hd : SquarePreorder (adjoiningSign C x (hC.1 x)) :=
      ⟨fun y => CD (hC.1 y),hn⟩
    have eq : C = adjoiningSign C x (hC.1 x) := hM.eq_of_le hd CD
    exact hx (eq.symm ▸ mem_adjoiningSign C x (hC.1 x))
  have spanning : C.toAddSubmonoid.IsSpanning := by
    intro x
    by_cases hx : x∈C
    · exact Or.inl hx
    by_cases hnx : -x∈C
    · exact Or.inr hnx
    exfalso
    obtain ⟨a,ha,b,hb,e₁⟩ := rejected x hx
    obtain ⟨c,hc,d,hd,e₂⟩ := rejected (-x) hnx
    have e₁' : 1+a = -x*b := by linear_combination -e₁
    have e₂' : 1+c = x*d := by linear_combination -e₂
    have prod : (1+a)*(1+c) = (-x*b)*(x*d) := congrArg₂ (· * ·) e₁' e₂'
    have eq : (-1:F) = a+c+a*c+x^2*(b*d) := by linear_combination -prod
    have yes := C.add_mem (C.add_mem (C.add_mem ha hc) (C.mul_mem ha hc))
      (C.mul_mem (hC.1 x) (C.mul_mem hb hd))
    exact hC.2 (eq.symm ▸ yes)
  exact ⟨C,hPC,pointed,spanning⟩

/-- Give the same field an extending order, retaining all the original
preorder elements as nonnegative. -/
theorem ordered_of_preorder (P : Subsemiring F) (hp : SquarePreorder P) :
    ∃ order : LinearOrder F, letI := order
      IsStrictOrderedRing F ∧ ∀ x∈P, 0≤x := by
  classical
  obtain ⟨C,incl,pointed,span⟩ := extend_to_orderCone P hp
  let order : LinearOrder F := LinearOrder.ofAddSubmonoid pointed span
  letI : LinearOrder F := order
  letI : IsOrderedRing F := IsOrderedRing.ofSubsemiring pointed
  have strict : IsStrictOrderedRing F := inferInstance
  refine ⟨order,strict,?_⟩
  intro x hx
  change x-0∈C
  simpa only [sub_zero] using incl hx

end
end RKCert.ReviewedNative.OrderedPreorderExtension
