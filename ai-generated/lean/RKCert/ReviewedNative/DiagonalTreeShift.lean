module

public import RKResearch.FiniteRootedTree
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-! Diagonal edge contraction on the free linear span of the reviewed
literal trees. Root lists remain ordered; no edge sets or quotient are used. -/
namespace RKResearch.DiagonalTreeShift

open RKResearch FiniteRootedTree
open scoped FiniteRootedTree

noncomputable section

abbrev TreeCombination (R : Type*) [CommSemiring R] := FiniteRootedTree →₀ R

variable (R : Type*) [CommSemiring R]

def atom (t : FiniteRootedTree) : TreeCombination R := Finsupp.single t 1

def lift {V : Type*} [AddCommMonoid V] [Module R V]
    (f : FiniteRootedTree → V) : TreeCombination R →ₗ[R] V :=
  Finsupp.linearCombination R f

@[simp] theorem lift_atom {V : Type*} [AddCommMonoid V] [Module R V]
    (f : FiniteRootedTree → V) (t : FiniteRootedTree) :
    lift R f (atom R t) = f t := by
  simp only [lift, atom, Finsupp.linearCombination_single, one_smul]

theorem hom_ext_atoms {V : Type*} [AddCommMonoid V] [Module R V]
    {f g : TreeCombination R →ₗ[R] V}
    (equal : ∀ t, f (atom R t) = g (atom R t)) : f = g := by
  apply Finsupp.lhom_ext
  intro t a
  have e : Finsupp.single t a = a • atom R t := by
    simp only [atom, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e, map_smul, map_smul, equal t]

private theorem bilin_ext_atoms {V : Type*} [AddCommMonoid V] [Module R V]
    {f g : TreeCombination R →ₗ[R] TreeCombination R →ₗ[R] V}
    (equal : ∀ t u, f (atom R t) (atom R u) = g (atom R t) (atom R u)) : f = g := by
  apply hom_ext_atoms R
  intro t
  apply hom_ext_atoms R
  exact equal t

def join : TreeCombination R →ₗ[R] TreeCombination R →ₗ[R] TreeCombination R :=
  lift R (fun t => lift R (fun u => atom R (t # u)))

def unary : TreeCombination R →ₗ[R] TreeCombination R :=
  lift R (fun t => atom R (.leaf ◂ t))

@[simp] theorem join_atom (t u : FiniteRootedTree) :
    join R (atom R t) (atom R u) = atom R (t # u) := by
  simp only [join, lift_atom]

@[simp] theorem unary_atom (t : FiniteRootedTree) :
    unary R (atom R t) = atom R (.leaf ◂ t) := lift_atom R _ t

private theorem literal_left_unit (t : FiniteRootedTree) : .leaf # t = t := by
  induction t with
  | leaf => rfl
  | butcherProduct a b ih _ => simp only [rootedSum, ih]

private theorem literal_assoc (t u v : FiniteRootedTree) :
    (t # u) # v = t # (u # v) := by
  induction v with
  | leaf => rfl
  | butcherProduct a b ih _ => simp only [rootedSum, ih]

@[simp] theorem join_unit_left (x : TreeCombination R) :
    join R (atom R .leaf) x = x := by
  change join R (atom R .leaf) x = LinearMap.id (R := R) x
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro t
  simp only [join_atom, literal_left_unit, LinearMap.id_apply]

@[simp] theorem join_unit_right (x : TreeCombination R) :
    join R x (atom R .leaf) = x := by
  change (join R).flip (atom R .leaf) x = LinearMap.id (R := R) x
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro t
  simp only [LinearMap.flip_apply, join_atom, rootedSum, LinearMap.id_apply]

theorem join_assoc (x y z : TreeCombination R) :
    join R (join R x y) z = join R x (join R y z) := by
  change (((join R).flip z).comp ((join R).flip y)) x =
    (join R).flip (join R y z) x
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro t
  change (((join R).flip z).comp (join R (atom R t))) y =
    ((join R (atom R t)).comp ((join R).flip z)) y
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro u
  change join R (join R (atom R t) (atom R u)) z =
    ((join R (atom R t)).comp (join R (atom R u))) z
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro v
  simp only [LinearMap.comp_apply, join_atom, literal_assoc]

/-- Extend a root-join identity from literal columns to all combinations. -/
theorem lift_join_of_atoms {V : Type*} [AddCommMonoid V] [Module R V]
    (F : TreeCombination R →ₗ[R] V) (J : V →ₗ[R] V →ₗ[R] V)
    (equal : ∀ t u, F (atom R (t # u)) = J (F (atom R t)) (F (atom R u)))
    (x y : TreeCombination R) :
    F (join R x y) = J (F x) (F y) := by
  have eq : (join R).compr₂ F = J.compl₁₂ F F := by
    apply bilin_ext_atoms R
    intro t u
    simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, join_atom] using equal t u
  exact LinearMap.congr_fun₂ eq x y

/-- Keeping the newest edge uses unary extension. Contracting it uses
the branch itself, multiplied by the diagonal shift. -/
@[simp] def expand (a : R) : FiniteRootedTree → TreeCombination R
  | .leaf => atom R .leaf
  | .butcherProduct t u => join R (expand a t) (unary R (expand a u) + a • expand a u)

theorem expand_unary (a : R) (t : FiniteRootedTree) :
    expand R a (.leaf ◂ t) = unary R (expand R a t) + a • expand R a t := by
  simp only [expand, join_unit_left]

theorem expand_rootedSum (a : R) (t u : FiniteRootedTree) :
    expand R a (t # u) = join R (expand R a t) (expand R a u) := by
  induction u with
  | leaf => simp only [rootedSum, expand, join_unit_right]
  | butcherProduct b c ih _ => simp only [rootedSum, expand, ih, join_assoc]

def operator (a : R) : TreeCombination R →ₗ[R] TreeCombination R := lift R (expand R a)

@[simp] theorem operator_atom (a : R) (t : FiniteRootedTree) :
    operator R a (atom R t) = expand R a t := lift_atom R _ t

theorem operator_join (a : R) (x y : TreeCombination R) :
    operator R a (join R x y) = join R (operator R a x) (operator R a y) := by
  apply lift_join_of_atoms R
  intro t u
  simpa only [operator_atom] using expand_rootedSum R a t u

theorem operator_unary (a : R) (x : TreeCombination R) :
    operator R a (unary R x) = unary R (operator R a x) + a • operator R a x := by
  have h : (operator R a).comp (unary R) =
      ((unary R).comp (operator R a)) + a • operator R a := by
    apply hom_ext_atoms R
    intro t
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      unary_atom, operator_atom] using expand_unary R a t
  exact LinearMap.congr_fun h x

theorem operator_zero : operator R (0 : R) = LinearMap.id := by
  apply hom_ext_atoms R
  intro t
  simp only [operator_atom, LinearMap.id_apply]
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    simp only [expand, ht, hu, zero_smul, add_zero, unary_atom, join_atom, rootedSum]

theorem operator_comp (a b : R) :
    (operator R a).comp (operator R b) = operator R (a+b) := by
  apply hom_ext_atoms R
  intro t
  simp only [LinearMap.comp_apply, operator_atom]
  induction t with
  | leaf => simp only [expand, operator_atom]
  | butcherProduct t u ht hu =>
    simp only [expand, operator_join, map_add, map_smul, operator_unary, ht, hu,
      add_smul, add_assoc]

def transform {V : Type*} [AddCommMonoid V] [Module R V]
    (a : R) (f : FiniteRootedTree → V) (t : FiniteRootedTree) : V :=
  lift R f (expand R a t)

theorem transform_first_edge {V : Type*} [AddCommMonoid V] [Module R V]
    (a : R) (f : FiniteRootedTree → V) :
    transform R a f (.leaf ◂ .leaf) = f (.leaf ◂ .leaf) + a • f .leaf := by
  simp only [transform, expand, join_unit_left, unary_atom, map_add, map_smul, lift_atom]

theorem lift_transform {V : Type*} [AddCommMonoid V] [Module R V]
    (a : R) (f : FiniteRootedTree → V) :
    lift R (transform R a f) = (lift R f).comp (operator R a) := by
  apply hom_ext_atoms R
  intro t
  simp only [lift_atom, LinearMap.comp_apply, operator_atom, transform]

@[simp] theorem transform_zero {V : Type*} [AddCommMonoid V] [Module R V]
    (f : FiniteRootedTree → V) : transform R 0 f = f := by
  funext t
  rw [transform, ← operator_atom, operator_zero, LinearMap.id_apply, lift_atom]

theorem transform_comp {V : Type*} [AddCommMonoid V] [Module R V]
    (a b : R) (f : FiniteRootedTree → V) :
    transform R a (transform R b f) = transform R (a+b) f := by
  funext t
  change lift R (transform R b f) (expand R a t) = lift R f (expand R (a+b) t)
  rw [lift_transform, LinearMap.comp_apply, ← operator_atom R a t]
  change lift R f (((operator R b).comp (operator R a)) (atom R t)) =
    lift R f (expand R (a+b) t)
  rw [operator_comp, operator_atom, add_comm b a]

section Inverse
variable (S : Type*) [CommRing S]
variable {V : Type*} [AddCommMonoid V] [Module S V]

@[simp] theorem transform_neg_left (a : S) (f : FiniteRootedTree → V) :
    transform S (-a) (transform S a f) = f := by
  rw [transform_comp, neg_add_cancel, transform_zero]

@[simp] theorem transform_neg_right (a : S) (f : FiniteRootedTree → V) :
    transform S a (transform S (-a) f) = f := by
  rw [transform_comp, add_neg_cancel, transform_zero]

end Inverse
end
end RKResearch.DiagonalTreeShift
