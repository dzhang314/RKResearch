module

public import RKCert.ReviewedNative.DiagonalTreeShift
public import RKCert.ReviewedNative.FiniteRootedSeriesCertificate
import Mathlib.Algebra.Module.Submodule.EqLocus
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Every literal tree keeps its own coefficient-one term, with an
order-strict correction. In particular the first failing tree is stable. -/
namespace RKResearch.DiagonalTreeShift

open RKResearch FiniteRootedTree RKResearch.FiniteSeries
open scoped FiniteRootedTree

noncomputable section

variable (R : Type*) [CommSemiring R]

def below (n : ℕ) : Submodule R (TreeCombination R) :=
  Submodule.span R {x | ∃ t : FiniteRootedTree, treeGrade t < n ∧ x = atom R t}

theorem atom_mem_below (t : FiniteRootedTree) {n : ℕ} (paid : treeGrade t < n) :
    atom R t ∈ below R n := Submodule.subset_span ⟨t, paid, rfl⟩

theorem below_mono {n m : ℕ} (h : n ≤ m) : below R n ≤ below R m := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  exact atom_mem_below R t (ht.trans_le h)

theorem unary_mem_below {x : TreeCombination R} {n : ℕ} (h : x ∈ below R n) :
    unary R x ∈ below R (n+1) := by
  have bound : below R n ≤ (below R (n+1)).comap (unary R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    change unary R (atom R t) ∈ below R (n+1)
    rw [unary_atom]
    exact atom_mem_below R _ (by rw [treeGrade_unary]; omega)
  exact bound h

theorem join_mem_below {x y : TreeCombination R} {n m : ℕ}
    (hx : x ∈ below R n) (hy : y ∈ below R m) :
    join R x y ∈ below R (n+m-1) := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ (join R) _ _ _ hx hy
  rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
  rw [join_atom]
  exact atom_mem_below R _ (by rw [treeGrade_rootedSum]; omega)

private theorem graft_degree (t u : FiniteRootedTree) :
    treeGrade (t ◂ u) = treeGrade t + (treeGrade u+1) := by
  change treeGrade (t # (.leaf ◂ u)) = _
  rw [treeGrade_rootedSum, treeGrade_unary]

theorem expand_eq_atom_add_lower (a : R) (t : FiniteRootedTree) :
    ∃ e ∈ below R (treeGrade t), expand R a t = atom R t + e := by
  induction t with
  | leaf => exact ⟨0, (below R (treeGrade .leaf)).zero_mem, (add_zero _).symm⟩
  | butcherProduct t u ht hu =>
    obtain ⟨et, mt, eqt⟩ := ht
    obtain ⟨eu, mu, equ⟩ := hu
    let X := atom R t + et
    let Z := unary R eu + a • (atom R u + eu)
    have mx : X ∈ below R (treeGrade t+1) :=
      (below R _).add_mem (atom_mem_below R _ (Nat.lt_succ_self _))
        (below_mono R (Nat.le_succ _) mt)
    have my : atom R u + eu ∈ below R (treeGrade u+1) :=
      (below R _).add_mem (atom_mem_below R _ (Nat.lt_succ_self _))
        (below_mono R (Nat.le_succ _) mu)
    have mz : Z ∈ below R (treeGrade u+1) :=
      (below R _).add_mem (unary_mem_below R mu) ((below R _).smul_mem _ my)
    have mU : unary R (atom R u) ∈ below R (treeGrade u+2) := by
      rw [unary_atom]
      exact atom_mem_below R _ (by rw [treeGrade_unary]; omega)
    refine ⟨join R et (unary R (atom R u)) + join R X Z, ?_, ?_⟩
    · have ha := join_mem_below R mt mU
      have hb := join_mem_below R mx mz
      rw [graft_degree]
      exact (below R _).add_mem
        (below_mono R (by omega : treeGrade t+(treeGrade u+2)-1 ≤
          treeGrade t+(treeGrade u+1)) ha)
        (below_mono R (by omega : (treeGrade t+1)+(treeGrade u+1)-1 ≤
          treeGrade t+(treeGrade u+1)) hb)
    · have pull : unary R (expand R a u) + a • expand R a u =
          unary R (atom R u) + Z := by
        simp only [equ, map_add, Z, add_assoc]
      have left : join R X (unary R (atom R u)) =
          join R (atom R t) (unary R (atom R u)) + join R et (unary R (atom R u)) := by
        change (join R).flip (unary R (atom R u)) (atom R t + et) = _
        exact map_add _ _ _
      change join R (expand R a t) (unary R (expand R a u) + a • expand R a u) = _
      rw [show expand R a t = X from eqt, pull, map_add (join R X), left,
        unary_atom, join_atom, rootedSum, rootedSum, add_assoc]

section Agreement
variable {V : Type*} [AddCommMonoid V] [Module R V]

/-- Under strict-prefix agreement, the same lower-order scalar is added
to both values of a literal tree. -/
theorem same_correction (a : R) (f g : FiniteRootedTree → V) (t : FiniteRootedTree)
    (same : ∀ u, (u.order : ℕ) < (t.order : ℕ) → f u = g u) :
    ∃ c, transform R a f t = f t + c ∧ transform R a g t = g t + c := by
  obtain ⟨e, he, expansion⟩ := expand_eq_atom_add_lower R a t
  have span : below R (treeGrade t) ≤ LinearMap.eqLocus (lift R f) (lift R g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change lift R f (atom R u) = lift R g (atom R u)
    rw [lift_atom, lift_atom]
    have ut := treeGrade_succ u
    have tt := treeGrade_succ t
    exact same u (by omega)
  have balanced := LinearMap.mem_eqLocus.mp (span he)
  refine ⟨lift R f e, ?_, ?_⟩
  · rw [transform, expansion, map_add, lift_atom]
  · rw [transform, expansion, map_add, lift_atom, ← balanced]

def AgreesThrough (n : ℕ) (f g : FiniteRootedTree → V) : Prop :=
  ∀ t, (t.order : ℕ) ≤ n → f t = g t

theorem agreesThrough_transform (a : R) {n : ℕ} {f g : FiniteRootedTree → V}
    (h : AgreesThrough n f g) :
    AgreesThrough n (transform R a f) (transform R a g) := by
  intro t ht
  obtain ⟨c, hf, hg⟩ := same_correction R a f g t (fun u hu => h u (hu.le.trans ht))
  rw [hf, hg, h t ht]

end Agreement

section Cancellative
variable {V : Type*} [AddCancelCommMonoid V] [Module R V]

theorem transform_at_eq_iff (a : R) (f g : FiniteRootedTree → V) (t : FiniteRootedTree)
    (same : ∀ u, (u.order : ℕ) < (t.order : ℕ) → f u = g u) :
    transform R a f t = transform R a g t ↔ f t = g t := by
  obtain ⟨c, hf, hg⟩ := same_correction R a f g t same
  rw [hf, hg]
  exact ⟨add_right_cancel, fun h => congrArg (fun x => x + c) h⟩

def FirstDifferenceAt (n : ℕ) (f g : FiniteRootedTree → V) : Prop :=
  (∀ t, (t.order : ℕ) < n → f t = g t) ∧
    ∃ t, (t.order : ℕ) = n ∧ f t ≠ g t

theorem firstDifference_transform (a : R) {n : ℕ} {f g : FiniteRootedTree → V}
    (h : FirstDifferenceAt n f g) :
    FirstDifferenceAt n (transform R a f) (transform R a g) := by
  obtain ⟨same, t, ht, bad⟩ := h
  refine ⟨?_, t, ht, ?_⟩
  · intro u hu
    exact (transform_at_eq_iff R a f g u (fun v hv => same v (hv.trans hu))).mpr (same u hu)
  · exact fun e => bad ((transform_at_eq_iff R a f g t (by simpa only [ht] using same)).mp e)

end Cancellative

section Inverse
variable (S : Type*) [CommRing S]
variable {V : Type*} [AddCancelCommMonoid V] [Module S V]

theorem agreesThrough_transform_iff (a : S) (n : ℕ) (f g : FiniteRootedTree → V) :
    AgreesThrough n (transform S a f) (transform S a g) ↔ AgreesThrough n f g := by
  constructor
  · intro h
    simpa only [transform_neg_left] using agreesThrough_transform S (-a) h
  · exact agreesThrough_transform S a

theorem firstDifference_transform_iff (a : S) (n : ℕ) (f g : FiniteRootedTree → V) :
    FirstDifferenceAt n (transform S a f) (transform S a g) ↔ FirstDifferenceAt n f g := by
  constructor
  · intro h
    simpa only [transform_neg_left] using firstDifference_transform S (-a) h
  · exact firstDifference_transform S a

end Inverse
end
end RKResearch.DiagonalTreeShift
