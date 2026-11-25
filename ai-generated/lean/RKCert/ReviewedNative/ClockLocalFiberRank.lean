module
public import RKCert.ReviewedNative.ClockLocalAnnihilator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-! # Exact fibre rank of the clock-local annihilator -/
namespace RKResearch.Certified.Graded.Reverse

open Module RKCert.Endpoint
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

/-- An actually occurring stage clock, not an arbitrary scalar. -/
abbrev ClockSite (c : Fin s → K) := ↥(Finset.univ.image c)

/-- The site of an original stage. -/
def clockLabel (c : Fin s → K) (i : Fin s) : ClockSite c :=
  ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩

/-- Original coordinates at one actual clock. -/
abbrev ClockFiber (c : Fin s → K) (x : ClockSite c) :=
  {i : Fin s // clockLabel c i = x}

/-- Keep the original coordinates in the indicated clock fibre. -/
def clockFiberRestrict (c : Fin s → K) (x : ClockSite c) :
    (Fin s → K) →ₗ[K] ClockFiber c x → K :=
  LinearMap.funLeft K K (Subtype.val : ClockFiber c x → Fin s)

/-- The whole column space seen on one clock fibre. -/
def clockFiberColumns (c : Fin s → K) (X : Submodule K (Fin s → K))
    (x : ClockSite c) : Submodule K (ClockFiber c x → K) :=
  X.map (clockFiberRestrict c x)

private theorem clockLabel_eq_iff (c : Fin s → K) (i : Fin s) (x : ClockSite c) :
    clockLabel c i = x ↔ c i = (x : K) :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

private theorem row_blockMask_eq_clockFiberRestrict
    (c : Fin s → K) (x : ClockSite c) (w v : Fin s → K) :
    row (blockMask c (x : K) w) v =
      row (clockFiberRestrict c x w) (clockFiberRestrict c x v) := by
  simp only [row_apply, dotProduct, blockMask, clockFiberRestrict, LinearMap.funLeft_apply]
  calc
    (∑ i : Fin s, (if c i = (x : K) then w i else 0) * v i) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin s => clockLabel c i = x), w i * v i := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : c i = (x : K) <;> simp [clockLabel_eq_iff, hi]
    _ = ∑ i : ClockFiber c x, w i.val * v i.val :=
      Finset.sum_subtype (p := fun i : Fin s => clockLabel c i = x) (F := inferInstance)
        (Finset.univ.filter fun i => clockLabel c i = x) (fun _ => by simp) (fun i => w i * v i)

/-- Membership of every zero-extended mask in the global annihilator is
exactly independent annihilation of the restricted columns on each fibre. -/
theorem mem_clockLocal_annih_iff {c w : Fin s → K} {X : Submodule K (Fin s → K)} :
    w ∈ clockLocal c (annih X) ↔
      ∀ x : ClockSite c, clockFiberRestrict c x w ∈ annih (clockFiberColumns c X x) := by
  rw [mem_clockLocal]
  constructor
  · intro hm x
    apply mem_annih.mpr
    intro v hv
    change v ∈ X.map (clockFiberRestrict c x) at hv
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    rw [← row_blockMask_eq_clockFiberRestrict c x w z]
    exact mem_annih.mp (hm (x : K)) z hz
  · intro h x
    by_cases hx : x ∈ Finset.univ.image c
    · let t : ClockSite c := ⟨x, hx⟩
      apply mem_annih.mpr
      intro v hv
      change row (blockMask c (t : K) w) v = 0
      rw [row_blockMask_eq_clockFiberRestrict c t w v]
      have hv' : clockFiberRestrict c t v ∈ X.map (clockFiberRestrict c t) :=
        Submodule.mem_map_of_mem hv
      exact mem_annih.mp (h t) _ hv'
    · have zeroMask : blockMask c x w = 0 := by
        funext i
        have hi : c i ≠ x := fun e => hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, e⟩)
        simp [blockMask, hi]
      rw [zeroMask]
      exact (annih X).zero_mem

private def clockFiberSplit (c : Fin s → K) :
    (Fin s → K) ≃ₗ[K] ((x : ClockSite c) → ClockFiber c x → K) :=
  (LinearEquiv.funCongrLeft K K (Equiv.sigmaFiberEquiv (clockLabel c))).trans
    (LinearEquiv.piCurry K (fun (x : ClockSite c) (_ : ClockFiber c x) => K))

private theorem clockFiberSplit_apply (c : Fin s → K) (w : Fin s → K) (x : ClockSite c) :
    clockFiberSplit c w x = clockFiberRestrict c x w := rfl

private def clockPiSubtype {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)] (N : ∀ i, Submodule K (V i)) :
    Submodule.pi Set.univ N ≃ₗ[K] ((i : ι) → ↥(N i)) where
  __ := Equiv.Set.univPi (fun i => (N i : Set (V i)))
  map_add' _ _ := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    funext i
    apply Subtype.ext
    rfl

/-- The exact product decomposition on original clock fibres. -/
@[no_expose] def clockLocalAnnihEquiv (c : Fin s → K) (X : Submodule K (Fin s → K)) :
    clockLocal c (annih X) ≃ₗ[K] ((x : ClockSite c) → ↥(annih (clockFiberColumns c X x))) := by
  let e := clockFiberSplit c
  let N := fun x : ClockSite c => annih (clockFiberColumns c X x)
  let U := Submodule.pi Set.univ N
  have h : clockLocal c (annih X) = U.comap e.toLinearMap := by
    ext w
    rw [mem_clockLocal_annih_iff]
    change (∀ x : ClockSite c, clockFiberRestrict c x w ∈ N x) ↔ e w ∈ U
    simp only [U, Submodule.mem_pi, Set.mem_univ, true_implies, e, clockFiberSplit_apply]
  exact (LinearEquiv.ofEq _ _ h).trans ((e.ofSubmodule' U).trans (clockPiSubtype N))

private theorem finrank_clockLocal_annih_eq_sum (c : Fin s → K) (X : Submodule K (Fin s → K)) :
    finrank K (clockLocal c (annih X)) = ∑ x : ClockSite c, finrank K (annih (clockFiberColumns c X x)) :=
  (clockLocalAnnihEquiv c X).finrank_eq.trans (Module.finrank_pi_fintype K)

/-- Local physical dimension is the sum of the exact per-fibre deficits. -/
theorem finrank_clockLocal_annih (c : Fin s → K) (X : Submodule K (Fin s → K)) :
    finrank K (clockLocal c (annih X)) =
      ∑ x : ClockSite c, (Fintype.card (ClockFiber c x) - finrank K (clockFiberColumns c X x)) := by
  rw [finrank_clockLocal_annih_eq_sum c X]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have rk := finrank_annih (clockFiberColumns c X x)
  omega

/-- The same fibre rank-nullity without truncated subtraction. -/
theorem finrank_clockLocal_annih_add_sum_eq (c : Fin s → K) (X : Submodule K (Fin s → K)) :
    finrank K (clockLocal c (annih X)) + (∑ x : ClockSite c, finrank K (clockFiberColumns c X x)) = s := by
  rw [finrank_clockLocal_annih_eq_sum c X, ← Finset.sum_add_distrib]
  calc
    (∑ x : ClockSite c, (finrank K (annih (clockFiberColumns c X x)) +
        finrank K (clockFiberColumns c X x))) = ∑ x : ClockSite c, Fintype.card (ClockFiber c x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact (add_comm _ _).trans (finrank_annih (clockFiberColumns c X x))
    _ = Fintype.card (Σ x : ClockSite c, ClockFiber c x) := Fintype.card_sigma.symm
    _ = Fintype.card (Fin s) := Fintype.card_congr (Equiv.sigmaFiberEquiv (clockLabel c))
    _ = s := Fintype.card_fin s

end
end RKResearch.Certified.Graded.Reverse
