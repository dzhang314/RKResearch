module

public import RKCert.DirkBoundary
public import RKCert.DirkTerminalMoments
public import RKCert.DIRKSmall

@[expose] public section

/-! # Unrestricted diagonally implicit RK: uniform stage floors

The hypotheses concern the original tableau and its full denominator-cleared
tree conditions. No nonzero individual weight, nonzero diagonal, ordering of
nodes, or characteristic-zero assumption is imposed. Residue-field transfer
retains the conclusion even for coefficient rings containing zero divisors.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

theorem twoOrbit_initial_zero {N D : Vec K s →ₗ[K] Vec K s} {u v w : Vec K s}
    (hz : finrank K (twoOrbit N D u v w 0)=0) : u=0 ∧ v=0 := by
  have h := Submodule.finrank_eq_zero.mp hz
  have hu : u∈twoOrbit N D u v w 0 :=
    (le_sup_left : Submodule.span K {u} ≤ twoOrbit N D u v w 0) (Submodule.subset_span (Set.mem_singleton _))
  have hv : v∈twoOrbit N D u v w 0 :=
    (le_sup_right : Submodule.span K {v} ≤ twoOrbit N D u v w 0) (Submodule.subset_span (Set.mem_singleton _))
  rw [h] at hu hv
  exact ⟨hu,hv⟩

theorem annih_flip_le {U W : Submodule K (Vec K s)} (h : W ≤ annih U) : U ≤ annih W := by
  intro u hu
  apply mem_annih.mpr
  intro w hw
  simpa only [row_apply, mul_comm] using mem_annih.mp (h hw) u hu

theorem dirk_terminal_refund (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) {m n r : ℕ} (hm : m=n+2)
    (hp : 2*m+1≤p) (hpay : m+r+3 ≤ p) : m+1+n+r+1 ≤ s := by
  cases s with
  | zero =>
    have hh := dirk_rank_budget ha ho hm hp hpay
    omega
  | succ s =>
    by_contra hlow
    have hb := dirk_rank_budget ha ho hm hp hpay
    have hf : finrank K (dirkFront A 0)=0 := by omega
    have hr : finrank K (dirkBack A b 0)=0 := by omega
    have hq := (twoOrbit_initial_zero hf).2
    obtain ⟨h₁,h₂⟩ := twoOrbit_initial_zero hr
    obtain ⟨i,hbi,hlast⟩ := last_output ho (by omega)
    have hrow := dirk_first_row ha hq
    have hci := dirk_last_node ha i hbi hlast h₁ h₂
    have ha' := dirkBack_annih ho m r hpay
    have he' := annih_flip_le ha'
    have hfr := dirkFront_rank ha ho n (by omega)
    rw [←hm] at hfr
    have hbk := dirkBack_rank ha ho r (by omega)
    have he := treeSpace_rank ho hp
    have hle := Submodule.finrank_mono he'
    have cap := finrank_annih_le (le_refl (annih (dirkBack A b r)))
    have eqn : treeSpace A m=annih (dirkBack A b r) :=
      Submodule.eq_of_le_of_finrank_eq he' (by omega)
    have hstage : Pi.single i (1:K) ∈ treeSpace A m := by
      rw [eqn, mem_annih]
      intro v hv
      have hh := dirkBack_prior ha i hlast hci h₁ h₂ r hv i le_rfl
      simp [row,Pi.single_apply,hh]
    obtain ⟨a,ha₀⟩ := exists_poly_zeroSpace ho (by omega) hstage
    have hnode : nodes A i=1 := by
      change 1 - nodes A i=0 at hci
      exact (sub_eq_zero.mp hci).symm
    apply terminal_not_decomposable ho hp hrow i hnode hbi a _ ha₀
    abel

/-- Over *any* coefficient field, at every order at least six. -/
theorem dirk_floor_field (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 6≤p) : p+(p-1)/2-3 ≤ s := by
  let m := (p-1)/2
  have hh := dirk_terminal_refund ha ho (m:=m) (n:=m-2) (r:=p-m-3)
    (by dsimp [m]; omega) (by dsimp [m]; omega) (by dsimp [m]; omega)
  dsimp [m] at hh
  omega

end RKCert.Paired

namespace RKCert
universe u

/-- The lower bound over every nontrivial commutative ring, on the original
tableau. There is no field-map, characteristic, or factorial-unit hypothesis. -/
theorem dirk_floor_ring {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 6≤p) : p+(p-1)/2-3 ≤ s :=
  lowerTriangular_of_all_fields (fun _ _ _ _ hA ht => Paired.dirk_floor_field hA ht hp) ha ho

/-- Uniform nontrivial-ring stage ledger, including orders zero through five. -/
def dirkRingFloor (p : ℕ) : ℕ :=
  match p with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | k+6 => (k+6)+(k+5)/2-3

theorem dirkRingFloor_le_stages {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j, i.val < j.val → A i j = 0)
    (ho : HasTreeOrderAtLeast A b p) : dirkRingFloor p ≤ s := by
  rcases p with _|p
  · exact Nat.zero_le _
  rcases p with _|p
  · exact DIRKFinite.positive_stages ho (by decide)
  rcases p with _|p
  · exact DIRKFinite.positive_stages ho (by decide)
  rcases p with _|p
  · exact DIRKFinite.order_three_ring ha ho
  rcases p with _|p
  · exact DIRKFinite.order_four_ring ha ho
  rcases p with _|p
  · exact DIRKFinite.order_five_ring ha ho
  exact dirk_floor_ring ha ho (by omega)

/-- Regression on the complete published uniform-ring column, not just its last entry. -/
theorem dirkRingFloor_through20 :
    (List.range 21).map dirkRingFloor =
    [0,1,1,2,3,4,5,7,8,10,11,13,14,16,17,19,20,22,23,25,26] := by decide

end RKCert
