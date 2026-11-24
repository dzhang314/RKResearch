module

public import RKCert.SDIRKCommutator
public import RKCert.GradeSeparation
public import RKCert.ResidueTransfer

@[expose] public section

namespace RKCert.Paired.SDIRK
open RKCert.Paired
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- Stage dimension recurrence using the actual, injective commutator and an
independent packet of scalar powers. Denominator units come from the achieved order, not
an assumption on the coefficient field. -/
theorem stage_rank_step (ho : HasTreeOrderAtLeast A b p) (ha : lower A) (hn : ∀ i, A i i ≠ 0)
    (j q : ℕ) (hgrade : q≤j+2) (hpay : q+j+3≤p) :
    q+1+Module.finrank K (treeSpace A j) ≤ Module.finrank K (treeSpace A (j+2)) := by
  let F := treeSpace A j
  let E := treeSpace A (j+2)
  let f : ((Fin (q+1) → K) × F) →ₗ[K] Vec K s :=
    (polyEval A q).coprod ((R A).comp F.subtype)
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem ((treeSpace_mono A hgrade) (polyEval_mem_treeSpace _ _ _))
      (commutator_mem z.2.property))
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have h : polyEval A q z.1 + R A (z.2 : Vec K s) = 0 :=
      congrArg (fun w : E => (w : Vec K s)) hz
    have h₁ : z.1=0 := by
      ext i
      apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) z.1 _ i
      intro l
      have hh := congrArg (probe A b l.val) h
      rw [map_add, probe_commutator ho (by omega) z.2.property, add_zero,
        probe_polyEval ho (by omega), map_zero] at hh
      exact hh
    have h₂ : (z.2 : Vec K s)=0 := by
      apply commutator_injective ha hn
      simpa [h₁] using h
    exact Prod.ext h₁ (Subtype.ext h₂)
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hg)

theorem stage_rank_base (ho : HasTreeOrderAtLeast A b p) {a q : ℕ}
    (hq : q≤a) (hp : q+a+1≤p) : q+1≤Module.finrank K (treeSpace A a) := by
  have h := treeSpace_rank ho (q:=q) (by omega)
  have h' := Submodule.finrank_mono (treeSpace_mono A hq)
  omega

/-- Parity recurrence of the physical stage dimensions. -/
def census (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => min 1 (p-1-1) + 1
  | j+2 => min (j+2) (p-1-(j+2)) + 1 + census p j

theorem census_le (ho : HasTreeOrderAtLeast A b p) (ha : lower A) (hn : ∀ i, A i i ≠ 0) :
    ∀ a, a+1≤p → census p a ≤ Module.finrank K (treeSpace A a)
  | 0, hp => stage_rank_base ho (q:=0) (by decide) hp
  | 1, hp => stage_rank_base ho (Nat.min_le_left ..) (by omega)
  | j+2, hp => by
    have h₀ := census_le ho ha hn j (by omega)
    let q := min (j+2) (p-1-(j+2))
    have h₁ := stage_rank_step ho ha hn j q (Nat.min_le_left ..) (by dsimp [q]; omega)
    change q+1+census p j ≤ _
    omega

def stageFloor (p : ℕ) : ℕ := max (census p (p-1)) (census p (p-2))

/-- The general parity census at any attained positive order, in any field. -/
theorem nonsingular_floor (ho : HasTreeOrderAtLeast A b p) (ha : lower A) (hn : ∀ i, A i i ≠ 0)
    (hp : 0<p) : stageFloor p ≤ s := by
  have go (a : ℕ) (hle : a+1≤p) : census p a ≤ s := by
    have h := (census_le ho ha hn a hle).trans (Submodule.finrank_le _)
    simpa only [Vec, Module.finrank_fin_fun] using h
  exact max_le (go _ (by omega)) (go _ (by omega))

def quadraticFloor (p : ℕ) : ℕ := ((p+1)^2/4 + 1)/2

private theorem floorCert :
    ∀ t : Fin 20, stageFloor (t.val+1) = quadraticFloor (t.val+1) := by decide

theorem nonsingular_quadratic_le20 (ho : HasTreeOrderAtLeast A b p) (ha : lower A)
    (hn : ∀ i, A i i ≠ 0) (hp : 0<p) (h20 : p≤20) : quadraticFloor p≤s := by
  have h := floorCert ⟨p-1,by omega⟩
  simp only at h
  rw [show p-1+1=p by omega] at h
  rw [← h]
  exact nonsingular_floor ho ha hn hp

theorem floor_table :
    (List.range 20).map (fun k => stageFloor (k+1)) =
      [1,1,2,3,5,6,8,10,13,15,18,21,25,28,32,36,41,45,50,55] := by decide

/-- Uniform nontrivial-ring result after specializing the actual tableau to a
residue field; all individual diagonal entries must be units. -/
theorem ring_quadratic_le20 {T : Type*} [CommRing T] [Nontrivial T]
    {A : Fin s → Fin s → T} {b : Fin s → T} (ho : HasTreeOrderAtLeast A b p)
    (ha : ∀ i j, i.val < j.val → A i j=0) (hn : ∀ i, IsUnit (A i i))
    (hp : 0<p) (h20 : p≤20) : quadraticFloor p≤s := by
  exact RKCert.unitDiagonal_of_all_fields (fun _ _ _ _ h₁ h₂ h₃ =>
    nonsingular_quadratic_le20 h₃ h₁ h₂ hp h20) ha hn ho

/-- Strict SDIRK needs just a common unit diagonal, with no support restriction. -/
theorem strict_sdirk_ring_le20 {T : Type*} [CommRing T] [Nontrivial T]
    {A : Fin s → Fin s → T} {b : Fin s → T} {γ : T} (ho : HasTreeOrderAtLeast A b p)
    (ha : ∀ i j, i.val < j.val → A i j=0) (he : ∀ i, A i i=γ) (hγ : IsUnit γ)
    (hp : 0<p) (h20 : p≤20) : quadraticFloor p≤s := by
  exact ring_quadratic_le20 ho ha (fun i => he i ▸ hγ) hp h20

end RKCert.Paired.SDIRK

