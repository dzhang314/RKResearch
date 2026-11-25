module
public import RKCert.ReviewedNative.ClockBlockDetection
public import RKCert.ReviewedNative.RowAnnihilator

@[expose] public section

/-! # The clock-local part of a physical row space -/
namespace RKResearch.Certified.Graded.Reverse

open RKCert.Endpoint
open scoped Classical

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

/-- Rows whose zero-extended restriction to each clock fibre belongs to `P`. -/
def clockLocal (c : Fin s → K) (P : Submodule K (Fin s → K)) :
    Submodule K (Fin s → K) :=
  ⨅ x : K, P.comap (diag (fun i => if c i = x then (1 : K) else 0))

theorem mem_clockLocal {c w : Fin s → K} {P : Submodule K (Fin s → K)} :
    w ∈ clockLocal c P ↔ ∀ x, blockMask c x w ∈ P := by
  have mask (x : K) :
      diag (fun i : Fin s => if c i = x then (1 : K) else 0) w = blockMask c x w := by
    funext i
    simp only [diag_apply, blockMask]
    by_cases hi : c i = x <;> simp [hi]
  simp only [clockLocal, Submodule.mem_iInf, Submodule.mem_comap, mask]

theorem clockLocal_le (c : Fin s → K) (P : Submodule K (Fin s → K)) :
    clockLocal c P ≤ P := by
  intro w hw
  have ha : assembleBlocks c (fun _ => w) ∈ P := by
    rw [assembleBlocks]
    exact P.sum_mem (fun x _ => mem_clockLocal.mp hw x)
  have he : assembleBlocks c (fun _ => w) = w := by
    funext i
    exact assembleBlocks_apply c (fun _ => w) i
  simpa only [he] using ha

theorem clockLocal_stable (c : Fin s → K) (P : Submodule K (Fin s → K)) :
    (clockLocal c P).map (diag c) ≤ clockLocal c P := by
  apply Submodule.map_le_iff_le_comap.mpr
  intro w hw
  change diag c w ∈ clockLocal c P
  apply mem_clockLocal.mpr
  intro x
  have he : blockMask c x (diag c w) = x • blockMask c x w := by
    funext i
    simp only [blockMask, diag_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : c i = x <;> simp [hi]
  rw [he]
  exact P.smul_mem x (mem_clockLocal.mp hw x)

/-- Every stable subspace of `P` lies in its clock-local part. -/
theorem le_clockLocal_of_stable {c : Fin s → K} {Q P : Submodule K (Fin s → K)}
    (inc : Q ≤ P) (stable : Q.map (diag c) ≤ Q) : Q ≤ clockLocal c P := by
  have hm : MaskInvariant c Q :=
    clock_mask_invariant (fun w hw => stable (Submodule.mem_map_of_mem hw))
  intro w hw
  exact mem_clockLocal.mpr (fun x => inc (hm x w hw))

theorem clockLocal_eq_iff (c : Fin s → K) (P : Submodule K (Fin s → K)) :
    clockLocal c P = P ↔ P.map (diag c) ≤ P := by
  constructor
  · intro he
    simpa only [he] using clockLocal_stable c P
  · intro stable
    exact le_antisymm (clockLocal_le c P) (le_clockLocal_of_stable le_rfl stable)

/-- Adjoining clock multiples of the columns does not change the clock-local annihilator. -/
theorem clockLocal_annih_clockStep (c : Fin s → K) (X : Submodule K (Fin s → K)) :
    clockLocal c (annih (X ⊔ X.map (diag c))) = clockLocal c (annih X) := by
  let W := clockLocal c (annih X)
  change clockLocal c (annih (X ⊔ X.map (diag c))) = W
  apply le_antisymm
  · have drop : annih (X ⊔ X.map (diag c)) ≤ annih X := annih_antitone le_sup_left
    exact le_clockLocal_of_stable ((clockLocal_le c _).trans drop) (clockLocal_stable c _)
  · have stable : W.map (diag c) ≤ W := clockLocal_stable c (annih X)
    have inAnn : X ≤ annih W := by
      simpa only [annih_annih] using (annih_antitone (clockLocal_le c (annih X)))
    have stableAnn : (annih W).map (diag c) ≤ annih W :=
      annih_map_diag (Submodule.map_le_iff_le_comap.mp stable)
    have step : X ⊔ X.map (diag c) ≤ annih W :=
      sup_le inAnn ((Submodule.map_mono inAnn).trans stableAnn)
    have inside : W ≤ annih (X ⊔ X.map (diag c)) := by
      simpa only [annih_annih] using (annih_antitone step)
    exact le_clockLocal_of_stable inside stable

end
end RKResearch.Certified.Graded.Reverse
