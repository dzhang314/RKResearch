module

public import RKCert.ReviewedNative.PhysicalSupportExactCover
public import RKCert.ReviewedNative.LocalLinearJointBands

@[expose] public section

/-! # Literal support from an ordinary local census, and the shared feed

Source-only. The support and correction adapter is independent of the
hidden rank. A refined census can use it without adopting the ordinary
triple-label count. No scalar contradiction enters this module. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

private theorem unit_label_separations (Q : K[X]) (T S : Finset K) :
    Disjoint coreLabels (tauLabels Q T) ∧ Disjoint coreLabels (contrastLabels Q S) ∧
      Disjoint (tauLabels Q T) (contrastLabels Q S) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro x hx ha
    change x.2.2 = 1 at hx
    exact one_ne_zero (hx.symm.trans ha.1)
  · intro x hx ha
    change x.2.2 = 1 at hx
    exact one_ne_zero (hx.symm.trans ha.1)
  · intro x ht hs
    exact hs.2.2.1 (ht.2.1.symm.trans hs.2.1)

private theorem live_of_orbit_evaluation_one {y a v : Fin s → K} {i : Fin s}
    (hv : v ∈ completeOrbit y a) (one : v i = 1) : a i ≠ 0 := by
  intro z
  obtain ⟨P, rfl⟩ := hv
  rw [weightedEval_apply, z, mul_zero] at one
  exact zero_ne_one one

/-- Unlike the profile-only cover, the right branches are live on the
original row itself, not only somewhere on its numerical fibre. -/
theorem JointBandCensus.physical_live_cover {y f e τ W : Fin s → K} {Q : K[X]}
    {U J : Submodule K (Fin s → K)} (C : JointBandCensus y f e τ W Q U J)
    (fill : s ≤ finrank K U + finrank K J + (weightedSites y τ).card + (weightedSites y W).card) :
    ∀ i, e i = 1 ∨ (e i = 0 ∧ f i = Q.eval (y i) ∧ τ i ≠ 0) ∨
      (e i = 0 ∧ f i = 0 ∧ Q.eval (y i) ≠ 0 ∧ W i ≠ 0) := by
  obtain ⟨st, sr, tr⟩ := unit_label_separations Q (weightedSites y τ) (weightedSites y W)
  have rank : finrank K (annih U) ≤
      finrank K J + finrank K (completeOrbit y τ) + finrank K (completeOrbit y W) := by
    rw [completeOrbit_rank, completeOrbit_rank]
    have all := finrank_annih U
    rw [Fintype.card_fin] at all
    omega
  have whole := exact_supported_triple_live C.core_on C.tau_on C.contrast_on st sr tr
    (sup_le (sup_le C.coreOrth (completeOrbit_annih C.clockStable C.tauOrth))
      (completeOrbit_annih C.clockStable C.contrastOrth)) rank (fun i => C.indicator _)
  intro i
  rcases whole.2 i with ⟨ci, _, _, _⟩ | ⟨hi, v, hv, v1⟩ | ⟨wi, v, hv, v1⟩
  · exact Or.inl ci
  · exact Or.inr (Or.inl ⟨hi.1, hi.2.1, live_of_orbit_evaluation_one hv v1⟩)
  · exact Or.inr (Or.inr ⟨wi.1, wi.2.1, wi.2.2.1, live_of_orbit_evaluation_one hv v1⟩)

/-- Common geometric input to the paid four-block ports. The compensating
weight trace is separate, and can have either early reverse-core rank. -/
structure UnitCleanFourFeed (A : Matrix (Fin s) (Fin s) K)
    (b τ h W k θ : Fin s → K) (U : Submodule K (Fin s → K)) (P : K[X]) : Prop where
  live : P ≠ 0
  degree : P.natDegree ≤ 5
  headGrade : h ∈ zeroSpace A 5
  correction : k ∈ hiddenKernel b τ U
  formula : θ = evalNodes A P - h - k
  support : ∀ i, θ i ≠ 0 ↔ W i ≠ 0
  value : ∀ i, θ i ≠ 0 → θ i = P.eval (nodes A i)
  sites : (weightedSites (nodes A) θ).card = 4
  tauOff : ∀ i, θ i ≠ 0 → τ i = 0
  clean : ∀ i, θ i ≠ 0 → ∀ v ∈ zeroSpace A 9, v i = 0

set_option maxHeartbeats 800000 in
theorem unit_clean_four_feed_of_live_cover
    {A : Matrix (Fin s) (Fin s) K} {b τ h W e : Fin s → K}
    {U : Submodule K (Fin s → K)} {Q : K[X]}
    (kinv : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    (h5 : h ∈ zeroSpace A 5) (hInv : U.map (diag h) ≤ U)
    (eK : e ∈ hiddenKernel b τ U) (binary : ∀ i, e i = 0 ∨ e i = 1)
    (tauRows : ∀ i, τ i ≠ 0 → h i = Q.eval (reflectedClock A i))
    (wRows : ∀ i, W i ≠ 0 → e i = 0 ∧ h i = 0 ∧ Q.eval (reflectedClock A i) ≠ 0)
    (outside : ∀ i, e i = 0 → h i ≠ Q.eval (reflectedClock A i) → W i ≠ 0)
    (wt4 : (weightedSites (reflectedClock A) W).card = 4)
    (qn : Q ≠ 0) (qd : Q.natDegree ≤ 5)
    (clean : ∀ i, W i ≠ 0 → ∀ v ∈ zeroSpace A 9, v i = 0) :
    ∃ k θ, UnitCleanFourFeed A b τ h W k θ U (Q.comp (1-X)) := by
  let y := reflectedClock A
  let L : K[X] := 1-X
  let P := Q.comp L
  have dL : L.natDegree ≤ 1 := by
    change (1-X : K[X]).natDegree ≤ 1
    exact (natDegree_sub_le (1 : K[X]) X).trans (by simp)
  have dP : P.natDegree ≤ 5 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul qd dL).trans_eq (Nat.mul_one 5))
  have LL : L.comp L = X := by
    simp only [L, sub_comp, one_comp, X_comp]
    ring
  have Pn : P ≠ 0 := by
    intro pz
    have eq : P.comp L = Q := by
      dsimp only [P]
      rw [comp_assoc, LL, comp_X]
    rw [pz, zero_comp] at eq
    exact qn eq.symm
  have reflectAt (i : Fin s) : P.eval (nodes A i) = Q.eval (y i) := by
    simp only [P, L, y, reflectedClock, eval_comp, eval_sub, eval_one, eval_X,
      Pi.sub_apply, Pi.one_apply]
  let k := weightedEval (nodes A) e P - h*e
  have kJ : k ∈ hiddenKernel b τ U := (hiddenKernel b τ U).sub_mem
    (reflected_clock_weighted_core kinv eK P) (hiddenKernel_external_mul eK hInv)
  let θ := evalNodes A P - h - k
  have diff (i : Fin s) : θ i = (1-e i)*(Q.eval (y i)-h i) := by
    simp only [θ, k, Pi.sub_apply, Pi.mul_apply, evalNodes_apply, weightedEval_apply, reflectAt i]
    ring
  have sup (i : Fin s) : θ i ≠ 0 ↔ W i ≠ 0 := by
    constructor
    · intro hi
      have ei : e i = 0 := by
        rcases binary i with iz | io
        · exact iz
        · exact (hi (by rw [diff, io, sub_self, zero_mul])).elim
      have hd : h i ≠ Q.eval (y i) := by
        intro same
        exact hi (by rw [diff, same, sub_self, mul_zero])
      exact outside i ei hd
    · intro wi
      obtain ⟨ei, hi, qi⟩ := wRows i wi
      simpa only [diff, ei, hi, sub_zero, one_mul] using qi
  have θValue (i : Fin s) (hi : θ i ≠ 0) : θ i = P.eval (nodes A i) := by
    obtain ⟨ei, hi0, _⟩ := wRows i ((sup i).mp hi)
    simpa only [diff, ei, hi0, sub_zero, one_mul] using (reflectAt i).symm
  have noTau (i : Fin s) (hi : θ i ≠ 0) : τ i = 0 := by
    obtain ⟨_, h0, qi⟩ := wRows i ((sup i).mp hi)
    by_contra ti
    exact qi ((tauRows i ti).symm.trans h0)
  have siteEq : weightedSites (nodes A) θ = (weightedSites y W).image (fun x => 1-x) := by
    ext x
    rw [mem_weightedSites, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, ix⟩
      refine ⟨y i, mem_weightedSites.mpr ⟨i, (sup i).mp hi, rfl⟩, ?_⟩
      change 1-(1-nodes A i) = x
      rw [←ix]
      ring
    · rintro ⟨a, ah, ax⟩
      obtain ⟨i, wi, ia⟩ := mem_weightedSites.mp ah
      refine ⟨i, (sup i).mpr wi, ?_⟩
      calc
        nodes A i = 1-y i := by
          simp only [y, reflectedClock, Pi.sub_apply, Pi.one_apply]
          ring
        _ = 1-a := congrArg (fun t : K => 1-t) ia
        _ = x := ax
  have count : (weightedSites (nodes A) θ).card = 4 := by
    rw [siteEq, Finset.card_image_of_injective _ (fun a b e => (sub_right_inj (a:=1)).mp e)]
    exact wt4
  refine ⟨k, θ, ?_⟩
  change UnitCleanFourFeed A b τ h W k θ U P
  exact ⟨Pn, dP, h5, kJ, rfl, sup, θValue, count, noTau, fun i hi => clean i ((sup i).mp hi)⟩

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
