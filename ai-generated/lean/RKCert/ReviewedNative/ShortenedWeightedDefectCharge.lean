module
public import RKCert.ReviewedNative.PaidClockLocalRank
public import RKCert.ReviewedNative.ClockLocalFiberRank
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! # Paid shortened weighted defects on the original clock fibres -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module Polynomial RKCert.Endpoint
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

/-- Restriction to the original coordinates whose clock is outside `S`. -/
def clockComplementRestrict (c : Fin s → K) (S : Finset K) :
    (Fin s → K) →ₗ[K] ({i : Fin s // c i ∉ S} → K) :=
  LinearMap.funLeft K K (Subtype.val : {i : Fin s // c i ∉ S} → Fin s)

/-- Shorten a space by imposing zero on every coordinate outside the chosen clocks. -/
def clockShorten (c : Fin s → K) (S : Finset K) (U : Submodule K (Fin s → K)) :
    Submodule K (Fin s → K) :=
  U ⊓ (clockComplementRestrict c S).ker

theorem mem_clockShorten {c w : Fin s → K} {S : Finset K} {U : Submodule K (Fin s → K)} :
    w ∈ clockShorten c S U ↔ w ∈ U ∧ ∀ i, c i ∉ S → w i = 0 := by
  rw [clockShorten, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨inU, off⟩
    exact ⟨inU, fun i hi => congrFun off ⟨i, hi⟩⟩
  · rintro ⟨inU, off⟩
    refine ⟨inU, ?_⟩
    funext i
    exact off i.val i.property

/-- The rank lost on puncturing at the complementary clocks is exactly the shortened rank. -/
theorem finrank_clockShorten_add_punctured
    (c : Fin s → K) (S : Finset K) (U : Submodule K (Fin s → K)) :
    finrank K (U.map (clockComplementRestrict c S)) + finrank K (clockShorten c S U) =
      finrank K U := by
  let f := clockComplementRestrict c S
  have ker_eq : (f.domRestrict U).ker = (clockShorten c S U).comap U.subtype := by
    rw [LinearMap.ker_domRestrict, clockShorten, Submodule.comap_inf,
      Submodule.comap_subtype_self, top_inf_eq]
  have inside : clockShorten c S U ≤ U := inf_le_left
  have rank_eq : finrank K ((clockShorten c S U).comap U.subtype) =
      finrank K (clockShorten c S U) :=
    (Submodule.comapSubtypeEquivOfLe inside).finrank_eq
  have dim := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, ker_eq, rank_eq] at dim
  exact dim

/-- Restriction ranks of a subspace sum to at most the rank of any clock-stable container. -/
theorem sum_finrank_clockFiberColumns_le_of_stable {c : Fin s → K}
    {U W : Submodule K (Fin s → K)} (inside : U ≤ W) (stable : W.map (diag c) ≤ W) :
    (∑ x : ClockSite c, finrank K (clockFiberColumns c U x)) ≤ finrank K W := by
  have dualStable : (annih W).map (diag c) ≤ annih W :=
    annih_map_diag (Submodule.map_le_iff_le_comap.mp stable)
  have dualInc : annih W ≤ clockLocal c (annih U) :=
    le_clockLocal_of_stable (annih_antitone inside) dualStable
  have incRank := Submodule.finrank_mono dualInc
  have dimW := finrank_annih W
  rw [Fintype.card_fin] at dimW
  have dimU := finrank_clockLocal_annih_add_sum_eq c U
  omega

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {p j g n : ℕ}

abbrev clockWeightedDefect (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (g : ℕ) :=
  (zeroSpace A g).map (diag b)

abbrev shortenedWeightedDefect (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (g : ℕ) (S : Finset K) :=
  clockShorten (nodes A) S (clockWeightedDefect A b g)

/-- Payment uses the allowed clocks of the weighted defect, not every stage clock.
There is no nonzero-weight, sign, or strict-triangularity premise. -/
theorem paid_weightedDefect_mem_clockLocal (ho : HasOrder p A b) {u : Fin s → K}
    (hu : u ∈ zeroSpace A g) (S : Finset K)
    (off : ∀ i, nodes A i ∉ S → diag b u i = 0) (pay : j + g + S.card ≤ p) :
    diag b u ∈ clockLocal (nodes A) (annih (treeSpace A j)) := by
  apply mem_clockLocal.mpr
  intro x
  by_cases hx : x ∈ S
  · let L : K[X] := Lagrange.basis S id x
    have inj : Set.InjOn (id : K → K) (↑S : Set K) := Set.injOn_id _
    have ld : L.natDegree = S.card - 1 := Lagrange.natDegree_basis inj hx
    have Lx : L.eval x = 1 := Lagrange.eval_basis_self inj hx
    have maskEq : blockMask (nodes A) x (diag b u) = diag (evalNodes A L) (diag b u) := by
      funext i
      rw [blockMask, diag_apply (evalNodes A L) (diag b u) i, evalNodes_apply]
      by_cases he : nodes A i = x
      · rw [if_pos he, he, Lx, one_mul]
      · rw [if_neg he]
        by_cases hi : nodes A i ∈ S
        · have Li : L.eval (nodes A i) = 0 :=
            Lagrange.eval_basis_of_ne (s := S) (v := id) (fun e => he e.symm) hi
          rw [Li, zero_mul]
        · rw [off i hi, mul_zero]
    have cv : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    have eL : evalNodes A L ∈ treeSpace A (S.card - 1) := evalNodes_mem_treeSpace A L ld.le
    apply mem_annih.mpr
    intro v hv
    have prod : u * (evalNodes A L * v) ∈ zeroSpace A (g + ((S.card - 1) + j)) :=
      zeroSpace_mul_treeSpace ho (by omega) hu (treeSpace_mul eL hv)
    have zero : probe A b 0 (u * (evalNodes A L * v)) = 0 :=
      LinearMap.mem_ker.mp
        ((probe_zeroSpace (j := g + ((S.card - 1) + j)) (k := 0) ho (by omega)) prod)
    have flip : diag b u = diag u b := by
      funext i
      simpa only [diag_apply] using (mul_comm (b i) (u i))
    rw [maskEq, flip, row_diag, row_diag]
    change row b (u * (evalNodes A L * v)) = 0
    simpa only [probe, pow_zero, mul_one] using zero
  · have maskZero : blockMask (nodes A) x (diag b u) = 0 := by
      funext i
      by_cases he : nodes A i = x
      · rw [blockMask, if_pos he]
        exact off i (fun hi => hx (he ▸ hi))
      · simp [blockMask, he]
    rw [maskZero]
    exact (annih (treeSpace A j)).zero_mem

theorem paid_shortenedWeightedDefect_le_clockLocal (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    shortenedWeightedDefect A b g S ≤ clockLocal (nodes A) (annih (treeSpace A j)) := by
  intro w hw
  obtain ⟨inU, off⟩ := mem_clockShorten.mp hw
  change w ∈ (zeroSpace A g).map (diag b) at inU
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp inU
  exact paid_weightedDefect_mem_clockLocal (j := j) (g := g) ho hu S off pay

/-- The exact sum of original-fibre ranks charges the local annihilator dimension. -/
theorem paid_shortenedWeightedDefect_clock_charge (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    (∑ x : ClockSite (nodes A),
      finrank K (clockFiberColumns (nodes A) (shortenedWeightedDefect A b g S) x)) ≤
      finrank K (clockLocal (nodes A) (annih (treeSpace A j))) :=
  sum_finrank_clockFiberColumns_le_of_stable
    (paid_shortenedWeightedDefect_le_clockLocal (j := j) (g := g) ho S pay)
    (clockLocal_stable (nodes A) (annih (treeSpace A j)))

theorem paid_shortenedWeightedDefect_clock_charge_of_staircase
    (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    (∑ x : ClockSite (nodes A),
      finrank K (clockFiberColumns (nodes A) (shortenedWeightedDefect A b g S) x)) ≤
      finrank K (back A b 0) + 1 :=
  (paid_shortenedWeightedDefect_clock_charge (j := j) (g := g) ho S pay).trans
    (paid_clock_local_rank_of_staircase H positive).rankCap

/-- Rank form of the same test, using only restriction to clocks outside `S`. -/
theorem paid_weightedDefect_rank_le_punctured_add_of_staircase
    (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) (ho : HasOrder p A b)
    (S : Finset K) (pay : j + g + S.card ≤ p) :
    finrank K (clockWeightedDefect A b g) ≤
      finrank K ((clockWeightedDefect A b g).map (clockComplementRestrict (nodes A) S)) +
        (finrank K (back A b 0) + 1) := by
  let U := clockWeightedDefect A b g
  have charge : finrank K (clockShorten (nodes A) S U) ≤ finrank K (back A b 0) + 1 :=
    (Submodule.finrank_mono (paid_shortenedWeightedDefect_le_clockLocal (j := j) (g := g) ho S pay)).trans
      (paid_clock_local_rank_of_staircase H positive).rankCap
  calc
    finrank K U = finrank K (U.map (clockComplementRestrict (nodes A) S)) +
        finrank K (clockShorten (nodes A) S U) :=
      (finrank_clockShorten_add_punctured (nodes A) S U).symm
    _ ≤ _ := Nat.add_le_add_left charge _

end
end RKResearch.Certified.Graded.Reverse
