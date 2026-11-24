module

public import RKCert.ReviewedNative.ERK17WidthFrame
public import RKCert.ReviewedNative.WeightedClockBand

@[expose] public section

/-! # The actual reverse support split at width twenty-six

Large support means polynomial coverage of the original annihilator, not
an arbitrary choice of numerical roots. The missing local cases are left
visible: at most two first-seed sites, or one quadratic-seed site. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
noncomputable section

/-- All powers of an actually paid seed remain in the corresponding
later native primitive flag, with one grade charged per multiplication. -/
theorem weighted_band_of_primitive_seed {v : Fin s → K} {j : ℕ}
    (seed : v ∈ primitiveBack A b j) (n : ℕ) :
    weightedBand (reflectedClock A) v (n+1) ≤ primitiveBack A b (j+n) := by
  let W := weightedEval (reflectedClock A) v
  have powers (k : ℕ) : W (X^k) ∈ primitiveBack A b (j+k) := by
    induction k with
    | zero =>
      have e : W 1 = v := by ext i; simp [W]
      simpa only [pow_zero,e,Nat.add_zero] using seed
    | succ k ih =>
      have z := adjointFlag_clock (monomialCredit A b) (j+k) (Submodule.mem_map_of_mem ih)
      have e : diag (reflectedClock A) (W (X^k)) = W (X^(k+1)) := by
        ext i
        simp only [diag_apply,W,weightedEval_apply,eval_pow,eval_X]
        rw [pow_succ']
        ring
      change diag (reflectedClock A) (W (X^k)) ∈ primitiveBack A b (j+k+1) at z
      rw [e] at z
      exact z
  have mono : Monotone (primitiveBack A b) := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  intro w hw
  obtain ⟨P,d,rfl⟩ := mem_weightedBand.mp hw
  by_cases z : P=0
  · rw [z,map_zero]
    exact (primitiveBack A b (j+n)).zero_mem
  have deg : P.natDegree < n+1 := (natDegree_lt_iff_degree_lt z).mpr d
  change W P ∈ _
  rw [P.as_sum_range' (n+1) deg,map_sum]
  apply Submodule.sum_mem
  intro k hk
  rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul]
  exact (primitiveBack A b (j+n)).smul_mem _ (mono (by have := Finset.mem_range.mp hk; omega) (powers k))

end
end RKResearch.Certified.Graded.Reverse

namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
noncomputable section

def WideLinear (A : Matrix (Fin 26) (Fin 26) K) (b : Fin 26 → K) : Prop :=
  9 ≤ (weightedSites (reflectedClock A) (firstSeed A b)).card ∧
    annih (treeSpace A 8) = weightedBand (reflectedClock A) (firstSeed A b) 8

omit [CharZero K] in
private theorem full_band_invariant (y d : Fin 26 → K) {L : Submodule K (Fin 26 → K)}
    (eq : L = (weightedEval y d).range) : L.map (diag y) ≤ L := by
  rintro w ⟨v,hv,rfl⟩
  rw [eq] at hv ⊢
  exact weighted_range_clock y d hv

set_option maxRecDepth 3500 in
set_option maxHeartbeats 600000 in
/-- If the first seed does not vanish, the intermediate 3–8-clock band is
impossible. In the wide branch all true annihilators are paid polynomials. -/
theorem width26_linear_broad_or_local (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 17 A b) (S : OddBalancedFrame A b 8 2) (nz : firstSeed A b ≠ 0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2 ∨ WideLinear A b := by
  let y := reflectedClock A
  let d := firstSeed A b
  let c := (weightedSites y d).card
  let L := primitiveBack A b
  have dm : d ∈ L 0 := Submodule.mem_span_singleton_self d
  have inc (n : ℕ) : weightedBand y d (n+1) ≤ L n := by
    simpa only [Nat.zero_add] using (weighted_band_of_primitive_seed dm n)
  have ranks (n : ℕ) (hn : n≤7) : finrank K (L n)=n+1 := by
    obtain ⟨rank,e⟩ := S.reverse.flagExact n hn
    change back A b n = L n at e
    rw [←e,rank,first_dim_one nz]
  change c≤2 ∨ WideLinear A b
  by_cases tiny : c≤2
  · exact Or.inl tiny
  right
  have big : 9≤c := by
    by_contra! smaller
    let n := c-1
    have eq : n+1=c := by dsimp [n]; omega
    have n7 : n≤7 := by dsimp [n]; omega
    have n2 : 2≤n := by dsimp [n]; omega
    have enough : n+1 ≤ (weightedSites y d).card := eq.le
    have back : (weightedSites y d).card ≤ n+1 := eq.ge
    have E : weightedBand y d (n+1)=L n := by
      apply Submodule.eq_of_le_of_finrank_le (inc n)
      rw [ranks n n7,weightedBand_rank y d _ enough]
    have sat : L n = (weightedEval y d).range := E.symm.trans (weightedBand_eq_range y d _ back)
    exact width26_reverse_clock_escape ha ho S n2 n7 (full_band_invariant y d sat)
  have E : weightedBand y d 8=L 7 := by
    apply Submodule.eq_of_le_of_finrank_le (inc 7)
    rw [ranks 7 (by decide),weightedBand_rank y d _ (show 8≤c by omega)]
  have ann : L 7 = annih (treeSpace A 8) :=
    (S.reverse.flagExact 7 (by decide)).2.symm.trans (S.reverse.firstNonzero nz)
  exact ⟨big,ann.symm.trans E.symm⟩

omit [CharZero K] in
theorem WideLinear.poly_cover (B : WideLinear A b) {w : Fin 26 → K}
    (hw : w ∈ annih (treeSpace A 8)) :
    ∃ P : K[X], P.natDegree ≤ 7 ∧ weightedEval (reflectedClock A) (firstSeed A b) P = w := by
  rw [B.2] at hw
  obtain ⟨P,d,e⟩ := mem_weightedBand.mp hw
  refine ⟨P,?_,e⟩
  by_cases hz : P=0
  · simp [hz]
  · have lt : P.natDegree < 8 := (natDegree_lt_iff_degree_lt hz).mpr d
    omega

set_option maxRecDepth 3500 in
set_option maxHeartbeats 650000 in
/-- The same gap excludes intermediate 2–7 quadratic clock sites. The
one-site exceptional branch is not assumed closed by this lemma. -/
theorem width26_quadratic_wide_of_two_sites (ha : ∀ i j, i ≤ j → A i j=0)
    (ho : HasOrder 17 A b) (S : OddBalancedFrame A b 8 2) (zero : firstSeed A b = 0)
    (atLeastTwo : 2 ≤ (weightedSites (reflectedClock A) (quadraticSeed A b)).card) :
    8 ≤ (weightedSites (reflectedClock A) (quadraticSeed A b)).card ∧
    ∃ t : Fin 26, LastActive b t ∧ nodes A t=1 ∧ quadraticSeed A b t=0 ∧
      zeroAt (annih (treeSpace A 8)) t = weightedBand (reflectedClock A) (quadraticSeed A b) 7 := by
  let y := reflectedClock A
  let d := quadraticSeed A b
  let c := (weightedSites y d).card
  let L := primitiveBack A b
  have dm : d ∈ L 1 := adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have inc (n : ℕ) (hn : 1≤n) : weightedBand y d n ≤ L n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simpa only [Nat.add_comm 1 k] using (weighted_band_of_primitive_seed dm k)
  have ranks (n : ℕ) (hn : n≤7) : finrank K (L n)=n := by
    obtain ⟨rank,e⟩ := S.reverse.flagExact n hn
    change back A b n = L n at e
    rw [←e,rank,first_dim_zero zero,add_zero]
  have big : 8≤c := by
    by_contra! smaller
    have lo : 2≤c := atLeastTwo
    have hi : c≤7 := by omega
    have E : weightedBand y d c=L c := by
      apply Submodule.eq_of_le_of_finrank_le (inc c (by omega))
      rw [ranks c hi,weightedBand_rank y d _ le_rfl]
    have sat : L c = (weightedEval y d).range :=
      E.symm.trans (weightedBand_eq_range y d _ le_rfl)
    exact width26_reverse_clock_escape ha ho S lo hi (full_band_invariant y d sat)
  have E : weightedBand y d 7=L 7 := by
    apply Submodule.eq_of_le_of_finrank_le (inc 7 (by decide))
    rw [ranks 7 (by decide),weightedBand_rank y d _ (show 7≤c by omega)]
  obtain ⟨t,last,one,_,ann⟩ := S.reverse.firstZero zero
  have d0 := (mem_tailZero.mp (last.seed_tail ha zero 1)) t le_rfl
  have eq : L 7 = zeroAt (annih (treeSpace A 8)) t :=
    (S.reverse.flagExact 7 (by decide)).2.symm.trans ann
  exact ⟨big,t,last,one,d0,eq.symm.trans E.symm⟩

end
end RKResearch.Certified.ERK17
