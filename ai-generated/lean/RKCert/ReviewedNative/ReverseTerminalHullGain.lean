module

public import RKCert.ReviewedNative.ReverseClockGain
public import RKCert.ReviewedNative.ERK17ReverseSupport
public import RKCert.ReviewedNative.EndpointAdjoint

@[expose] public section

/-! # Clock-hull gain with an independently paid terminal coordinate

The whole numerical quadratic seed hull is stable once it is taken
through its site rank. It need not equal any primitive flag. Its
outgoing Hermite debit and the independent terminal-coordinate
debit are both paid in the original reverse flag. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- If the actual nonzero quadratic seed has u distinct clock sites,
its completed hull pays u plus the next outgoing Hermite debit; an
original terminal coordinate absent from E_j pays one more. -/
theorem primitiveBack_terminal_hull_budget
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    {t : Fin s} (last : LastActive b t) (first : firstSeed A b=0) {j u : ℕ}
    (sites : (weightedSites (reflectedClock A) (quadraticSeed A b)).card=u)
    (pos : 1≤u) (pay : j+u+3≤p) (outside : coordinate (K:=K) t∉treeSpace A j) :
    finrank K (treeSpace A j)+u+(u+2)/2+1≤s := by
  let y := reflectedClock A
  let d := quadraticSeed A b
  let W := (weightedEval y d).range
  let r := (u+2)/2
  have eq : weightedBand y d u=W := weightedBand_eq_range y d u sites.le
  have rk : finrank K W=u := eq ▸ weightedBand_rank y d u sites.ge
  have seed : d∈primitiveBack A b 1 :=
    adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have inc : W≤primitiveBack A b u := by
    rw [←eq]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u≠0)
    simpa only [Nat.add_comm 1 k] using weighted_band_of_primitive_seed seed k
  have mask : MaskInvariant y W := clock_mask_invariant
    (fun v hv => weighted_range_clock y d hv)
  have mass (v : Fin s→K) (hv : v∈W) : ∑ i,v i=0 := by
    have h := mem_annih.mp (primitiveBack_annih ho 0 u (by omega) (inc hv)) _
      (one_mem_treeSpace A 0)
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using h
  have failed := reverse_failed_clock_blocks ho W mask mass (r:=r) (by dsimp [r];omega)
  have gain := ordered_hermite_outgoing Fin.revPerm (mat A.transpose) (causal_transpose ha)
    y b W (primitiveBack A b (u+1)) mask
    (inc.trans (adjointFlag_le_succ _ _))
    (fun _ h => adjointFlag_transpose _ _ (Submodule.mem_map_of_mem (inc h)))
    r failed (fun P dP => reverse_primitive_next u P (by dsimp [r] at dP;omega))
  change finrank K W+r≤finrank K (primitiveBack A b (u+1)) at gain
  rw [rk] at gain
  have cover : primitiveBack A b (u+1)≤zeroAt (annih (treeSpace A j)) t := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho j (u+1) (by omega) hv,
      mem_tailZero.mp (last.primitiveBack_tail ha first _ hv) t le_rfl⟩
  have rank := Submodule.finrank_mono cover
  have debit := finrank_zeroAt_annih (treeSpace A j) t outside
  have complementary := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at complementary
  change u+r≤finrank K (primitiveBack A b (u+1)) at gain
  change finrank K (treeSpace A j)+u+r+1≤s
  omega

end
end RKResearch.Certified.Graded.Reverse
