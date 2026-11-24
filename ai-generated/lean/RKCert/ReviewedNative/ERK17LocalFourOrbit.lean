module

public import RKCert.ReviewedNative.ERK17LocalFourAxisPayment
public import RKCert.ReviewedNative.ReverseClockGain

@[expose] public section

/-! # Actual reverse rank cost for invariant subspaces of a full annihilator

An invariant paid orbit need not equal, or even lie in, a specified
primitive flag. The transpose moves it by full tree-span pairing; only
the independent primitive generators charge the primitive flag. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module Polynomial RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

theorem reverse_annihilator_invariant_gain
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b) (m k : ℕ)
    (pay : m+k+3≤p) {V : Submodule K (Fin s→K)}
    (inside : V≤annih (treeSpace A (m+1))) (stable : V.map (diag (reflectedClock A))≤V) :
    finrank K V+(k+2)/2≤finrank K (annih (treeSpace A m)) := by
  let Y := reflectedClock A
  let Z := annih (treeSpace A m)
  let r := (k+2)/2
  have mask : MaskInvariant Y V := clock_mask_invariant (fun _ hv=>stable (Submodule.mem_map_of_mem hv))
  have mass (v : Fin s→K) (hv : v∈V) : (∑ i,v i)=0 := by
    have a := mem_annih.mp (inside hv) _ (one_mem_treeSpace A (m+1))
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using a
  have paid : 2*r≤p := by dsimp [r]; omega
  have count := reverse_failed_clock_blocks ho V mask mass paid
  have sub : V≤Z := inside.trans (annih_antitone (treeSpace_mono A (Nat.le_succ m)))
  have shifted : V.map (mat A.transpose)≤Z := (Submodule.map_mono inside).trans
    (annih_map_transpose (mat_treeSpace A m))
  apply ordered_hermite_outgoing Fin.revPerm (mat A.transpose) (causal_transpose ha) Y b V Z mask sub
    (fun _ hv=>shifted (Submodule.mem_map_of_mem hv)) r count
  intro P hp
  apply primitiveBack_annih ho m (k+1) (by omega)
  exact reverse_primitive_next k P (by dsimp [r] at hp; omega)

end
end RKResearch.Certified.Graded.Reverse

namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26→K}
variable {U : Submodule K (Fin 26→K)}

theorem width26_rank_four_reverse_invariant_cap
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (rich : 7≤finrank K (zeroSpace A 6)) {B : Submodule K (Fin 26→K)}
    (inside : B≤annih (treeSpace A 7)) (inv : B.map (diag (reflectedClock A))≤B) :
    finrank K B≤7 := by
  have go := reverse_annihilator_invariant_gain ha ho 6 8 (by decide) inside inv
  change finrank K B+5≤finrank K (annih (treeSpace A 6)) at go
  have fr := treeSpace_rank_eq_of_separation ho (q:=6) (by decide) (coeff_separated ho (by decide))
  have eq := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin] at eq
  omega

/-- Neither an ordinary τ-orbit nor a rational advance can place a whole
seven-site invariant band in Ann(E7), even with an arbitrary early-core
coordinate support. -/
theorem width26_rank_four_no_paid_complete_orbit
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 2 U τ) (rich : 7≤finrank K (zeroSpace A 6))
    (v : Fin 26→K) (many : 7≤(weightedSites (reflectedClock A) v).card) (orth : v∈annih U)
    (pay : (weightedEval (reflectedClock A) v).range≤annih (treeSpace A 7)) : False := by
  let y := reflectedClock A
  let V := (weightedEval y v).range
  have Uin : U≤annih (treeSpace A 7) := by
    have e : U=primitiveBack A b 1 := F.core
    rw [e]
    exact primitiveBack_annih ho 7 1 (by decide)
  have rU : finrank K U=2 := by
    have S := (ordered_width26_full_frame ha ho).1
    have e : U=primitiveBack A b 1 := F.core
    obtain ⟨r,eq⟩ := S.reverse.flagExact 1 (by decide)
    rw [e,←eq,r,first_dim_one nz]
  have rV : finrank K V=(weightedSites y v).card := by
    have fit := weightedBand_eq_range y v (weightedSites y v).card le_rfl
    change _=V at fit
    rw [←fit,weightedBand_rank _ _ _ le_rfl]
  have Vorth : V≤annih U := by
    rintro _ ⟨P,rfl⟩
    apply mem_annih.mpr
    intro u hu
    have o := mem_annih.mp orth _ (reflected_clock_weighted_core F.invariant hu P)
    rw [row_apply,dotProduct] at o ⊢
    convert o using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [weightedEval_apply]
    ring
  have dis : U⊓V=⊥ := by
    apply le_antisymm _ bot_le
    rintro u ⟨hu,hv⟩
    rw [eq_zero_of_self_row_zero (mem_annih.mp (Vorth hv) u hu)]
    exact (⊥:Submodule K (Fin 26→K)).zero_mem
  have Vinv : V.map (diag y)≤V := by
    rintro _ ⟨w,hw,rfl⟩
    exact weighted_range_clock y v hw
  have Vinv' : (U⊔V : Submodule K (Fin 26→K)).map (diag y)≤U⊔V := by
    rw [Submodule.map_sup]
    exact sup_le (F.invariant.trans le_sup_left) (Vinv.trans le_sup_right)
  have cap := width26_rank_four_reverse_invariant_cap ha ho rich (sup_le Uin pay) Vinv'
  have cd := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [dis,finrank_bot,add_zero,rU,rV] at cd
  change 7≤(weightedSites y v).card at many
  change finrank K (U ⊔ V : Submodule K (Fin 26 → K)) ≤ 7 at cap
  omega

theorem width26_local_four_tau_at_least_eight
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 2 U τ) (rich : 7≤finrank K (zeroSpace A 6)) :
    8≤(weightedSites (reflectedClock A) τ).card := by
  let y := reflectedClock A
  have head : 7≤(weightedSites y τ).card := by
    have e := F.site_count
    change 6 < (weightedSites y τ).card at e
    omega
  change 8≤(weightedSites y τ).card
  by_contra! small
  have eq := weightedBand_eq_range y τ 7 (by omega)
  apply width26_rank_four_no_paid_complete_orbit ha ho nz F rich τ head F.headOrthogonal
  rw [←eq]
  intro w hw
  obtain ⟨P,d,rfl⟩ := mem_weightedBand.mp hw
  have pd : P.natDegree≤6 := by
    by_cases z : P=0
    · simp [z]
    have n := (natDegree_lt_iff_degree_lt z).mpr d
    omega
  exact local_four_low_head_paid_E7 ho F P pd

end
end RKResearch.Certified.ERK17
