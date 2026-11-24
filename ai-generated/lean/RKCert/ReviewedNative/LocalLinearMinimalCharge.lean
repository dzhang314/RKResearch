module

public import RKCert.ReviewedNative.LocalLinearHiddenKernel

@[expose] public section

/-! Draft only. If the paid local reverse head has the minimum number of
clocks, the full orbit buys an outgoing Hermite charge into the genuine
reverse flag. It need not be the whole source flag. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p h r : ℕ} {A : Matrix (Fin s) (Fin s) K} {b τ : Fin s→K}
variable {U : Submodule K (Fin s→K)}

set_option maxHeartbeats 800000 in
theorem local_linear_minimal_sites_paid_gain
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ)
    (rankU : finrank K U=r)
    (sites : r+(weightedSites (reflectedClock A) τ).card=h+2)
    (pay : h+3≤p) (m : ℕ) (charge : 2*m≤h+3) :
    h+2+m≤finrank K (primitiveBack A b (h+2)) := by
  let y := reflectedClock A
  let n := (weightedSites y τ).card
  let B := weightedBand y τ n
  let C := diag y
  let D := U⊔B
  let L := primitiveBack A b
  have npos : 0<n := by
    have test := F.site_count
    change h+1-r<n at test
    omega
  change r+n=h+2 at sites
  have Brank : finrank K B=n := weightedBand_rank y τ n le_rfl
  have asOrbit : B=(weightedEval y τ).range := weightedBand_eq_range y τ n le_rfl
  have Binv : B.map C≤B := by
    rintro _ ⟨v,hv,rfl⟩
    rw [asOrbit] at hv ⊢
    obtain ⟨P,rfl⟩ := hv
    refine ⟨X*P,?_⟩
    ext i
    simp only [weightedEval_apply,eval_mul,eval_X,C,diag_apply]
    ring
  have Borth : B≤annih U := by
    intro v hv
    rw [asOrbit] at hv
    obtain ⟨P,rfl⟩ := hv
    apply mem_annih.mpr
    intro w hw
    have z := mem_annih.mp F.headOrthogonal _ (reflected_clock_weighted_core F.invariant hw P)
    rw [row_apply,dotProduct] at z ⊢
    convert z using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [weightedEval_apply,y]
    ring
  have dis : U⊓B=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have e := eq_zero_of_self_row_zero (mem_annih.mp (Borth hv.2) _ hv.1)
    simpa only [e] using (⊥ : Submodule K (Fin s→K)).zero_mem
  have Ddim : finrank K D=h+2 := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq U B
    rw [dis,finrank_bot,add_zero,rankU,Brank,sites] at e
    exact e
  have Dinv : D.map C≤D := by
    change (U⊔B).map C≤U⊔B
    rw [Submodule.map_sup]
    exact sup_le (F.invariant.trans le_sup_left) (Binv.trans le_sup_right)
  have mono : Monotone L := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have Bpay : B≤L (h+1) := by
    intro v hv
    obtain ⟨P,deg,e⟩ := mem_weightedBand.mp hv
    rw [←e]
    have Pd : P.natDegree≤n-1 := by
      by_cases pz : P=0
      · simp [pz]
      · have z := (natDegree_lt_iff_degree_lt pz).mpr deg
        omega
    have ok := weighted_primitive_band F.headMem P Pd
    rwa [show r+(n-1)=h+1 by omega] at ok
  have Dpay : D≤L (h+1) := sup_le (F.core.le.trans (mono (by omega))) Bpay
  have mask : MaskInvariant y D := clock_mask_invariant
    (fun _ hv=>Dinv (Submodule.mem_map_of_mem hv))
  have mass (v : Fin s→K) (hv : v∈D) : ∑ i,v i=0 := by
    have z := mem_annih.mp (primitiveBack_annih ho 0 (h+1) (by omega) (Dpay hv)) _
      (one_mem_treeSpace A 0)
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using z
  have enough := reverse_failed_clock_blocks ho D mask mass (r:=m) (by omega)
  have moves (v : Fin s→K) (hv : v∈D) : mat A.transpose v∈L (h+2) := by
    have step : (L (h+1)).map (mat A.transpose)≤L (h+2) := adjointFlag_transpose _ _
    exact step (Submodule.mem_map_of_mem (Dpay hv))
  have paid (P : K[X]) (deg : P.natDegree+1≤2*m) :
      mat A.transpose (weightedEval y b P)-weightedEval y b (primitive P)∈L (h+2) :=
    reverse_primitive_next (A:=A) (b:=b) (h+1) P (by omega)
  have gain := ordered_hermite_outgoing Fin.revPerm _ (causal_transpose ha) y b D (L (h+2))
    mask (Dpay.trans (mono (by omega))) moves m enough paid
  rwa [Ddim] at gain

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
