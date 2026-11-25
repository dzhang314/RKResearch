module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor

@[expose] public section

/-! # Exact graded defect descent for a paid Volterra eigenvector -/
namespace RKResearch.Certified.Graded

open FiniteRootedTree Module
open scoped Matrix

section Linear

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- An eigenvector in an injective operator's image of a submodule was
already in that submodule. No inverse or cancellation of the eigenvalue
is needed: if T u=v, then T (r • u)=T v. -/
theorem eigenvector_mem_of_mem_map {T : V →ₗ[R] V} (hinj : Function.Injective T)
    {U : Submodule R V} {v : V} {r : R} (he : T v = r • v)
    (hv : v ∈ U.map T) : v ∈ U := by
  obtain ⟨u, hu, hTu⟩ := Submodule.mem_map.mp hv
  have eq : r • u = v := hinj (by rw [map_smul, hTu, he])
  exact eq ▸ U.smul_mem r hu

end Linear

section Field

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- A paid coefficient packet is separated by the probes of matching degree. -/
theorem paid_coeffEval_eq_zero (ho : RKResearch.HasOrder p A b) {q : ℕ}
    (hpay : 2*q+1 ≤ p) (a : Fin (q+1) → K)
    (hv : ∀ k : Fin (q+1), probe A b k.val (coeffEval A q a) = 0) : a = 0 := by
  ext i
  apply moments_detect ho (d := 1) (by decide) (by omega) (fun i j => by omega) a _ i
  intro k
  have h := hv k
  rwa [probe_coeffEval ho (by omega)] at h

private theorem paid_coeffEval_finrank (ho : RKResearch.HasOrder p A b) {q : ℕ}
    (hpay : 2*q+1 ≤ p) : finrank K (coeffEval A q).range = q+1 := by
  have hi : Function.Injective (coeffEval A q) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    exact paid_coeffEval_eq_zero ho hpay a (fun k => by rw [ha, map_zero])
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]

private theorem coeffEval_range_le {q j : ℕ} (hq : q ≤ j) :
    (coeffEval A q).range ≤ treeSpace A j := by
  rintro _ ⟨a, rfl⟩
  exact treeSpace_mono A hq (coeffEval_mem_treeSpace A q a)

/-- An exact rank step has only the indicated clock packet and genuine
equal-order defects. The entire latter space is the Volterra image
of the earlier tree space. -/
structure ExactVolterraPacket (A : Matrix (Fin s) (Fin s) K) (j q : ℕ) : Prop where
  split : treeSpace A (j+2) = (coeffEval A q).range ⊔ (treeSpace A j).map (volterra A)
  defect : zeroSpace A (j+2) = (treeSpace A j).map (volterra A)

theorem exact_volterra_packet (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) {j q : ℕ}
    (hgrade : q ≤ j+2) (hpay : q+j+3 ≤ p)
    (htight : finrank K (treeSpace A (j+2)) = q+1+finrank K (treeSpace A j)) :
    ExactVolterraPacket A j q := by
  let U := (coeffEval A q).range
  let V := (treeSpace A j).map (volterra A)
  let Z := zeroSpace A (j+2)
  let E := treeSpace A (j+2)
  have hUZ : U ⊔ Z ≤ E := sup_le (coeffEval_range_le hgrade) (zeroSpace_le_treeSpace A _)
  have hVZ : V ≤ Z := by
    rintro _ ⟨u, hu, rfl⟩
    exact volterra_treeSpace ho j (by omega) hu
  have hdis : U ⊓ Z = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨hU, hZ⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, rfl⟩ := hU
    have ha₀ : a = 0 := paid_coeffEval_eq_zero ho (by omega) a (fun k =>
      probe_zeroSpace ho (by omega) hZ)
    rw [ha₀, map_zero]
    exact (⊥ : Submodule K (Fin s → K)).zero_mem
  have hUrank : finrank K U = q+1 := paid_coeffEval_finrank ho (by omega)
  let e : (Fin s → K) ≃ₗ[K] (Fin s → K) :=
    LinearEquiv.ofBijective (volterra A)
      ⟨volterra_injective ha hn, LinearMap.surjective_of_injective (volterra_injective ha hn)⟩
  have hVrank : finrank K V = finrank K (treeSpace A j) := e.finrank_map_eq _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U Z
  rw [hdis, finrank_bot, add_zero, hUrank] at hsum
  have hup := Submodule.finrank_mono hUZ
  have hlo := Submodule.finrank_mono hVZ
  have hE : finrank K E = q+1+finrank K (treeSpace A j) := htight
  have hdef : Z = V := (Submodule.eq_of_le_of_finrank_le hVZ (by omega)).symm
  have heq : U ⊔ Z = E := Submodule.eq_of_le_of_finrank_le hUZ (by omega)
  refine ⟨?_, hdef⟩
  change E = U ⊔ V
  rw [← hdef]
  exact heq.symm

/-- Inside an exact packet, the invisible vectors have no clock
component and lie in the operator image of the preceding space. -/
theorem ExactVolterraPacket.invisible_image {j q : ℕ} {v : Fin s → K}
    (h : ExactVolterraPacket A j q) (ho : RKResearch.HasOrder p A b)
    (hgrade : q ≤ j+2) (hpay : q+j+3 ≤ p)
    (hv : v ∈ treeSpace A (j+2)) (hobs : ∀ k, probe A b k v = 0) :
    v ∈ (treeSpace A j).map (volterra A) := by
  rw [h.split] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := hu
  have hwZ : w ∈ zeroSpace A (j+2) := h.defect.symm ▸ hw
  have ha₀ : a = 0 := by
    apply paid_coeffEval_eq_zero ho (by omega)
    intro k
    have hz : probe A b k.val w = 0 := probe_zeroSpace ho (by omega) hwZ
    simpa only [map_add,hz,add_zero] using hobs k.val
  rw [ha₀,map_zero,zero_add]
  exact hw

private theorem invisible_of_pure_grade (ho : RKResearch.HasOrder p A b) {q : ℕ}
    (hpay : 2*q+1 ≤ p) (hr : finrank K (treeSpace A q) = q+1) {v : Fin s → K}
    (hv : v ∈ treeSpace A q) (hobs : ∀ k, probe A b k v = 0) : v = 0 := by
  have eq : (coeffEval A q).range = treeSpace A q :=
    Submodule.eq_of_le_of_finrank_eq (coeffEval_range_le le_rfl)
      ((paid_coeffEval_finrank ho hpay).trans hr.symm)
  rw [← eq] at hv
  obtain ⟨a, rfl⟩ := hv
  rw [paid_coeffEval_eq_zero ho hpay a (fun k => hobs k.val), map_zero]

/-- A single tight parity rank gives an exact descent to its bottom
clock packet. This proves visibility on any such genuine graded
space, not just at a selected order or distinct-clock configuration. -/
theorem volterra_invisible_of_tight_parity (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (hp : 3 ≤ p)
    {v : Fin s → K} {r : K} (he : volterra A v = r • v)
    (hobs : ∀ k, probe A b k v = 0) :
    ∀ j, j+1 ≤ p → finrank K (treeSpace A j) = parityCensus p j →
      v ∈ treeSpace A j → v = 0
  | 0, _, hr, hv => invisible_of_pure_grade ho (q := 0) (by omega)
      (by simpa only [parityCensus] using hr) hv hobs
  | 1, _, hr, hv => by
      have hc : parityCensus p 1 = 2 := by
        rw [parityCensus, min_eq_left (show 1 ≤ p-2 from by omega)]
      exact invisible_of_pure_grade ho (q := 1) (by omega) (hr.trans hc) hv hobs
  | j+2, hbound, hr, hv => by
      let q := min (j+2) (p-1-(j+2))
      have hq : q ≤ j+2 := Nat.min_le_left _ _
      have hpay : q+j+3 ≤ p := by dsimp [q]; omega
      have hc : parityCensus p (j+2) = q+1+parityCensus p j := rfl
      have hl := parityCensus_le_finrank ho ha hn j (by omega)
      have hs := nonsingular_rank_step ho ha hn j q hq hpay
      have hprev : finrank K (treeSpace A j) = parityCensus p j := by omega
      have hex : finrank K (treeSpace A (j+2)) = q+1+finrank K (treeSpace A j) := by omega
      have pkt := exact_volterra_packet ho ha hn hq hpay hex
      have hv' : v ∈ treeSpace A j :=
        eigenvector_mem_of_mem_map (volterra_injective ha hn) he
          (pkt.invisible_image ho hq hpay hv hobs)
      exact volterra_invisible_of_tight_parity ho ha hn hp he hobs j (by omega) hprev hv'

/-- The actual price-two row cuts out an exact hyperplane whenever the
paid census for its budget is one below the ambient dimension. -/
theorem volterra_hyperplane_of_census (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (hp : 3 ≤ p)
    (hcount : parityCensus p (p-3) + 1 = s) :
    treeSpace A (p-3) = ((probe A b 0).comp (volterra A)).ker ∧
      finrank K (treeSpace A (p-3)) = parityCensus p (p-3) := by
  let L := (probe A b 0).comp (volterra A)
  have hle : treeSpace A (p-3) ≤ L.ker := by
    intro v hv
    change probe A b 0 (volterra A v) = 0
    exact probe_zeroSpace ho (by omega) (volterra_treeSpace ho (p-3) (by omega) hv)
  have hunit : probe A b 0 (1 : Fin s → K) = 1 := by
    simpa only [normTree_leaf,order,PNat.one_coe,Nat.zero_add,Nat.cast_one,one_mul] using
      probe_normTree ho .leaf 0 (by simp only [order,PNat.one_coe]; omega)
  obtain ⟨u,hu⟩ := (LinearMap.surjective_of_injective (volterra_injective ha hn)) 1
  have hLu : L u = 1 := by
    change probe A b 0 (volterra A u) = 1
    rw [hu,hunit]
  have hsur : Function.Surjective L := by
    intro a
    exact ⟨a • u, by rw [map_smul,smul_eq_mul,hLu,mul_one]⟩
  have hnull := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at hnull
  change 1 + finrank K L.ker = s at hnull
  have hib : finrank K (treeSpace A (p-3)) ≤ finrank K L.ker := Submodule.finrank_mono hle
  have hl := parityCensus_le_finrank ho ha hn (p-3) (by omega)
  have hrank : finrank K (treeSpace A (p-3)) = finrank K L.ker := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle hrank, by omega⟩

/-- Global visibility from the exact codimension-one starting census.
No assumption on the weights, clock coincidences, eigenvalue, or
characteristic is used beyond the reviewed order and nonsingularity. -/
theorem volterra_invisible_of_hyperplane_census (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (hp : 3 ≤ p)
    (hcount : parityCensus p (p-3) + 1 = s)
    {v : Fin s → K} {r : K} (he : volterra A v = r • v)
    (hobs : ∀ k, probe A b k v = 0) : v = 0 := by
  obtain ⟨hspace, hr⟩ := volterra_hyperplane_of_census ho ha hn hp hcount
  have hv : v ∈ treeSpace A (p-3) := by
    rw [hspace]
    change probe A b 0 (volterra A v) = 0
    rw [he,map_smul,hobs 0,smul_zero]
  exact volterra_invisible_of_tight_parity ho ha hn hp he hobs (p-3) (by omega) hr hv

end Field
end RKResearch.Certified.Graded
