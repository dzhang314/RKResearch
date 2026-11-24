module

public import RKCert.ReviewedNative.ERK19LocalFiveGeometry

@[expose] public section

/-! Draft conditional degree-four endpoint. The rank-five support-dimension
census is a separate obligation: these declarations do not assert it. -/
namespace RKResearch.Certified.Graded.LocalFivePorts
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

/-- Chronological 4+3 with an actual degree-four rectangular budget.
Three support clocks suffice; any original zero clock is harmless. -/
theorem quintic_eq_zero_of_four_paid_tests
    (ha : ∀ i j,i≤j→A i j=0) {θ : Fin s→K} {Q : K[X]} (q5 : Q.natDegree≤5)
    (sites : 3≤(weightedSites (nodes A) θ).card)
    (paid : ∀ H : K[X], H.natDegree≤4 → ∀ i : Fin s, θ i≠0 →
      mat A (weightedEval (nodes A) θ H) i=(primitive (H*Q)).eval (nodes A i)) :
    Q=0 := by
  let c := nodes A
  let S := weightedSites c θ
  let I := Finset.univ.filter (fun i : Fin s=>θ i≠0 ∧ c i≠0)
  have ie : I.Nonempty := by
    have e : ∃ a∈S, a≠0 := by
      by_contra! no
      have sub : S⊆({0} : Finset K) := fun a z=>Finset.mem_singleton.mpr (no a z)
      have h := Finset.card_le_card sub
      rw [Finset.card_singleton] at h
      change 3≤S.card at sites
      omega
    obtain ⟨a,aMem,an⟩ := e
    obtain ⟨i,inZ,ic⟩ := mem_weightedSites.mp aMem
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inZ,ic.trans_ne an⟩⟩
  let i := I.min' ie
  have im : i∈I := Finset.min'_mem _ _
  obtain ⟨il,iu⟩ := (Finset.mem_filter.mp im).2
  let u := c i
  let J := Finset.univ.filter (fun j : Fin s => θ j≠0 ∧ c j≠0 ∧ c j≠u)
  have je : J.Nonempty := by
    have e : ∃ a∈S, a≠0 ∧ a≠u := by
      by_contra! no
      have sub : S⊆insert 0 ({u} : Finset K) := by
        intro a ae
        by_cases z : a=0
        · exact Finset.mem_insert.mpr (Or.inl z)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (no a ae z)))
      have h := Finset.card_le_card sub
      have o := Finset.card_insert_le 0 ({u} : Finset K)
      rw [Finset.card_singleton] at o
      change 3≤S.card at sites
      omega
    obtain ⟨a,aMem,an,au⟩ := e
    obtain ⟨j,jn,jc⟩ := mem_weightedSites.mp aMem
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,jn,jc.trans_ne an,jc.trans_ne au⟩⟩
  let j := J.min' je
  have jm : j∈J := Finset.min'_mem _ _
  obtain ⟨jl,jz,jd⟩ := (Finset.mem_filter.mp jm).2
  apply RKCert.ReviewedNative.Quintic.quintic_four_three Q q5 iu jz jd
  · intro k
    let H : K[X] := X^(k.val+1)
    have d : H.natDegree≤4 := by dsimp only [H]; rw [natDegree_X_pow]; have := k.isLt; omega
    have zero : mat A (weightedEval c θ H) i=0 := by
      apply causal_mat ha
      intro l li
      by_cases θz : θ l=0
      · simp [weightedEval_apply,θz]
      · have cz : c l=0 := by
          by_contra nn
          have lm : l∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,θz,nn⟩
          exact (not_le_of_gt li) (Finset.min'_le _ _ lm)

        simp [H,weightedEval_apply,cz]
    exact (paid H d i il).symm.trans zero
  · intro k
    rw [←mul_assoc]
    let H : K[X] := X^(k.val+1)*(X-C u)
    have d : H.natDegree≤4 := by
      apply natDegree_mul_le.trans
      rw [natDegree_X_pow,natDegree_X_sub_C]
      have := k.isLt
      omega
    have zero : mat A (weightedEval c θ H) j=0 := by
      apply causal_mat ha
      intro l lj
      by_cases θz : θ l=0
      · simp [weightedEval_apply,θz]
      · by_cases cz : c l=0
        · have pos : k.val+1≠0 := by omega
          simp [H,weightedEval_apply,cz]
        · have same : c l=u := by
            by_contra dd
            have lm : l∈J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,θz,cz,dd⟩
            exact (not_le_of_gt lj) (Finset.min'_le _ _ lm)
          simp [H,weightedEval_apply,same]
    exact (paid H d j jl).symm.trans zero

end
end RKResearch.Certified.Graded.LocalFivePorts

namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ h k θ : Fin 29→K} {P Q T : K[X]}

/-- The only saturation output the chronological gate needs. It does
not ask that the output weights be nonzero on all exposed rows or that
all stage clocks be distinct. -/
structure LocalFivePortCover (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (U : Submodule K (Fin 29→K)) (τ h θ k : Fin 29→K) (T : K[X]) : Prop where
  headDegree : T.natDegree≤5
  headLive : T≠0
  correction : k∈hiddenKernel b τ U
  exactContrast : θ=evalNodes A T-h-k
  enough : 3≤(weightedSites (nodes A) θ).card
  clean : ∀ i : Fin 29, θ i≠0 → ∀ z∈zeroSpace A 10,z i=0

set_option maxHeartbeats 600000 in
theorem width29_local_five_close_of_cover
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (F : LocalLinearBand A b 8 r U τ) (G : LocalFiveGeometry A b r U τ h P Q)
    (C : LocalFivePortCover A b U τ h θ k T) : False := by
  apply C.headLive
  apply LocalFivePorts.quintic_eq_zero_of_four_paid_tests ha C.headDegree C.enough
  intro H hd i hi
  have hH : evalNodes A H∈treeSpace A 4 := evalNodes_mem_treeSpace A H hd
  have hk : h*evalNodes A H∈zeroSpace A 9 :=
    zeroSpace_mul_treeSpace ho (n:=4) (by decide) G.staircase.headGrade hH
  have kinv := hiddenKernel_forward_clock F
  have lift : weightedEval (nodes A) k H∈hiddenKernel b τ U :=
    reflected_clock_weighted_core kinv C.correction H
  have E : k*evalNodes A H=weightedEval (nodes A) k H := by
    ext l
    simp [weightedEval_apply,mul_comm]
  have k6 : k*evalNodes A H∈zeroSpace A 6 := G.staircase.inside (E.symm ▸ lift)
  have za := C.clean i hi _ (mat_zeroSpace_charZero A 9 hk)
  have zb := C.clean i hi _ (zeroSpace_mono A (by decide : 7≤10)
    (mat_zeroSpace_charZero A 6 k6))
  have deg : (H*T).natDegree≤9 := natDegree_mul_le.trans (by have := C.headDegree; omega)
  have zc := C.clean i hi _ (primitive_defect A (H*T) (q:=9) deg)
  have e : weightedEval (nodes A) θ H=evalNodes A (H*T)-(h*evalNodes A H)-(k*evalNodes A H) := by
    rw [C.exactContrast]
    ext l
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.mul_apply,eval_mul]
    ring
  rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,za,zb,sub_zero,sub_zero]
  exact sub_eq_zero.mp zc

end
end RKResearch.Certified.ERK19
