module

public import RKCert.ReviewedNative.ERK19LocalFivePorts
public import RKCert.ReviewedNative.LocalLinearSupportTools

@[expose] public section
/-! Draft adapter only: the physical census must produce the exact
`LocalFiveCoverPremises`; no rank-five exclusion is claimed without this. -/

namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ h e W : Fin 29→K} {P Q : K[X]}

/-- Exact remaining saturation contract, phrased only in the observable
geometry needed by the gate. The full physical joint-block cover implies
`reflectedCover`, not conversely. No independence of individual rows at
a repeated c/Y is asserted. -/
structure LocalFiveCoverPremises (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (U : Submodule K (Fin 29→K)) (τ h e W : Fin 29→K) (Q : K[X]) : Prop where
  coreMask : e∈hiddenKernel b τ U
  idempotentValues : ∀ i,e i=0 ∨ e i=1
  offCore : ∀ v∈hiddenKernel b τ U,∀ i,e i=0 → v i=0
  reflectedCover : ∀ i,e i=0 → h i=Q.eval (reflectedClock A i) ∨ h i=0
  contrastRows : ∀ i,W i≠0 → e i=0 ∧ h i=0 ∧ Q.eval (reflectedClock A i)≠0
  contrastSites : 5≤(weightedSites (reflectedClock A) W).card

set_option maxHeartbeats 750000 in
omit [IsStrictOrderedRing K] in
theorem width29_local_five_port_cover_of_saturation
    (F : LocalLinearBand A b 8 r U τ) (G : LocalFiveGeometry A b r U τ h P Q)
    (C : LocalFiveCoverPremises A b U τ h e W Q) :
    ∃ k θ T, LocalFivePortCover A b U τ h θ k T := by
  let c := nodes A
  let y := reflectedClock A
  let J := hiddenKernel b τ U
  let R : K[X] := 1-X
  let T := Q.comp R
  have dd : R.natDegree=1 := by
    dsimp only [R]
    rw [natDegree_sub_eq_right_of_natDegree_lt (p:=1) (q:=X) (by simp),natDegree_X]
  have dT : T.natDegree≤5 := natDegree_comp_le.trans
    ((Nat.mul_le_mul G.fit.qDeg dd.le).trans_eq (Nat.mul_one 5))
  have reflectTwice : R.comp R=X := by
    dsimp only [R]
    simp only [sub_comp,one_comp,X_comp]
    ring
  have tLive : T≠0 := by
    intro z
    have qz : T.comp R=Q := by
      dsimp only [T]
      rw [comp_assoc,reflectTwice,comp_X]
    rw [z,zero_comp] at qz
    exact G.nonzeroHead qz.symm
  have trueT (i : Fin 29) : T.eval (c i)=Q.eval (y i) := by
    simp only [T,eval_comp,R,eval_sub,eval_one,eval_X,y,
      reflectedClock,Pi.sub_apply,Pi.one_apply,c]
  let k := weightedEval c e T-h*e
  have kJ : k∈J := J.sub_mem
    (reflected_clock_weighted_core (hiddenKernel_forward_clock F) C.coreMask T)
    (hiddenKernel_external_mul C.coreMask G.fit.preserves)
  let θ := evalNodes A T-h-k
  have θval (i : Fin 29) : θ i=(1-e i)*(T.eval (c i)-h i) := by
    simp only [θ,k,weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.mul_apply,c]
    ring
  have clean (i : Fin 29) (hi : θ i≠0) : e i=0 ∧ h i=0 := by
    have ei : e i=0 := by
      rcases C.idempotentValues i with z|one
      · exact z
      · exfalso
        apply hi
        rw [θval,one,sub_self,zero_mul]
    refine ⟨ei,?_⟩
    rcases C.reflectedCover i ei with same|hz
    · exfalso
      apply hi
      rw [θval,trueT i,same,sub_self,mul_zero]
    · exact hz
  let Tθ := weightedSites c θ
  have enough : 3≤Tθ.card := by
    have image : weightedSites y W⊆Tθ.image (fun a : K=>1-a) := by
      intro a ah
      obtain ⟨i,wi,ea⟩ := mem_weightedSites.mp ah
      obtain ⟨ze,zh,qt⟩ := C.contrastRows i wi
      have non : θ i≠0 := by
        rw [θval,ze,zh,trueT i,sub_zero,sub_zero,one_mul]
        exact qt
      exact Finset.mem_image.mpr
        ⟨c i,mem_weightedSites.mpr ⟨i,non,rfl⟩,ea⟩
    have x := (C.contrastSites.trans (Finset.card_le_card image)).trans Finset.card_image_le
    omega
  refine ⟨k,θ,T,⟨dT,tLive,kJ,rfl,enough,fun i hi z hz=>?_⟩⟩
  obtain ⟨ei,headOff⟩ := clean i hi
  rw [G.tenth] at hz
  obtain ⟨u,hu,S,_,eq⟩ := HeadFiber.exists_poly hz
  have zu := C.offCore u hu i ei
  simp only [congrFun eq i,Pi.add_apply,weightedEval_apply,zu,headOff,mul_zero,add_zero]

/-- All remaining mathematical work sits in the saturation producer. -/
theorem width29_local_five_impossible_of_saturation
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (F : LocalLinearBand A b 8 r U τ) (G : LocalFiveGeometry A b r U τ h P Q)
    (C : LocalFiveCoverPremises A b U τ h e W Q) : False := by
  obtain ⟨k,θ,T,cov⟩ := width29_local_five_port_cover_of_saturation F G C
  exact width29_local_five_close_of_cover ha ho F G cov

end
end RKResearch.Certified.ERK19
