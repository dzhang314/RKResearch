module

public import RKCert.ReviewedNative.ERK17LocalFourAxes
public import RKCert.ReviewedNative.LocalLinearCompensatedContrast

@[expose] public section

/-! # Genuine off-axis compensated contrast for the rank-four census

An orthogonal compensated contrast loses no support when zeroing the
exceptional grade-six axis: its off-zero axis part already vanishes.
This is a native precondition for the refined (y,h,ξ,e) census. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ h ξ e W : Fin 26→K}
variable {U : Submodule K (Fin 26→K)} {P Q : K[X]}

set_option maxRecDepth 3500
set_option maxHeartbeats 1000000

/-- The output trace of ξ, not just preservation of U, makes every
orthogonally compensated contrast row vanish where ξ is nonzero. -/
theorem local_four_contrast_off_axis (F : LocalLinearBand A b 7 2 U τ)
    (D : LocalFourAxes A b τ h ξ U) (T : LocalLinearTraces A b U τ h 2 5 P Q)
    (eK : e∈hiddenKernel b τ U) (WU : W∈annih U)
    (on : ∀ i,W i≠0 → e i=0 ∧ h i=0 ∧ Q.eval (reflectedClock A i)≠0)
    {u : Fin 26→K} (hu : u∈U)
    (form : W=weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) τ P-u) :
    ∀ i,W i≠0 → ξ i=0 := by
  let y := reflectedClock A
  let ch (x : K) : K := if x=0 then 1 else 0
  let near (x : K) : K := if Q.eval x=0 then 0 else 1
  let mult (x : K) : K := if Q.eval x=0 then 0 else Q.eval x
  let sel (x : K) : K := if x=0 then 0 else 1
  let divx (x : K) : K := if x=0 then 0 else x⁻¹
  let Z : Fin 26→K := fun i=>sel (ξ i)*W i
  have invE : U.map (diag e)≤U := (mem_hiddenKernel.mp eK).2.2
  have axis (v : Fin 26→K) (hv : v∈U) (g : K→K) : (fun i=>g (ξ i)*v i)∈U :=
    clock_function_mem (fun _ hx=>D.axisPreserves (Submodule.mem_map_of_mem hx)) g hv
  obtain ⟨v,hv,R,_,refund⟩ := D.weightRefund
  let a := selectThree y h e mult ch ch (fun i=>divx (ξ i)*v i)
  let c := selectThree y h e near ch ch (fun i=>sel (ξ i)*u i)
  have aU : a∈U := selectThree_mem F.invariant T.preserves invE mult ch ch (axis v hv divx)
  have cU : c∈U := selectThree_mem F.invariant T.preserves invE near ch ch (axis u hu sel)
  have eq : Z=a-c := by
    ext i
    by_cases xx : ξ i=0
    · simp [Z,a,c,selectThree,sel,divx,xx]
    by_cases ee : e i=0
    · by_cases hh : h i=0
      · by_cases qq : Q.eval (y i)=0
        · have wi : W i=0 := by
            by_contra nz
            exact (on i nz).2.2 qq
          simp [Z,a,c,selectThree,sel,divx,near,mult,ch,xx,ee,hh,qq,wi]
        · have tau : τ i=0 := by
            have trace := congrFun T.tauTrace i
            rw [Pi.mul_apply,hh,mul_zero,weightedEval_apply] at trace
            exact (mul_eq_zero.mp trace.symm).resolve_left qq
          have wo := congrFun form i
          simp only [Pi.sub_apply,weightedEval_apply,tau,mul_zero,sub_zero] at wo
          have ve := congrFun refund i
          simp only [Pi.mul_apply,Pi.add_apply,weightedEval_apply,tau,mul_zero,add_zero] at ve
          change b i*ξ i=v i at ve
          change W i=Q.eval (y i)*b i-u i at wo
          simp only [Z,a,c,selectThree,sel,divx,near,mult,ch,xx,ee,hh,qq,ite_false,ite_true,
            Pi.sub_apply,one_mul,mul_one,wo,←ve]
          field_simp [xx]
          <;> ring
      · have wi : W i=0 := by
          by_contra nz
          exact hh (on i nz).2.1
        simp [Z,a,c,selectThree,sel,divx,near,mult,ch,xx,ee,hh,wi]
    · have wi : W i=0 := by
        by_contra nz
        exact ee (on i nz).1
      simp [Z,a,c,selectThree,sel,divx,near,mult,ch,xx,ee,wi]
  have ZU : Z∈U := eq.symm ▸ U.sub_mem aU cU
  have Zo : Z∈annih U := by
    have h := selectThree_annih D.axisPreserves D.axisPreserves D.axisPreserves sel
      (fun _=>1) (fun _=>1) WU
    have same : selectThree ξ ξ ξ sel (fun _ => 1) (fun _ => 1) W = Z := by
      ext i
      simp only [selectThree,Z,mul_one]
    exact same ▸ h
  have zero : Z=0 := eq_zero_of_self_row_zero (mem_annih.mp Zo _ ZU)
  intro i wi
  by_contra nz
  exact wi (by simpa only [Z,sel,nz,ite_false,one_mul,Pi.zero_apply] using congrFun zero i)

/-- Concrete inputs earned before the 16-joint-head-block count. The
kernel/τ/contrast have their true vector values; an unoccupied supplied
label is not treated as a stage. -/
structure LocalFourCensusInputs (A : Matrix (Fin 26) (Fin 26) K)
    (b τ h ξ e W : Fin 26→K) (U : Submodule K (Fin 26→K)) (P Q : K[X]) : Prop where
  trace : LocalLinearTraces A b U τ h 2 5 P Q
  live : Q≠0
  unit : e∈hiddenKernel b τ U
  binary : ∀ i,e i=0∨e i=1
  kernelOff : ∀ v∈hiddenKernel b τ U,∀ i,e i=0 → v i=0
  coreRank : finrank K U=2
  kernelOrthogonal : hiddenKernel b τ U≤annih U
  coreMass : ∀ v∈U,(∑ i,v i)=0
  tauRows : ∀ i,τ i≠0 → e i=0 ∧ h i=Q.eval (reflectedClock A i)
  contrastOrthogonal : W∈annih U
  compensated : ∃ u∈U,W=weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) τ P-u
  contrastRows : ∀ i,W i≠0 → e i=0 ∧ h i=0 ∧ ξ i=0 ∧ Q.eval (reflectedClock A i)≠0
  contrastCount : 4≤(weightedSites (reflectedClock A) W).card
  cleanRows : ∀ i,W i≠0 → ∀ v∈zeroSpace A 9,v i=0

theorem width26_local_four_census_inputs
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7=annih (treeSpace A 8))
    (D : LocalFourAxes A b τ h ξ U) :
    ∃ P Q : K[X], ∃ e W, LocalFourCensusInputs A b τ h ξ e W U P Q := by
  obtain ⟨P,Q,T⟩ := local_linear_two_traces ho F full (by decide) (by decide) D.fifth
  have live : Q≠0 := fun z=>D.headOut (LocalLinearTraces.mem_hidden_of_q_zero F T z)
  obtain ⟨e,eK,bin,eo⟩ := hiddenKernel_support_unit b τ U
  obtain ⟨W,WU,on,u,hu,form⟩ := local_linear_compensated_contrast F T eK bin
  have offAxis := local_four_contrast_off_axis F D T eK WU on hu form
  have sit := local_linear_contrast_site_floor ho F full (by decide) (by decide)
    live T.qDeg T.pDeg hu form
  have S := (ordered_width26_full_frame ha ho).1
  have rU : finrank K U=2 := by
    have ue : U=primitiveBack A b 1 := F.core
    obtain ⟨rk,eq⟩ := S.reverse.flagExact 1 (by decide)
    rw [ue,←eq,rk,first_dim_one nz]
  have ua : U≤annih (treeSpace A 8) := (F.core.le.trans
    ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by decide : 2-1≤7))).trans full.le
  have orth : hiddenKernel b τ U≤annih U := by
    intro v hv
    have vt := hiddenKernel_le_paid_tree F (by decide) full hv
    apply mem_annih.mpr
    intro w hw
    have e := mem_annih.mp (ua hw) _ vt
    rw [row_apply,dotProduct_comm,←row_apply] at e
    exact e
  have mass (v : Fin 26→K) (hv : v∈U) : (∑ i,v i)=0 := by
    have one : (1 : Fin 26→K)∈treeSpace A 8 := by
      have e : evalNodes A (1 : K[X])=(1 : Fin 26→K) := by ext i; simp
      rw [←e]
      exact evalNodes_mem_treeSpace A _ (by simp)
    have p := mem_annih.mp (ua hv) 1 one
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using p
  have rows (i : Fin 26) (li : τ i≠0) : e i=0 ∧ h i=Q.eval (reflectedClock A i) := by
    have e0 := congrFun (mem_hiddenKernel.mp eK).1 i
    have tr := congrFun T.tauTrace i
    simp only [Pi.mul_apply,Pi.zero_apply,weightedEval_apply] at e0 tr
    exact ⟨(mul_eq_zero.mp e0).resolve_left li,
      mul_right_cancel₀ li (by simpa only [mul_comm (h i) (τ i)] using tr)⟩
  refine ⟨P,Q,e,W,⟨T,live,eK,bin,eo,rU,orth,mass,rows,WU,⟨u,hu,form⟩,?_,?_,?_⟩⟩
  · intro i wi
    obtain ⟨ei,hi,qi⟩ := on i wi
    exact ⟨ei,hi,offAxis i wi,qi⟩
  · exact sit
  · intro i wi v hv
    exact D.cleared i (fun w hw=>eo w hw i (on i wi).1) (on i wi).2.1 (offAxis i wi) v hv

end
end RKResearch.Certified.ERK17
