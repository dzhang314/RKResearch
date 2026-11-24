module

public import RKCert.ReviewedNative.LocalLinearHiddenKernel

@[expose] public section

/-! Source-only draft of neutral support-unit and signed support tools. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {b τ f u : Fin s→K} {U : Submodule K (Fin s→K)}

theorem hiddenKernel_external_mul
    (mem : u∈hiddenKernel b τ U) (stable : U.map (diag f)≤U) :
    f*u∈hiddenKernel b τ U := by
  obtain ⟨ht,hb,hu⟩ := mem_hiddenKernel.mp mem
  apply mem_hiddenKernel.mpr
  refine ⟨by rw [show τ*(f*u)=f*(τ*u) by ac_rfl,ht,mul_zero],?_,?_⟩
  · have e : b*(f*u)=diag f (b*u) := by
      ext i
      simp only [Pi.mul_apply,diag_apply]
      ring
    rw [e]
    exact stable (Submodule.mem_map_of_mem hb)
  · rintro _ ⟨x,hx,rfl⟩
    have e : diag (f*u) x=diag f (diag u x) := by
      ext i
      simp only [Pi.mul_apply,diag_apply]
      ring
    rw [e]
    exact stable (Submodule.mem_map_of_mem (hu (Submodule.mem_map_of_mem hx)))

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- One support idempotent suffices; no class basis or signed quadrature is
used. Squares are of unconstrained coefficient vectors, never of output
weights in a positivity shortcut. -/
theorem hiddenKernel_support_unit (b τ : Fin s→K) (U : Submodule K (Fin s→K)) :
    ∃ e∈hiddenKernel b τ U, (∀ i,e i=0 ∨ e i=1) ∧
      ∀ v∈hiddenKernel b τ U,∀ i,e i=0 → v i=0 := by
  let J := hiddenKernel b τ U
  let live (i : Fin s) := ∃ v∈J,v i≠0
  have chooseRow (i : Fin s) : ∃ w∈J, live i → w i≠0 := by
    by_cases he : live i
    · obtain ⟨w,hm,hn⟩ := he
      exact ⟨w,hm,fun _=>hn⟩
    · exact ⟨0,J.zero_mem,fun c=>(he c).elim⟩
  choose w wJ any using chooseRow
  let v := ∑ j : Fin s, w j*w j
  have vJ : v∈J := J.sum_mem (fun j _=>hiddenKernel_mul (wJ j) (wJ j))
  have vpos (i : Fin s) (yes : live i) : 0<v i := by
    have h : 0<w i i*w i i := mul_self_pos.mpr (any i yes)
    have ge : w i i*w i i≤∑ j : Fin s,w j i*w j i :=
      Finset.single_le_sum (f:=fun j : Fin s=>w j i*w j i) (fun j _=>mul_self_nonneg (w j i)) (Finset.mem_univ i)
    have ev : v i=∑ j : Fin s,w j i*w j i := by simp only [v,Finset.sum_apply,Pi.mul_apply]
    rw [ev]
    exact h.trans_le ge
  let e (i : Fin s) := (v i)⁻¹*v i
  have diagV (z : Fin s→K) (hz : z∈J) : diag v z∈J := by
    have e : diag v z=v*z := by ext i; simp
    rw [e]
    exact hiddenKernel_mul vJ hz
  refine ⟨e,clock_function_mem diagV Inv.inv vJ,fun i=>?_,fun z hz i ez=>?_⟩
  · by_cases v0 : v i=0
    · exact Or.inl (by simp [e,v0])
    · exact Or.inr (inv_mul_cancel₀ v0)
  · by_contra zz
    exact zero_ne_one (ez.symm.trans (inv_mul_cancel₀ (vpos i ⟨z,hz,zz⟩).ne'))


omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Detect a too-small compensated contrast by the *actual* full reverse
annihilator, not by a positivity/Gram step or a p17 helper. In particular,
h=8 gives five physical reflected clocks; h=7 gives four. -/
theorem local_linear_contrast_site_floor
    {p h r : ℕ} {A : Matrix (Fin s) (Fin s) K} {W v : Fin s→K} {P Q : K[X]}
    (ho : HasOrder p A b) (F : LocalLinearBand A b h r U τ)
    (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (pay : 2*h+3≤p) (h4 : 4≤h)
    (live : Q≠0) (q5 : Q.natDegree≤5)
    (p5 : P=0 ∨ P.natDegree+r+1≤5) (vU : v∈U)
    (form : W=weightedEval (reflectedClock A) b Q-weightedEval (reflectedClock A) τ P-v) :
    h-3≤(RKCert.Endpoint.WeightedClock.weightedSites (reflectedClock A) W).card := by
  classical
  let y := reflectedClock A
  let S := RKCert.Endpoint.WeightedClock.weightedSites y W
  change h-3≤S.card
  by_contra! small
  let Z : K[X] := nodalHull S
  have dz : Z.natDegree=S.card := natDegree_nodalHull S
  have rb : r≤2 := by rcases F.coreRank with e|e <;> omega
  have wz : weightedEval y W Z=0 := by
    ext i
    by_cases e : W i=0
    · simp [weightedEval_apply,e]
    · have mem : y i∈S := RKCert.Endpoint.WeightedClock.mem_weightedSites.mpr ⟨i,e,rfl⟩
      simp [weightedEval_apply,Z,nodalHull_eval_of_mem mem]
  have fit : (Z*P).natDegree≤h-r := by
    rcases p5 with e|bd
    · simp [e]
    · exact natDegree_mul_le.trans (by omega)
  have tau := weighted_primitive_band F.headMem (Z*P) fit
  rw [show r+(h-r)=h by omega] at tau
  have mon : Monotone (primitiveBack A b) :=
    monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have inside : U≤primitiveBack A b h := F.core.le.trans (mon (by omega))
  have stable := inside (reflected_clock_weighted_core F.invariant vU Z)
  have e := scaled_contrast_decomposition (M:=Z) form
  change weightedEval y W Z=weightedEval y b (Z*Q)-weightedEval y τ (Z*P)-weightedEval y v Z at e
  rw [wz] at e
  have eq : weightedEval y b (Z*Q)=weightedEval y τ (Z*P)+weightedEval y v Z := by
    rw [sub_sub] at e
    exact sub_eq_zero.mp e.symm
  have paid : weightedEval y b (Z*Q)∈annih (treeSpace A (h+1)) := by
    rw [eq,←full]
    exact (primitiveBack A b h).add_mem tau stable
  have nz : Z≠0 := (monic_nodalHull S).ne_zero
  exact (mul_ne_zero nz live) (weighted_reflected_annihilation_zero ho (d:=h+1)
    (natDegree_mul_le.trans (by omega)) le_rfl (by omega) paid)

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
