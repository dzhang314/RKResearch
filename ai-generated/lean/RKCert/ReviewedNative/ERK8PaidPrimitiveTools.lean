module

public import RKCert.ReviewedNative.ERKTaggedHorizonSupport
public import RKCert.ReviewedNative.ERK8PaidNodalGain

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Bounded-denominator primitive and gain tools for the ERK8 census -/
namespace RKResearch.Certified.Graded.ERK8PaidField

open RKResearch Polynomial Module OneOff ERKTaggedHorizon RKCert.Endpoint
open scoped Matrix Classical

section Primitives
variable {K ι : Type*} [Field K] [Fintype ι] {A : Matrix ι ι K} {b : ι→K} {p : ℕ}

theorem primitive_defect_paid (ho : HasOrder p A b) (P : K[X]) {q : ℕ}
    (hp : P.natDegree≤q) (pay : q+1≤p) :
    mat A (evalNodes A P)-evalNodes A (primitive P)∈zeroSpace A (q+1) := by
  let D : K[X] →ₗ[K] (ι→K) := (mat A).comp (evalNodes A)-(evalNodes A).comp primitive
  have mono (n:ℕ) (hn:n≤q) (a:K) :
      D (monomial n a)∈zeroSpace A (q+1) := by
    have unit : ((n+1:ℕ):K)≠0 := (ho.natCast_isUnit (by omega) (by omega)).ne_zero
    have h : ((n+1:ℕ):K) • mat A (fun i=>(nodes A i)^n) -
      (fun i=>(nodes A i)^(n+1))∈zeroSpace A (n+1) := monomialStageDefect_mem A n
    have old := (zeroSpace A (n+1)).smul_mem (a/((n+1:ℕ):K)) h
    rw [smul_sub,smul_smul,div_mul_cancel₀ _ unit] at old
    apply zeroSpace_mono A (by omega : n+1≤q+1)
    change (mat A) (evalNodes A (monomial n a))-evalNodes A (primitive (monomial n a))∈_
    rw [primitive_monomial,evalNodes_monomial,evalNodes_monomial,map_smul,normTree_clockTree,normTree_clockTree]
    exact old
  change D P∈_
  rw [P.as_sum_range' (q+1) (by omega),map_sum]
  exact (zeroSpace A (q+1)).sum_mem (fun n hn=>mono n (by have :=Finset.mem_range.mp hn;omega) _)

end Primitives

section Forward
variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
  {b : Fin s → K}

theorem mDef_apply_paid (ho : HasOrder p A b) (j : ℕ) (pay : j+1≤p) (i : Fin s) :
    mDef A j i = mat A ((nodes A)^j) i - nodes A i^(j+1)/((j+1:ℕ):K) := by
  have hunit : ((j+1:ℕ):K) ≠ 0 := (ho.natCast_isUnit (by omega) pay).ne_zero
  change ((j+1:ℕ):K)⁻¹ *
    ((((j+1:ℕ):K) * mat A ((nodes A)^j) i) - nodes A i ^ (j+1)) = _
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hunit,one_mul,div_eq_mul_inv,mul_comm (_⁻¹)]

theorem g_apply_paid (ho : HasOrder p A b) (pay : 2≤p) (i : Fin s) :
    g A i = mat A (nodes A) i - nodes A i^2/2 := by
  simpa [g] using mDef_apply_paid ho 1 pay i

theorem zeroSpace_strict_paid (ha:∀i j,i≤j→A i j=0) (ho:HasOrder p A b)
    {q j:ℕ} (sep:∀a,coeffEval A q a∈zeroSpace A q→a=0) (jpos:1≤j) (jq:j+1≤q)
    (pay : j+1≤p) : zeroSpace A j<zeroSpace A (j+1) := by
  refine lt_of_le_of_ne (zeroSpace_mono A (Nat.le_succ _)) ?_
  intro he
  apply nodes_not_defect_of_separation (by omega) sep
  apply zeroSpace_mono A jq
  rw [←he,←show diag (nodes A) (1:Fin s→K)=nodes A by ext i;simp]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 (zeroSpace A j)
  · intro v hv
    rw [he]
    exact mat_zeroSpace ho j pay hv
  · intro v hv
    rw [he]
    exact diag_zeroSpace A j hv
  · rw [he]
    exact zeroSpace_mono A (by omega : 2≤j+1) (forward_seed_mem A)

private theorem strict_nodal_mat (ha : ∀ i k, i ≤ k → A i k=0) :
    StrictlyCausal (mat A) := by
  intro i x y pre
  have z := causal_mat ha i (x-y) (fun k hk => sub_eq_zero.mpr (pre k hk))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using z

private theorem hermite_eval (A : Matrix (Fin s) (Fin s) K) (P : K[X]) :
    weightedEval (nodes A) 1 P = evalNodes A P := by
  ext i
  simp

theorem clock_invariant_outgoing_paid (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder p A b) {j : ℕ} (pay : j+1≤p)
    (sep : PolySeparated A j) {U : Submodule K (Fin s → K)}
    (sub : U ≤ zeroSpace A j) (stable : U.map (diag (nodes A)) ≤ U) :
    finrank K U + (j+1)/2 ≤ finrank K (zeroSpace A (j+1)) := by
  have hm := clock_mask_invariant (fun _ hv => stable (Submodule.mem_map_of_mem hv))
  apply outgoing_nodal_gain_paid (nodes A) 1 U (zeroSpace A (j+1)) (mat A) (strict_nodal_mat ha)
    hm (sub.trans (zeroSpace_mono A (Nat.le_succ j)))
    (fun _ h => mat_zeroSpace ho j pay (sub h)) _
    (fun n pos le => (ho.natCast_isUnit (n:=n) pos (by omega)).ne_zero)
  · exact (show (j+1)/2≤j by omega).trans (failed_nodes_of_separation sep sub hm)
  · intro P hP
    rw [hermite_eval,hermite_eval]
    exact primitive_defect_paid ho P (by omega) pay

theorem clock_invariant_incoming_paid (ha : ∀ i k, i ≤ k → A i k=0)
    (ho : HasOrder p A b) {j : ℕ} (pay : j+1≤p) (sep : PolySeparated A (j+1))
    (stable : (zeroSpace A (j+1)).map (diag (nodes A)) ≤ zeroSpace A (j+1)) :
    finrank K (zeroSpace A j) + (j+1)/2 ≤ finrank K (zeroSpace A (j+1)) := by
  have hm := clock_mask_invariant (fun _ hv => stable (Submodule.mem_map_of_mem hv))
  apply incoming_nodal_gain_paid (nodes A) 1 (zeroSpace A j) (zeroSpace A (j+1)) (mat A)
    (strict_nodal_mat ha) hm (zeroSpace_mono A (Nat.le_succ j))
    (fun _ h=>mat_zeroSpace ho j pay h) _
    (fun n pos le => (ho.natCast_isUnit (n:=n) pos (by omega)).ne_zero)
  · exact (show (j+1)/2≤j+1 by omega).trans (failed_nodes_of_separation sep le_rfl hm)
  · intro P hP
    rw [hermite_eval,hermite_eval]
    exact primitive_defect_paid ho P (by omega) pay

theorem not_two_or_three_paid (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (sep : PolySeparated A 4) (r3 : finrank K (zeroSpace A 3)=2)
    (r4 : finrank K (zeroSpace A 4)=3) :
    (offKnots A).card≠2 ∧ (offKnots A).card≠3 := by
  constructor
  · intro h
    have r := band_rank (A:=A) (q:=1) (by omega)
    have eqn : band A 1=zeroSpace A 3 := Submodule.eq_of_le_of_finrank_le
      (band_le A 1) (by omega)
    have stab := band_stable (A:=A) (q:=1) (by omega)
    rw [eqn] at stab
    have cost := clock_invariant_outgoing_paid ha ho (by decide : 3+1≤8)
      (sep.mono (by decide : 3≤4)) le_rfl stab
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at cost
    omega
  · intro h
    have r := band_rank (A:=A) (q:=2) (by omega)
    have eqn : band A 2=zeroSpace A 4 := Submodule.eq_of_le_of_finrank_le
      (band_le A 2) (by omega)
    have stab := band_stable (A:=A) (q:=2) (by omega)
    rw [eqn] at stab
    have cost := clock_invariant_incoming_paid ha ho (by decide : 3+1≤8) sep stab
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at cost
    omega

theorem off_pos_paid (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (sep : PolySeparated A 4) : 0 < (offKnots A).card := by
  by_contra! no
  have gz : g A=0 := by
    funext i
    by_contra h
    have pos := Finset.card_pos.mpr ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩
    omega
  have seed : (2:K) • mat A (diag (nodes A) (1:Fin s→K)) -
    diag (nodes A) (diag (nodes A) 1) = (2:K) • g A := by
    have he : diag (nodes A) (1:Fin s→K)=nodes A := by ext i; simp
    rw [he]
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]
    rw [g_apply_paid ho (by decide)]
    have h : (nodes A i)^2 / 2 * 2 = (nodes A i)^2 :=
      div_mul_cancel₀ _ (ho.natCast_isUnit (n:=2) (by decide) (by decide)).ne_zero
    linear_combination h
  apply sep.nodes_not_mem (by decide)
  rw [←show diag (nodes A) (1:Fin s→K)=nodes A by ext i;simp]
  apply (show (⊥ : Submodule K (Fin s → K)) ≤ zeroSpace A 4 from bot_le)
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 _
  · intro v hv
    rw [(Submodule.mem_bot K).mp hv,map_zero]
    exact Submodule.zero_mem _
  · intro v hv
    rw [(Submodule.mem_bot K).mp hv,map_zero]
    exact Submodule.zero_mem _
  · rw [seed,gz,smul_zero]
    exact Submodule.zero_mem _

theorem on_primitive_zero_paid (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2) {i : Fin s} (hi : g A i=0)
    (Q : K[X]) (hq : Q.natDegree≤3) (v : Fin s→K) (hv : mat A v i=0)
    (hpre : ∀ j, j < i → Q.eval (nodes A j)=v j) : (primitive Q).eval (nodes A i)=0 := by
  have rem := clean_four_vanish hF hi (primitive_defect_paid ho Q hq (by decide))
  have eq := causal_action_eq ha i (evalNodes A Q) v hpre
  change mat A (evalNodes A Q) i - (primitive Q).eval (nodes A i)=0 at rem
  rw [eq,hv,zero_sub,neg_eq_zero] at rem
  exact rem

theorem clean_mixed_defect_paid (ho : HasOrder 8 A b) (hF : zeroSpace A 4=band A 2)
    {i : Fin s} (hi : g A i=0) :
    mat A (diag (nodes A) (g A)) i=0 :=
  clean_four_vanish hF hi (mat_zeroSpace ho 3 (by decide) (diag_zeroSpace A 2 (mDef_mem A 1)))

end Forward
end RKResearch.Certified.Graded.ERK8PaidField
