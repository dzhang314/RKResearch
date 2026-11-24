module

public import RKCert.ReviewedNative.LocalLinearBand
public import RKCert.ReviewedNative.NativeHeadMultiplier
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! # Paid physical mixed traces in a local first-seed band

The initial localized invariant subspace is not assumed to be
coordinatewise closed. Its invariance under a low-grade feature is
earned using the actual full midpoint annihilator. No adjoint RK
tableau or unverified coupled flag is introduced. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

private theorem reflected_poly_degree (k : ℕ) : ((1-X : K[X])^k).natDegree≤k := by
  have d : (1-X : K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  simpa only [Nat.mul_one] using natDegree_pow_le_of_le k d

theorem primitive_shifted_column_annih (ho : HasOrder p A b)
    {n j g k : ℕ} (pay : n+j+g+k+2≤p)
    {v f : Fin s→K} (hv : v∈primitiveBack A b n) (hf : f∈treeSpace A j) :
    (diag (reflectedClock A)^k) (v*f)∈annih (treeSpace A g) := by
  apply mem_annih.mpr
  intro w hw
  let R := (1-X : K[X])^k
  have step := treeSpace_mul (treeSpace_mul hf (evalNodes_mem_treeSpace A R (reflected_poly_degree k))) hw
  have z := mem_annih.mp (primitiveBack_annih ho _ _ (by omega) hv) _ step
  rw [row_apply,dotProduct] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [HeadFiber.clock_power_value,Pi.mul_apply,evalNodes_apply,R,eval_pow,
    eval_sub,eval_one,eval_X,reflectedClock,Pi.sub_apply,Pi.one_apply]
  ring

theorem output_shifted_defect_annih (ho : HasOrder p A b)
    {j g k : ℕ} (pay : j+g+k+1≤p)
    {f : Fin s→K} (hf : f∈zeroSpace A j) :
    (diag (reflectedClock A)^k) (b*f)∈annih (treeSpace A g) := by
  apply mem_annih.mpr
  intro w hw
  let R := (1-X : K[X])^k
  have step := zeroSpace_mul_treeSpace ho (by omega) hf
    (treeSpace_mul (evalNodes_mem_treeSpace A R (reflected_poly_degree k)) hw)
  have z : probe A b 0 _=0 := probe_zeroSpace ho (by omega) step
  simp only [probe,row_apply,dotProduct,pow_zero,mul_one] at z
  rw [row_apply,dotProduct]
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [HeadFiber.clock_power_value,Pi.mul_apply,evalNodes_apply,R,eval_pow,
    eval_sub,eval_one,eval_X,reflectedClock,Pi.sub_apply,Pi.one_apply]
  ring

private theorem clock_pow_core {c : Fin s→K} {U : Submodule K (Fin s→K)}
    (inv : U.map (diag c)≤U) {u : Fin s→K} (hu : u∈U) (k : ℕ) :
    (diag c^k) u∈U := by
  have e := clock_function_mem (fun v (hv : v∈U)=>inv (Submodule.mem_map_of_mem hv))
    (fun a=>a^k) hu
  have eq : (diag c^k) u=(fun i=>c i^k*u i) := by ext i; simp
  rw [eq]
  exact e

theorem local_core_preserved_by_defect (ho : HasOrder p A b)
    {h r j : ℕ} {U : Submodule K (Fin s→K)} {τ f : Fin s→K}
    (F : LocalLinearBand A b h r U τ)
    (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (pay : 2*h+3≤p) (limit : j+r≤h) (hf : f∈zeroSpace A j) :
    U.map (diag f)≤U := by
  let c := reflectedClock A
  let S := Finset.univ.image c
  rintro _ ⟨v,hv,rfl⟩
  have mask := clock_mask_invariant (fun _ hv=>F.invariant (Submodule.mem_map_of_mem hv))
  have blocks (z : K) : diag f (blockMask c z v)∈U := by
    have src : blockMask c z v∈primitiveBack A b (r-1) := F.core.le (mask _ _ hv)
    have test := primitive_shifted_column_annih ho (n:=r-1) (j:=j) (g:=h+1)
      (k:=0) (by omega) src (zeroSpace_le_treeSpace A j hf)
    rw [←full] at test
    have e : (diag c^0) (blockMask c z v*f)=diag f (blockMask c z v) := by
      simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
      ext i; simp [mul_comm]
    change (diag c^0) (blockMask c z v*f)∈primitiveBack A b h at test
    rw [e] at test
    apply F.local_mem_core (by omega) test (y:=z)
    intro i other
    have z : c i≠z := other
    simp [blockMask,z]
  have sum : (∑ z∈S,blockMask c z v)=v := by
    ext i
    rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (c i) (Finset.mem_image_of_mem c (Finset.mem_univ i))]
    · simp [blockMask]
    · intro j _ hj; simp [blockMask,Ne.symm hj]
  rw [←sum,map_sum]
  exact U.sum_mem (fun z _=>blocks z)

private theorem trace_after_shifts {c τ : Fin s→K} {U : Submodule K (Fin s→K)}
    {v : Fin s→K} {n ℓ : ℕ} (stable : U.map (diag c)≤U)
    (many : n<(HeadFiber.escapeSites c τ U).card)
    (shifts : ∀ k≤ℓ,(diag c^k) v∈chain (diag c) U τ n) :
    ∃ u∈U, ∃ P : K[X], v=u+weightedEval c τ P ∧ (P=0 ∨ P.natDegree+ℓ<n) := by
  have base : v∈chain (diag c) U τ n := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using shifts 0 (Nat.zero_le _)
  obtain ⟨u,hu,P,pd,eq⟩ := HeadFiber.exists_poly base
  refine ⟨u,hu,P,eq,?_⟩
  by_cases pn : P=0
  · exact Or.inl pn
  right
  have shiftRep (k : ℕ) :
      (diag c^k) v=(diag c^k) u+weightedEval c τ (X^k*P) := by
    rw [eq,map_add]
    congr 1
    ext i
    simp only [HeadFiber.clock_power_value,weightedEval_apply,eval_mul,eval_pow,eval_X]
    ring
  have deg (k : ℕ) : (X^k*P).natDegree=k+P.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) pn,natDegree_X_pow]
  have powNZ (k : ℕ) : X^k*P≠0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) pn
  have grow (k : ℕ) (pay : k≤ℓ) : (X^k*P).degree < (n:WithBot ℕ) := by
    induction k with
    | zero => simpa using pd
    | succ k ih =>
      obtain ⟨u',hU,Q,qd,e⟩ := HeadFiber.exists_poly (shifts (k+1) pay)
      have ex := (shiftRep (k+1)).symm.trans e
      have dif : weightedEval c τ (X^(k+1)*P-Q)∈U := by
        rw [map_sub]
        have a : weightedEval c τ (X^(k+1)*P)-weightedEval c τ Q =
          u'-(diag c^(k+1)) u := by
          calc
            _ = ((diag c^(k+1)) u+weightedEval c τ (X^(k+1)*P))-
                (diag c^(k+1)) u-weightedEval c τ Q := by abel
            _ = _ := by rw [ex]; abel
        rw [a]
        exact U.sub_mem hU (clock_pow_core stable hu _)
      have bound := (natDegree_lt_iff_degree_lt (powNZ k)).mpr (ih (by omega))
      have next : (X^(k+1)*P).degree ≤ (n:WithBot ℕ) := by
        refine degree_le_natDegree.trans ?_
        have hs : (X^(k+1)*P).natDegree≤n := by rw [deg] at bound ⊢; omega
        exact_mod_cast hs
      have many' : (n:WithBot ℕ)<((HeadFiber.escapeSites c τ U).card:WithBot ℕ) := by exact_mod_cast many
      have bd := (degree_sub_le (X^(k+1)*P) Q).trans_lt (max_lt (next.trans_lt many') (qd.trans many'))
      have same := sub_eq_zero.mp (HeadFiber.faithful_on_escape_sites stable bd dif)
      rwa [same]
  have nlt := (natDegree_lt_iff_degree_lt (powNZ ℓ)).mpr (grow ℓ le_rfl)
  rw [deg] at nlt
  omega

variable [LinearOrder K] [IsStrictOrderedRing K]

structure LocalLinearTraces (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K)
    (U : Submodule K (Fin s→K)) (τ f : Fin s→K) (r j : ℕ) (P Q : K[X]) : Prop where
  preserves : U.map (diag f)≤U
  qDeg : Q.natDegree≤j
  pDeg : P=0 ∨ P.natDegree+r+1≤j
  tauTrace : τ*f=weightedEval (reflectedClock A) τ Q
  weightTrace : b*f-weightedEval (reflectedClock A) τ P∈U

set_option maxHeartbeats 1000000 in
theorem local_linear_two_traces (ho : HasOrder p A b)
    {h r j : ℕ} {U : Submodule K (Fin s→K)} {τ f : Fin s→K}
    (F : LocalLinearBand A b h r U τ)
    (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (pay : 2*h+3≤p) (budget : j+r≤h) (hf : f∈zeroSpace A j) :
    ∃ P Q, LocalLinearTraces A b U τ f r j P Q := by
  let Y := diag (reflectedClock A)
  let c := reflectedClock A
  have stable := local_core_preserved_by_defect ho F full pay budget hf
  have rune := F.band h (by omega) le_rfl
  have qsh (k : ℕ) (hk : k≤h-r-j) :
      (Y^k) (τ*f)∈chain Y U τ (h+1-r) := by
    rw [←rune,full]
    exact primitive_shifted_column_annih ho (n:=r) (j:=j) (g:=h+1) (k:=k)
      (by omega) F.headMem (zeroSpace_le_treeSpace _ _ hf)
  have psh (k : ℕ) (hk : k≤h+1-j) :
      (Y^k) (b*f)∈chain Y U τ (h+1-r) := by
    rw [←rune,full]
    exact output_shifted_defect_annih ho (j:=j) (g:=h+1) (k:=k) (by omega) hf
  obtain ⟨u,hu,Q,e,Qcap⟩ := trace_after_shifts F.invariant F.escapes qsh
  obtain ⟨u',hu',P,e',Pcap⟩ := trace_after_shifts F.invariant F.escapes psh
  have annf : τ*f∈annih U := by
    apply mem_annih.mpr
    intro w hw
    have z := mem_annih.mp F.headOrthogonal _
      (stable (Submodule.mem_map_of_mem hw : diag f w∈U.map (diag f)))
    simpa only [row_apply,dotProduct,Pi.mul_apply,diag_apply,mul_assoc] using z
  have annQ : weightedEval c τ Q∈annih U := by
    apply mem_annih.mpr
    intro w hw
    have hw' := clock_function_mem (fun v (hv : v∈U)=>F.invariant (Submodule.mem_map_of_mem hv))
      (fun x => Q.eval x) hw
    have z := mem_annih.mp F.headOrthogonal _ hw'
    rw [row_apply,dotProduct] at z ⊢
    convert z using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [weightedEval_apply]
    ring
  have za : u∈annih U := by
    have difference := (annih U).sub_mem annf annQ
    rw [e,add_sub_cancel_right] at difference
    exact difference
  have uz := eq_zero_of_self_row_zero (mem_annih.mp za u hu)
  refine ⟨P,Q,⟨stable,?_,?_,?_,?_⟩⟩
  · rcases Qcap with z|y
    · simp [z]
    · omega
  · rcases Pcap with z|y
    · exact Or.inl z
    · exact Or.inr (by omega)
  · simpa only [uz,zero_add] using e
  · rw [e',add_sub_cancel_right]
    exact hu'

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
