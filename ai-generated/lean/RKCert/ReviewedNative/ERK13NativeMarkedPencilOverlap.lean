module

public import RKCert.ReviewedNative.ERK13NativeMarkedQuadraticCore
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Literal degree-seven cubic overlap without joint support normalization

The argument eliminates the same v directly in original stage coordinates.
Its product with the terminal mark vanishes exactly, and each of the three
ordinary error columns lies in U by v- or clock-invariance. No closure of
U under arbitrary internal products and no head surgery are used. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w v : Fin 19 → K} {r : ℕ} {G P : K[X]}

private theorem head_power_unpaid_predecessor
    (stable : U.map (diag (nodes A))≤U) {n : ℕ} (pos : 0<n)
    (unpaid : ((diag (nodes A))^(n+1)) w ∉ escapeHeadBand A U w (n+1)) :
    ((diag (nodes A))^n) w ∉ escapeHeadBand A U w n := by
  intro h
  apply unpaid
  rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
  exact escapeHeadBand_map_succ stable pos (Submodule.mem_map_of_mem h)

/-- The two real shifts v,Cv,C²v in F5 peel two genuine head powers.
A nonzero v modulo U is represented there by a nonzero polynomial T. -/
theorem NativePaidHead.grade_three_short_head_rep
    (H : NativePaidHead A b r U w) (room : 3≤r)
    (hv : v∈zeroSpace A 3) (off : v∉U) :
    ∃ u∈U, ∃ T : K[X], T≠0 ∧ T.natDegree+3≤r ∧
      v=u+weightedEval (nodes A) w T := by
  obtain ⟨m,rm⟩ : ∃ m : ℕ, r=m+3 := ⟨r-3,by omega⟩
  subst r
  let D := diag (nodes A)
  have f5 : zeroSpace A 5=escapeHeadBand A U w (m+3) := H.head.flags 0 (by decide)
  have f6 : zeroSpace A 6=escapeHeadBand A U w (m+4) := H.head.flags 1 (by decide)
  have un4 : (D^(m+4)) w ∉ escapeHeadBand A U w (m+4) := by
    rw [←f6]
    exact H.head.unpaid
  have un3 : (D^(m+3)) w∉escapeHeadBand A U w (m+3) :=
    head_power_unpaid_predecessor H.head.coreStable (n:=m+3) (by omega) un4
  have un2 : (D^(m+2)) w∉escapeHeadBand A U w (m+2) :=
    head_power_unpaid_predecessor H.head.coreStable (n:=m+2) (by omega) un3
  have v4 : D v∈zeroSpace A 4 := diag_zeroSpace A 3 hv
  have a0 : v∈zeroSpace A 5 := zeroSpace_mono A (by decide : 3≤5) hv
  have a1 : D v∈zeroSpace A 5 := zeroSpace_mono A (by decide : 4≤5) v4
  have a2 : D (D v)∈zeroSpace A 5 := diag_zeroSpace A 4 v4
  rw [f5] at a0 a1 a2
  have b0 := clock_chain_drop_of_next_unpaid H.head.coreStable (m+2) un3 a0 a1
  have b1 := clock_chain_drop_of_next_unpaid H.head.coreStable (m+2) un3 a1 a2
  have c0 := clock_chain_drop_of_next_unpaid H.head.coreStable (m+1) un2 b0 b1
  obtain ⟨u,hu,T,td,repT⟩ := HeadFiber.exists_poly c0
  have tn : T≠0 := by
    intro z
    have eq : v=u := by simpa only [z,map_zero,add_zero] using repT
    exact off (eq.symm ▸ hu)
  have tm : T.natDegree<m+1 := (natDegree_lt_iff_degree_lt tn).mpr td
  exact ⟨u,hu,T,tn,by omega,repT⟩

-- The one ring calculation is over scalar variables, not over the
-- dependent Fin 19 stage arrays or evalNodes/weightedEval maps.
private theorem overlap_row_identity
    (g v w a u p q t mark : K)
    (rg : g=a+q*w+mark) (rv : v=u+t*w) (noMark : v*mark=0) :
    (g*t-q*p)*w=v*a+q*(v*w-p*w)-g*u := by
  linear_combination v*rg - g*rv + noMark

set_option maxHeartbeats 700000 in
/-- Original-stage elimination and the fresh-site count force GT=QP with
deg Q≤5. The P argument is retained, so this is the *same* multiplier
which went into both preterminal scalar ports. -/
theorem NativeMarkedEscapeChart.cubic_overlap_of_profile
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (out : v∉U) (room : 3≤r)
    (vs : U.map (diag v)≤U) (pd : P.natDegree≤3)
    (profile : v*w-weightedEval (nodes A) w P∈U) :
    ∃ T Q : K[X], T≠0 ∧ Q≠0 ∧ T.natDegree+3≤r ∧ Q.natDegree≤5 ∧ G*T=Q*P := by
  let c := nodes A
  obtain ⟨u,uu,T,tn,td,vRep⟩ := H.head.grade_three_short_head_rep room hv out
  obtain ⟨d,hd,gRep⟩ := H.early_mesh_exact_mark ha ho early
  obtain ⟨a,au,Q,qd,dRep⟩ := HeadFiber.exists_poly hd
  have qb : Q.natDegree≤r+1 := by
    by_cases z : Q=0
    · simp [z]
    · have lt : Q.natDegree<r+2 := (natDegree_lt_iff_degree_lt z).mpr qd
      omega
  have vLast : v (Fin.last 18)=0 := early_terminal_zeroSpace_five_last ho
    H.head.paidRanks.lastActive early (zeroSpace_mono A (by decide : 3≤5) hv)
  have whole : evalNodes A G=a+weightedEval c w Q+G.eval 1 • coordinate (Fin.last 18) := by
    simpa only [dRep,c] using gRep
  have stable (f : Fin 19→K) (hf : f∈U) : diag c f∈U :=
    H.head.head.coreStable (Submodule.mem_map_of_mem hf)
  have va : diag v a∈U := vs (Submodule.mem_map_of_mem au)
  have mulQ : (fun i=>Q.eval (c i)*(v*w-weightedEval c w P) i)∈U :=
    clock_function_mem (c:=c) stable Q.eval profile
  have mulG : (fun i=>G.eval (c i)*u i)∈U :=
    clock_function_mem (c:=c) stable G.eval uu
  have identity : weightedEval c w (G*T-Q*P) =
      diag v a + (fun i=>Q.eval (c i)*(v*w-weightedEval c w P) i) -
      (fun i=>G.eval (c i)*u i) := by
    funext i
    have noMark : v i*coordinate (K:=K) (Fin.last 18) i=0 := by
      by_cases tag : i=Fin.last 18
      · rw [tag,vLast,zero_mul]
      · have offMark : coordinate (K:=K) (Fin.last 18) i=0 :=
          @Pi.single_eq_of_ne (Fin 19) (fun _=>K) _ (Classical.decEq _) (Fin.last 18) i tag 1
        rw [offMark,mul_zero]
    have rg := congrFun whole i
    have rv := congrFun vRep i
    simp only [evalNodes_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,weightedEval_apply] at rg
    simp only [Pi.add_apply,weightedEval_apply] at rv
    change G.eval (c i)=a i+Q.eval (c i)*w i+G.eval 1*coordinate (Fin.last 18) i at rg
    change v i=u i+T.eval (c i)*w i at rv
    have tagZero : v i*(G.eval 1*coordinate (K:=K) (Fin.last 18) i)=0 := calc
      _ = G.eval 1*(v i*coordinate (K:=K) (Fin.last 18) i) := mul_left_comm _ _ _
      _ = 0 := by rw [noMark,mul_zero]
    simp only [weightedEval_apply,eval_sub,eval_mul,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,diag_apply]
    exact overlap_row_identity (G.eval (c i)) (v i) (w i) (a i) (u i)
      (P.eval (c i)) (Q.eval (c i)) (T.eval (c i)) _ rg rv tagZero
  have inU : weightedEval c w (G*T-Q*P)∈U := by
    rw [identity]
    exact U.sub_mem (U.add_mem va mulQ) mulG
  have dg : G.natDegree=7 := H.first.degree
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at dg; omega
  have width := H.more_head_clocks ha ho (m:=2) (by decide)
  have width' : r+4 < (HeadFiber.escapeSites c w U).card := width
  have natbound : (G*T-Q*P).natDegree≤r+4 := by
    have dt : (G*T).natDegree≤r+4 := (natDegree_mul_le (p:=G) (q:=T)).trans (by omega)
    have dq : (Q*P).natDegree≤r+4 := (natDegree_mul_le_of_le qb pd).trans (by omega)
    simpa only [max_self] using natDegree_sub_le_of_le dt dq
  have payCast : ((G*T-Q*P).natDegree : WithBot ℕ) <
      ((HeadFiber.escapeSites c w U).card : WithBot ℕ) :=
    WithBot.coe_lt_coe.mpr (natbound.trans_lt width')
  have bound : (G*T-Q*P).degree < ((HeadFiber.escapeSites c w U).card : WithBot ℕ) :=
    degree_le_natDegree.trans_lt payCast
  have eq : G*T=Q*P := sub_eq_zero.mp
    (HeadFiber.faithful_on_escape_sites H.head.head.coreStable bound inU)
  have qn : Q≠0 := by
    intro z
    rw [z,zero_mul] at eq
    exact mul_ne_zero gn tn eq
  have r4 := H.radius_le_four ha ho
  exact ⟨T,Q,tn,qn,td,by omega,eq⟩

/-- The exact field-theoretic overlap required by the downstream cubic
pencil test, stated for any literal de-X factor B. -/
theorem not_coprime_of_degree_seven_overlap {B T Q : K[X]}
    (dG : G.natDegree=7) (gX : G=X*B)
    (qn : Q≠0) (qd : Q.natDegree≤5) (eq : G*T=Q*P) :
    ¬IsCoprime B P := by
  intro cop
  have bn : B≠0 := by
    intro z
    rw [gX,z,mul_zero,natDegree_zero] at dG
    omega
  rw [gX,natDegree_X_mul bn] at dG
  have multiple : B∣Q*P := ⟨X*T,by rw [←eq,gX]; ac_rfl⟩
  have divQ : B∣Q := cop.dvd_of_dvd_mul_right multiple
  have low : B.natDegree≤Q.natDegree := natDegree_le_of_dvd divQ qn
  omega

theorem NativeMarkedEscapeChart.early_pencil_ports_with_overlap
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (off : v∉U) :
    ∃ (P J : K[X]) (scale : K) (k l : Fin 19),
      P≠0 ∧ P.natDegree≤3 ∧ (J=0 ∨ NativeEarlyF7Mode A U w r J) ∧
      NativeMarkedCubicPortPair A G P J scale k l ∧
      ∀ B : K[X], G=X*B → ¬IsCoprime B P := by
  by_cases room : 3≤r
  · obtain ⟨stable,P,pn,pd,pr⟩ := H.low_multiplier_profile ha ho (d:=3) (Or.inr rfl) room hv off
    obtain ⟨J,jmode,scale,k,l,pair⟩ := H.two_preterminal_cubic_ports ha ho early hv stable pd pn pr
    obtain ⟨T,Q,_,qn,_,qd,rel⟩ := H.cubic_overlap_of_profile ha ho early hv off room stable pd pr
    exact ⟨P,J,scale,k,l,pn,pd,jmode,pair,fun B hb =>
      not_coprime_of_degree_seven_overlap H.first.degree hb qn qd rel⟩
  · have eqr : r=2 := by have := H.head.headBounds.1; omega
    subst r
    exact (off (radius_two_grade_three_core H.head hv)).elim

end
end RKResearch.Certified.Graded.ERK13NativeFirst
