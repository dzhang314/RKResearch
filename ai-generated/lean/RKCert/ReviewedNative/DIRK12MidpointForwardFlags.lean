module

public import RKCert.ReviewedNative.DIRK12MidpointCausalRows
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Literal low forward defects of the physical midpoint DIRK tableau.
The only remaining low-forward tests are the stated, deghosted live
primitive equations; the terminal needs no separate primitive system. -/
namespace RKResearch.Certified.DIRK12MidpointForward

open RKResearch Graded DualSupport12VectorReplay DIRK12MidpointGhost
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

set_option linter.unusedSectionVars false

/-- Embed the three literal h, p h, p² h profiles in the physical rows. -/
def gen (k : Nat) (i : Fin 15) : K :=
  Fin.cases (motive:=fun _ => K) 0 (fun r =>
    Fin.addCases (motive:=fun _ => K) (fun g : Fin 4 => (lift k g : K)) (fun _ : Fin 10 => 0) r) i

@[simp] theorem gen_origin (k : Nat) : gen (K:=K) k 0 = 0 := rfl

@[simp] theorem gen_hidden (k : Nat) (g : Fin 4) : gen (K:=K) k (hidden g) = (lift k g : K) := by
  simp [gen,hidden]

@[simp] theorem gen_visible (k : Nat) (j : Fin 10) : gen (K:=K) k (visible j) = 0 := by
  simp [gen,visible]

theorem gen_supported (k : Nat) : DualSupport12.supported ghost (gen (K:=K) k) := by
  intro i
  refine stage_cases (P:=fun j => ¬ ghost j → gen (K:=K) k j=0) ?_ ?_ ?_ i
  · simp
  · intro g h
    exact (h (ghost_hidden g)).elim
  · simp

abbrev forwardBand (K : Type*) [Field K] [CharZero K] (j : Nat) : Submodule K (V15 K) :=
  band (gen (K:=K)) j

theorem fw_zero (j : Nat) (hj : j ≤ 2) : forwardBand K j = ⊥ := by
  have z : width j = 0 := by unfold width; omega
  simp [forwardBand,band,z]

theorem fw_support (j : Nat) (v : V15 K) (hv : v ∈ forwardBand K j) :
    DualSupport12.supported ghost v := by
  intro i hi
  exact span_by_zero (gen (K:=K)) j (M:=LinearMap.proj i) (fun k => gen_supported k.val i hi) v hv

/-- A three-term coefficient receipt with unused positions explicitly zero. -/
def profile (w : Fin 3 → K) (i : Fin 15) : K := ∑ l, w l * gen l.val i

theorem profile_mem (j : Nat) (w : Fin 3 → K)
    (h : ∀ l : Fin 3, ¬ l.val < width j → w l=0) : profile w ∈ forwardBand K j := by
  have e : (profile w : V15 K) = ∑ l : Fin 3, w l • gen l.val := by
    ext i
    simp [profile,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [e]
  apply Submodule.sum_mem
  intro l _
  by_cases hl : l.val < width j
  · exact (forwardBand K j).smul_mem _ (span_gen (⟨l.val,hl⟩ : Fin (width j)))
  · simp [h l hl]

private theorem power_silent (k : Fin 3) :
    (∑ g : Fin 4, (tap g : K)*(lift k.val g : K))=0 := by
  have e := congrArg (fun r : Rat => (r : K)) (tap_annihilates k)
  simpa [add4,add_assoc,Fin.sum_univ_succ] using e

private theorem power_integral (k : Fin 5) :
    (∑ g : Fin 4, (tap g : K)*(clock g : K)^(k.val+1)) =
      1/((k.val+2:Nat):K) := by
  have e := congrArg (fun r : Rat => (r : K)) (moments k)
  simpa [add4,add_assoc,Fin.sum_univ_succ,Rat.cast_div] using e

namespace Feed

variable (P : Feed K)

private theorem action_sum (v : V15 K) (i : Fin 15) :
    mat P.tableau v i = P.tableau i 0*v 0 +
      ((∑ g, P.tableau i (hidden g)*v (hidden g)) +
        ∑ j, P.tableau i (visible j)*v (visible j)) :=
  sum_stages (fun j => P.tableau i j*v j)

theorem gen_nonterminal_zero (k : Fin 2) (j : Fin 10) (hn : visible j ≠ terminal) :
    mat P.tableau (gen k.val) (visible j) = 0 := by
  rw [action_sum]
  simp only [gen_origin,gen_hidden,gen_visible,mul_zero,Finset.sum_const_zero,zero_add,add_zero,
    tableau_nonterminal_tap _ _ _ hn]
  have d (g : Fin 4) : (tap g : K)*(P.mode0 j+P.mode1 j*P.clocks (hidden g))*(lift k.val g : K) =
    P.mode0 j*((tap g : K)*(lift k.val g : K)) +
    (P.mode1 j*P.a)*((tap g : K)*(lift (k.val+1) g : K)) := by
    rw [clocks_hidden]
    simp only [lift,Rat.cast_mul,Rat.cast_pow,pow_succ]
    ring
  simp_rw [ghostTap,d]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    power_silent (K:=K) (⟨k.val, by omega⟩ : Fin 3),
    power_silent (K:=K) (⟨k.val+1, by omega⟩ : Fin 3)]
  ring

private theorem output_terminal (v : V15 K) (bT : P.b terminal ≠ 0)
    (ghosts : ∀ g : Fin 4, P.b (hidden g)=0)
    (quiet : row P.b v=0)
    (others : ∀ i, ¬ ghost i → i≠terminal → v i=0) :
    v terminal=0 := by
  rw [row_apply,dotProduct,Fin.sum_univ_castSucc] at quiet
  have e (i : Fin 14) : P.b i.castSucc*v i.castSucc=0 := by
    by_cases g : ghost i.castSucc
    · have hg : ∃ r : Fin 4, hidden r=i.castSucc := by
        change 1 ≤ i.val ∧ i.val ≤ 4 at g
        refine ⟨⟨i.val-1,by omega⟩,?_⟩
        apply Fin.ext
        simp
        omega
      obtain ⟨r,hr⟩ := hg
      rw [←hr,ghosts,zero_mul]
    · have hn : i.castSucc ≠ terminal := by
        intro he
        have q := congrArg Fin.val he
        simp only [Fin.val_castSucc,Fin.val_last] at q
        omega
      rw [others _ g hn,mul_zero]
  rw [Finset.sum_eq_zero (fun i _ => e i),zero_add] at quiet
  exact (mul_eq_zero.mp quiet).resolve_left bT

private theorem dual_row (z v : V15 K) :
    row z (mat P.tableau v) = row (mat P.tableau.transpose z) v := by
  rw [row_apply,row_apply,mat_apply,mat_apply,dotProduct_comm (P.tableau.transpose *ᵥ z),
    Matrix.dotProduct_transpose_mulVec]

private theorem silent_ghost (v : V15 K)
    (ghosts : ∀ g : Fin 4, P.b (hidden g)=0) (hv : DualSupport12.supported ghost v) :
    row (P.b*(1-P.clocks)) v = 0 := by
  rw [row_apply,dotProduct,sum_stages]
  simp only [Pi.mul_apply,Pi.sub_apply,Pi.one_apply,ghosts,zero_mul,Finset.sum_const_zero]
  simp only [hv 0 non_ghost_origin, mul_zero, zero_add]
  exact Finset.sum_eq_zero (fun j _ => by simp [hv _ (non_ghost_visible j)])

theorem gen_action (k : Fin 2) (bT : P.b terminal ≠ 0)
    (ghosts : ∀ g : Fin 4, P.b (hidden g)=0)
    (adj : mat P.tableau.transpose P.b=P.b*(1-P.clocks)) :
    mat P.tableau (gen k.val) = profile (fun l => P.a*(imageCoeff k l : K)) := by
  have org : mat P.tableau (gen k.val) 0=0 := by
    simp [action_sum,tableau_origin]
  have term : mat P.tableau (gen k.val) terminal=0 := by
    apply P.output_terminal _ bT ghosts
    · rw [dual_row,adj]
      exact P.silent_ghost _ ghosts (gen_supported k.val)
    · apply stage_cases
      · exact fun _ _ => org
      · intro g hg
        exact (hg (ghost_hidden g)).elim
      · intro j _ hn
        exact P.gen_nonterminal_zero k j hn
  funext i
  refine stage_cases (P:=fun i => mat P.tableau (gen k.val) i=profile _ i) ?_ ?_ ?_ i
  · simp [org,profile]
  · intro g
    rw [action_sum]
    simp only [gen_origin,gen_hidden,gen_visible,tableau_hidden_hidden,mul_zero,
      Finset.sum_const_zero,zero_add,add_zero,profile]
    have sum4 : (∑ h : Fin 4, (P.a*(block g h : K))*(lift k.val h : K)) =
        P.a * ∑ h : Fin 4, (block g h : K)*(lift k.val h : K) := by
      simp only [Finset.mul_sum,mul_assoc]
    have e := congrArg (fun r : Rat => (r : K)) (action_lift k g)
    have ce : (∑ h : Fin 4, (block g h : K)*(lift k.val h : K)) =
        ∑ l : Fin 3, (imageCoeff k l : K)*(lift l.val g : K) := by
      simpa [act,add4,add3,add_assoc,Fin.sum_univ_succ] using e
    rw [sum4,ce]
    simp only [Finset.mul_sum,mul_assoc]
  · intro j
    have e : mat P.tableau (gen k.val) (visible j)=0 := by
      by_cases h : visible j=terminal
      · rw [h,term]
      · exact P.gen_nonterminal_zero k j h
    simp [e,profile]

theorem fw_A (bT : P.b terminal ≠ 0) (ghosts : ∀ g : Fin 4, P.b (hidden g)=0)
    (adj : mat P.tableau.transpose P.b=P.b*(1-P.clocks))
    (j : Nat) (hj : j < 5) : ∀ v ∈ forwardBand K j, mat P.tableau v ∈ forwardBand K (j+1) := by
  apply span_by_linear (gen (K:=K)) j
  intro k
  have k2 : k.val < 2 := by have h := k.isLt; unfold width at h; omega
  rw [P.gen_action ⟨k.val,k2⟩ bT ghosts adj]
  apply profile_mem
  intro l hl
  have hkl : k.val+1 < l.val := by have h := k.isLt; unfold width at hl h; omega
  simp [imageCoeff_zero (⟨k.val,k2⟩ : Fin 2) l hkl]

theorem clock_action (k : Nat) :
    P.clocks * gen (K:=K) k = P.a • gen (k+1) := by
  funext i
  refine stage_cases (P:=fun i => (P.clocks*gen (K:=K) k) i=(P.a • gen (K:=K) (k+1)) i) ?_ ?_ ?_ i
  · simp [Pi.mul_apply,Pi.smul_apply]
  · intro g
    simp only [Pi.mul_apply,Pi.smul_apply,clocks_hidden,gen_hidden,smul_eq_mul,lift,
      Rat.cast_mul,Rat.cast_pow,pow_succ]
    ring
  · intro j
    simp [Pi.mul_apply,Pi.smul_apply]

theorem fw_C (j : Nat) (hj : j < 5) :
    ∀ v ∈ forwardBand K j, nodes P.tableau * v ∈ forwardBand K (j+1) := by
  intro v hv
  rw [nodes_tableau]
  change diag P.clocks v ∈ _
  refine span_by_linear (gen (K:=K)) j ?_ v hv
  intro k
  have h : k.val+1 < width (j+1) := by have g := k.isLt; unfold width at g ⊢; omega
  change P.clocks*gen k.val ∈ _
  rw [clock_action]
  exact (forwardBand K (j+1)).smul_mem _ (span_gen (⟨k.val+1,h⟩ : Fin (width (j+1))))

theorem primitive_zero : DualSupport12.forward P.tableau 0 = 0 := by
  simp [DualSupport12.forward,nodes]

private theorem primitive_at (n : Nat) (i : Fin 15) :
    DualSupport12.forward P.tableau n i =
      ((n+1:Nat):K) * (mat P.tableau (P.clocks^n)) i - P.clocks i^(n+1) := by
  simp only [DualSupport12.forward,nodes_tableau,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply]

theorem primitive_origin (n : Nat) : DualSupport12.forward P.tableau n 0 = 0 := by
  rw [primitive_at,action_sum]
  simp [tableau_origin,Pi.pow_apply]

theorem primitive_hidden (m : Fin 4) (g : Fin 4) :
    DualSupport12.forward P.tableau (m.val+1) (hidden g) =
      profile (fun l => P.a^(m.val+2)*(primitiveCoeff m l : K)) (hidden g) := by
  rw [primitive_at,action_sum]
  simp only [Pi.pow_apply,clocks_origin,zero_pow (by omega : m.val+1 ≠ 0),mul_zero,
    tableau_hidden_hidden,clocks_hidden,tableau_hidden_visible,zero_mul,Finset.sum_const_zero,
    zero_add,add_zero,mul_pow,profile,gen_hidden]
  have sum4 : (∑ h : Fin 4, (P.a*(block g h : K)) *
       (P.a^(m.val+1)*(clock h : K)^(m.val+1))) =
      P.a^(m.val+2)*∑ h : Fin 4, (block g h : K)*(clock h : K)^(m.val+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [show m.val+2=m.val+1+1 by omega,pow_succ]
    ring
  have e := congrArg (fun r : Rat => (r : K)) (primitive_lift m g)
  have ce : ((m.val+2:Nat):K) * (∑ h : Fin 4, (block g h : K)*(clock h : K)^(m.val+1)) -
       (clock g : K)^(m.val+2) =
       ∑ l : Fin 3, (primitiveCoeff m l : K)*(lift l.val g : K) := by
    simpa [act,add4,add3,add_assoc,Fin.sum_univ_succ] using e
  rw [sum4,show m.val+1+1=m.val+2 by omega]
  have ef : (∑ l : Fin 3, (P.a^(m.val+2)*(primitiveCoeff m l : K))*(lift l.val g : K)) =
      P.a^(m.val+2)*∑ l : Fin 3, (primitiveCoeff m l : K)*(lift l.val g : K) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [ef]
  linear_combination P.a^(m.val+2)*ce

/-- The sole remaining first-through-fourth primitive tests on the live data.
All ghost effects have been paid and removed from this equation. -/
def LiveBudget : Prop :=
  ∀ (m : Fin 4) (i : Fin 10), visible i ≠ terminal →
    ((m.val+2:Nat):K) * (∑ j, (if i<j then 0 else P.live i j) * P.cVisible j^(m.val+1)) +
      P.mode0 i*P.a^(m.val+1) +
      (((m.val+2:Nat):K)/((m.val+3:Nat):K))*P.mode1 i*P.a^(m.val+2) =
      P.cVisible i^(m.val+2)

theorem primitive_nonterminal_live (h : P.LiveBudget) (m : Fin 4) (i : Fin 10)
    (hn : visible i ≠ terminal) :
    DualSupport12.forward P.tableau (m.val+1) (visible i)=0 := by
  rw [primitive_at,action_sum]
  simp only [Pi.pow_apply,clocks_origin,zero_pow (by omega : m.val+1 ≠ 0),mul_zero,
    zero_add,clocks_visible,tableau_nonterminal_live _ _ _ hn,tableau_nonterminal_tap _ _ _ hn]
  have gf (g : Fin 4) : P.ghostTap i g * P.clocks (hidden g)^(m.val+1) =
      (P.mode0 i*P.a^(m.val+1))*((tap g : K)*(clock g : K)^(m.val+1)) +
      (P.mode1 i*P.a^(m.val+2))*((tap g : K)*(clock g : K)^(m.val+2)) := by
    simp only [ghostTap,clocks_hidden,mul_pow,show m.val+2=m.val+1+1 by omega,pow_succ]
    ring
  simp_rw [gf]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      power_integral (K:=K) (⟨m.val, by omega⟩ : Fin 5),
      power_integral (K:=K) (⟨m.val+1, by omega⟩ : Fin 5)]
  have e := h m i hn
  have nz : ((m.val+2:Nat):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show m.val+1+1=m.val+2 by omega, show m.val+1+2=m.val+3 by omega]
  field_simp [nz] at ⊢ e
  linear_combination e

theorem primitive_silent (j : Nat) (adj : mat P.tableau.transpose P.b=P.b*(1-P.clocks))
    (scalar : ∀ k < 12, ((k+1:Nat):K)*row P.b (P.clocks^k)=1) (hj : j < 5) :
    row P.b (DualSupport12.forward P.tableau j)=0 := by
  rw [DualSupport12.forward,nodes_tableau,map_sub,map_smul,smul_eq_mul,dual_row,adj]
  have e : row (P.b*(1-P.clocks)) (P.clocks^j) =
      row P.b (P.clocks^j)-row P.b (P.clocks^(j+1)) := by
    rw [pow_succ',← map_sub]
    simp only [row_apply,dotProduct,Pi.mul_apply,Pi.sub_apply,Pi.one_apply,Pi.pow_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e]
  have h0 := scalar j (by omega)
  have h1 := scalar (j+1) (by omega)
  push_cast at h0 h1 ⊢
  linear_combination h0-h1

/-- All low forward primitives once the deghosted nonterminal live equations
are supplied. The actual terminal follows by the paid adjoint and scalar moments. -/
theorem fw_primitive (bT : P.b terminal ≠ 0) (ghosts : ∀ g : Fin 4, P.b (hidden g)=0)
    (adj : mat P.tableau.transpose P.b=P.b*(1-P.clocks))
    (scalar : ∀ k < 12, ((k+1:Nat):K)*row P.b (P.clocks^k)=1)
    (live : P.LiveBudget) (j : Nat) (hj : j < 5) :
    DualSupport12.forward P.tableau j ∈ forwardBand K (j+1) := by
  cases j with
  | zero => simp [P.primitive_zero]
  | succ j =>
    let m : Fin 4 := ⟨j,by omega⟩
    have hterm : DualSupport12.forward P.tableau (j+1) terminal=0 := by
      apply P.output_terminal _ bT ghosts (P.primitive_silent _ adj scalar (by omega))
      apply stage_cases
      · exact fun _ _ => P.primitive_origin _
      · intro g hg
        exact (hg (ghost_hidden g)).elim
      · intro i _ hn
        exact P.primitive_nonterminal_live live m i hn
    have eq : DualSupport12.forward P.tableau (j+1) =
        profile (fun l => P.a^(m.val+2)*(primitiveCoeff m l : K)) := by
      funext i
      refine stage_cases (P:=fun i => DualSupport12.forward P.tableau (j+1) i = profile _ i) ?_ ?_ ?_ i
      · simp [P.primitive_origin,profile]
      · exact P.primitive_hidden m
      · intro i
        simp only [profile,gen_visible,mul_zero,Finset.sum_const_zero]
        by_cases hn : visible i = terminal
        · rw [hn]
          exact hterm
        · exact P.primitive_nonterminal_live live m i hn
    rw [eq]
    apply profile_mem
    intro l hl
    have hml : m.val ≤ l.val := by dsimp [m]; unfold width at hl; omega
    simp [primitiveCoeff_zero _ _ hml]

end Feed

end RKResearch.Certified.DIRK12MidpointForward

#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.fw_A
#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.fw_C
#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.fw_primitive
