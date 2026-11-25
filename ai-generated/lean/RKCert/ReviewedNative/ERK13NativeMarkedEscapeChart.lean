module

public import RKCert.ReviewedNative.ERK13NativeMarkedStaircase
public import RKCert.ReviewedNative.PaidMarkedAdjacentClock

import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The propagated actual marked first-escape chart

The rank input is the checked staircase. A single first alias advances the
polynomial block under the original clock. There is no assumed mode on an
unmarked grade and no folded or ghost tableau. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape MarkedAdjacent
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {r a : ℕ} {G : K[X]}

abbrev escapeHeadBand (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (n : ℕ) :=
  chain (diag (nodes A)) U w n

abbrev markedEscapeHeadBand (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) (n : ℕ) :=
  escapeHeadBand A U w n ⊔ terminalMark A b

theorem escapeHeadBand_mono {n m : ℕ} (h : n≤m) :
    escapeHeadBand A U w n ≤ escapeHeadBand A U w m := by
  have inc := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) m).mp le_rfl
  exact (clock_chain_le_iff n).mpr ⟨inc.1,fun i hi=>inc.2 i (lt_of_lt_of_le hi h)⟩

theorem escapeHeadBand_map_succ (stable : U.map (diag (nodes A))≤U) {n : ℕ} (hn : 0<n) :
    (escapeHeadBand A U w n).map (diag (nodes A))≤escapeHeadBand A U w (n+1) :=
  le_sup_right.trans (clock_chain_next stable hn).le

theorem markedEscapeHeadBand_clock_step (stable : U.map (diag (nodes A))≤U)
    {n : ℕ} (hn : 0<n) :
    markedEscapeHeadBand A b U w n ⊔ (markedEscapeHeadBand A b U w n).map (diag (nodes A)) =
      markedEscapeHeadBand A b U w (n+1) := by
  change (escapeHeadBand A U w n ⊔ terminalMark A b) ⊔
     (escapeHeadBand A U w n ⊔ terminalMark A b).map (diag (nodes A)) = _
  rw [Submodule.map_sup,sup_sup_sup_comm,clock_chain_next stable hn,
    sup_eq_left.mpr (terminalMark_clock A b)]

theorem escapeHeadBand_paid_from_six (H : NativePaidHead A b r U w) (m : ℕ) :
    escapeHeadBand A U w (r+1+m) ≤ zeroSpace A (6+m) := by
  induction m with
  | zero =>
    have e : zeroSpace A 6=escapeHeadBand A U w (r+1) := H.head.flags 1 le_rfl
    simpa only [Nat.add_zero,e] using
      (le_rfl : escapeHeadBand A U w (r+1)≤escapeHeadBand A U w (r+1))
  | succ m ih =>
    have e : escapeHeadBand A U w (r+1+(m+1)) = escapeHeadBand A U w (r+1+m) ⊔
        (escapeHeadBand A U w (r+1+m)).map (diag (nodes A)) := by
      exact (clock_chain_next (w:=w) H.head.coreStable (n:=r+1+m) (by omega)).symm
    rw [e]
    apply sup_le
    · exact ih.trans (zeroSpace_mono A (by omega))
    · rintro _ ⟨x,hx,rfl⟩
      have hz : diag (nodes A) x ∈ zeroSpace A ((6+m)+1) :=
        diag_zeroSpace A (6+m) (ih hx)
      exact hz

theorem escapeHeadBand_paid_from_seven (H : NativePaidHead A b r U w) (m : ℕ) :
    escapeHeadBand A U w (r+2+m) ≤ zeroSpace A (7+m) := by
  have t := escapeHeadBand_paid_from_six H (m+1)
  rwa [show r+1+(m+1)=r+2+m by omega,show 6+(m+1)=7+m by omega] at t

private theorem escapeHeadBand_rank_cap (n : ℕ) :
    finrank K (escapeHeadBand A U w n)≤finrank K U+n := by
  induction n with
  | zero =>
    change finrank K U≤finrank K U+0
    omega
  | succ n ih =>
    by_cases paid : (diag (nodes A)^n) w∈escapeHeadBand A U w n
    · have eq : escapeHeadBand A U w (n+1)=escapeHeadBand A U w n :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr paid)
      rw [eq]
      omega
    · change finrank K (↥(escapeHeadBand A U w n ⊔
          (K ∙ ((diag (nodes A)^n) w)) : Submodule K (Fin 19 → K))) ≤ _
      rw [Submodule.finrank_sup_span_singleton paid]
      omega

theorem first_alias_mem_markedEscapeHeadBand (H : NativePaidHead A b r U w)
    (F : FirstEscape A b a G) : evalNodes A G∈markedEscapeHeadBand A b U w (r+2) := by
  change evalNodes A G∈chain (diag (nodes A)) U w (r+2)⊔terminalMark A b
  rw [←H.escapeShape]
  exact F.paid

/-- Chart advance of the degree-`a` clock sector: trim by the literal
first alias and keep the resulting defect-and-mark portion separate. -/
theorem coeffEval_map_clock_le_first_marked (H : NativePaidHead A b r U w)
    (F : FirstEscape A b a G) :
    ((coeffEval A a).range).map (diag (nodes A)) ≤
      (coeffEval A a).range ⊔ markedEscapeHeadBand A b U w (r+2) := by
  rintro _ ⟨f,hf,rfl⟩
  obtain ⟨P,pd,rfl⟩ := exists_polynomial_of_coeff_range hf
  have xd : (X*P).natDegree≤a+1 := natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  obtain ⟨q,qd⟩ := reduction_by_next_degree xd F.degree
  have hl : evalNodes A (X*P-q • G)∈(coeffEval A a).range :=
    ⟨_,(evalNodes_eq_coeffEval A _ qd).symm⟩
  have hg := first_alias_mem_markedEscapeHeadBand H F
  rw [←evalNodes_X_mul A P,show X*P=(X*P-q • G)+q • G by abel,map_add,map_smul]
  exact ((coeffEval A a).range ⊔ markedEscapeHeadBand A b U w (r+2)).add_mem
    (Submodule.mem_sup_left hl)
    (Submodule.mem_sup_right ((markedEscapeHeadBand A b U w (r+2)).smul_mem _ hg))

/-- All charts are indexed by the number of actual advances after
first escape. Both `a=5` and `a=6` have the same head-length increment. -/
structure NativeMarkedEscapeChart (A : Matrix (Fin 19) (Fin 19) K)
    (b : Fin 19 → K) (a : ℕ) (G : K[X]) (r : ℕ)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K) : Prop where
  seed : firstSeed A b=0
  head : NativePaidHead A b r U w
  first : FirstEscape A b a G
  chart : ∀ m, a+1+m≤10 → markedTreeSpace A b (a+1+m)=
      (coeffEval A a).range⊔markedEscapeHeadBand A b U w (r+2+m)
  separated : ∀ m, a+1+m≤10 → ∀ P : K[X], P.natDegree≤a →
    evalNodes A P∈markedEscapeHeadBand A b U w (r+2+m) → P=0

theorem native_marked_escape_chart (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (H : NativePaidHead A b r U w) (F : FirstEscape A b a G) :
    NativeMarkedEscapeChart A b a G r U w := by
  have aw : a=5 ∨ a=6 := F.width.elim Or.inr (fun h=>Or.inl h.1)
  obtain ⟨ranks,steps⟩ := marked_staircase_ranks13 ha ho H seed
  let V := (coeffEval A a).range
  let D := diag (nodes A)
  let Z (n : ℕ) := markedEscapeHeadBand A b U w n
  have chart (m : ℕ) : a+1+m≤10 → markedTreeSpace A b (a+1+m)=V⊔Z (r+2+m) := by
    induction m with
    | zero =>
      intro _
      simpa only [Nat.add_zero,V,Z,←H.escapeShape] using F.decomposition
    | succ m ih =>
      intro hm
      have next := steps (a+1+m) (by omega) (by omega)
      rw [show a+1+(m+1)=(a+1+m)+1 by omega,next,ih (by omega)]
      change (V⊔Z (r+2+m))⊔(V⊔Z (r+2+m)).map D = V⊔Z (r+2+(m+1))
      rw [Submodule.map_sup,sup_sup_sup_comm,
        markedEscapeHeadBand_clock_step H.head.coreStable (by omega),
        show r+2+(m+1)=r+2+m+1 by omega]
      have cv : V.map D≤V⊔Z (r+2+m+1) :=
        (coeffEval_map_clock_le_first_marked H F).trans
          (sup_le_sup le_rfl (sup_le_sup (escapeHeadBand_mono (by omega)) le_rfl))
      exact le_antisymm (sup_le (sup_le le_sup_left cv) le_sup_right)
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  refine ⟨seed,H,F,chart,?_⟩
  intro m pay P pd e
  have rr := ranks (a+1+m) (by omega) pay
  have hu := H.head.baseRank
  rw [H.five] at hu
  have bc := escapeHeadBand_rank_cap (A:=A) (U:=U) (w:=w) (r+2+m)
  have br := rank_sup_terminalMark (A:=A) (b:=b) (escapeHeadBand A U w (r+2+m))
    (fun _ hz=>last_coordinate_not_defect ho (j:=7+m) H.paidRanks.lastActive
      (by omega) (escapeHeadBand_paid_from_seven H m hz))
  change finrank K (Z (r+2+m))=finrank K (escapeHeadBand A U w (r+2+m))+terminalDebit A b at br
  rw [terminalDebit,ite_eq_left seed] at br
  have cap : finrank K (Z (r+2+m))≤8+m := by omega
  have dim : finrank K (↥(V⊔Z (r+2+m) : Submodule K (Fin 19→K))) = a+1+(8+m) := calc
    _ = finrank K (markedTreeSpace A b (a+1+m)) :=
      congrArg (fun T : Submodule K (Fin 19→K) => finrank K T) (chart m pay).symm
    _ = a+1+m+8 := rr
    _ = a+1+(8+m) := by omega
  exact polynomial_buffer_separated ha ho (by omega) cap dim pd e

/-- The checked marked rank jump pays a real number of unmarked head clocks.
The terminal line does not get counted as an extra clock. -/
theorem NativeMarkedEscapeChart.more_head_clocks
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {m : ℕ} (pay : a+1+m≤9) :
    r+2+m<(HeadFiber.escapeSites (nodes A) w U).card := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  obtain ⟨rr,_⟩ := marked_staircase_ranks13 ha ho H.head H.seed
  apply HeadFiber.more_escape_sites H.head.head.coreStable (by omega)
  intro invariant
  have eq : escapeHeadBand A U w (r+2+m+1)=escapeHeadBand A U w (r+2+m) :=
    (clock_chain_next H.head.head.coreStable (by omega)).symm.trans (sup_eq_left.mpr invariant)
  have markedEq : markedEscapeHeadBand A b U w (r+2+(m+1)) =
      markedEscapeHeadBand A b U w (r+2+m) :=
    congrArg (fun Z : Submodule K (Fin 19→K) => Z⊔terminalMark A b) eq
  have eqT : markedTreeSpace A b (a+1+(m+1))=markedTreeSpace A b (a+1+m) := calc
    _ = (coeffEval A a).range⊔markedEscapeHeadBand A b U w (r+2+(m+1)) := H.chart (m+1) (by omega)
    _ = (coeffEval A a).range⊔markedEscapeHeadBand A b U w (r+2+m) :=
      congrArg (fun Z : Submodule K (Fin 19→K) => (coeffEval A a).range⊔Z) markedEq
    _ = _ := (H.chart m (by omega)).symm
  have eqR : a+1+(m+1)+8=a+1+m+8 := calc
    _ = finrank K (markedTreeSpace A b (a+1+(m+1))) := (rr _ (by omega) (by omega)).symm
    _ = finrank K (markedTreeSpace A b (a+1+m)) :=
      congrArg (fun S : Submodule K (Fin 19→K) => finrank K S) eqT
    _ = _ := rr _ (by omega) (by omega)
  omega

/-- Split only the actual first alias, and retain its six paid marked
moments without choosing when the terminal enters the ordinary flag. -/
theorem NativeMarkedEscapeChart.mesh_moments
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    G.eval 0=0 ∧ (∀ k≤5, unitMoment K k G=unitMoment K 0 G) ∧
      ∀ k<5, endpointMoment K k G=0 := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  have paid := escape_paid A b H.first.paid
  have dg := H.first.degree
  refine ⟨origin_of_marked_defect_polynomial ha (by decide) paid,?_,?_⟩
  · intro k hk
    exact unitMoment_eq_initial_of_marked_defect ha ho H.head.paidRanks.lastActive
      (by omega) (by omega) paid
  · intro k hk
    exact endpointMoment_zero_of_marked_defect ha ho H.head.paidRanks.lastActive
      (by omega) (by omega) paid

end
end RKResearch.Certified.Graded.ERK13NativeFirst
