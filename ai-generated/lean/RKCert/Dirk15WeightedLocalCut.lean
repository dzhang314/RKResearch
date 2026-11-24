module

public import RKCert.Dirk15LocalReverse
public import RKCert.FourDebutCut
public import RKCert.DirkWeightedFourInterface

@[expose] public section

/-! # Actual weighted four-debut input, without an unweighted assumption
The padded reverse projection retains zero-base and repeated-clock rows.
This certifies the paid input hypotheses, not the downstream weighted
four-debut exclusion. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial PivotProjection
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_local_projects_to_weighted_cut (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15CubicBudget A b)
    (inv : (markedTerminalZero (s:=19) A 15 3).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 3) :
    Nonempty (LocalProjection.WeightedFour K 20) := by
  obtain ⟨i,w,hi,pref,loc,H⟩ := order15_local_cubic_chart ha ho h inv
  let d := reverseCubic A b
  let y := mirror A
  let C' := diag y
  let N := transMat A
  let Pj := remove d i
  let N' := contracted N d i
  let M := markedTerminalZero (s:=19) A 15
  let Qsp := fun j => chain C' ⊥ (Pj w) (j-3)
  have proj (j : ℕ) (hl : 3≤j) (hu : j≤6) :
      (M j).map Pj=Qsp j := by
    change (markedTerminalZero A 15 j).map (remove (reverseCubic A b) i)=_
    rw [H j hl hu]
    exact projected_chain hi loc w _
  have d3 : d∈M 3 := order15_reverseCubic_mem ho h.terminal
  have mat_step {j : ℕ} (hj : j+2≤15) {v : Vec K 20} (hv : v∈M j) :
      N v∈M (j+1) :=
    ⟨marked_mat hj hv.1,prior_last_iff.mpr (h.terminal.trans_zero_terminal v)⟩
  have nd : N d∈M 4 := mat_step (by decide) d3
  have ynd : C' (N d)∈M 5 := markedTerminalZero_clock (by decide : 4+2≤15)
    (Submodule.mem_map_of_mem nd)
  have nnd : N (N d)∈M 5 := mat_step (by decide) nd
  have paid (u : Vec K 20) (k j : ℕ) (hle : k≤j) (hj : 3≤j) (hu : j≤6)
      (hg : u∈M k) : Pj u∈Qsp j := by
    rw [←proj j hj hu]
    exact Submodule.mem_map_of_mem (markedTerminalZero_mono A 15 hle hg)
  refine ⟨⟨y,Pj b,Pj w,N',?_,?_,?_,?_⟩⟩
  · have causal := contracted_causal (causalDiag_transpose ha) hi
      (fun j hj => pref j (Fin.rev_lt_rev.mp hj))
    intro j x z e
    have h₀ := causal j (x-z) (fun l hl => by
      rw [Pi.sub_apply,e l (Fin.rev_lt_rev.mp hl).le,sub_self])
    have h₁ : (x-z) j=0 := sub_eq_zero.mpr (e j le_rfl)
    rw [h₁,mul_zero,map_sub,Pi.sub_apply,sub_eq_zero] at h₀
    exact h₀
  · intro T hT
    change row (weightedEval y (remove d i b) T) 1=_
    rw [←remove_weighted loc,remove_sum (leaf_marked_zero d3.1)]
    exact (ReverseTrace.scalar A b (hT.trans (by decide : 7≤14))).weighted_sum ho
      (by decide : 14+1≤15)
  · intro m hm hm' P Q hp hq
    let v := weightedEval y b P-weightedEval y w Q
    have qpay : weightedEval y w Q∈M m := by
      change weightedEval y w Q∈markedTerminalZero A 15 m
      rw [H m hm (by omega)]
      have he : weightedEval y w Q=fun k => w k*Q.eval (y k) := by ext k; simp [mul_comm]
      rw [he]
      exact FourDebut.polynomial_head_mem hq
    have a : N (weightedEval y b P)-weightedEval y b (formalPrimitive P)∈M (m+1) := by
      refine ⟨weighted_reverse_primitive ho hp (by omega), prior_last_iff.mpr ?_⟩
      change transMat A _ (Fin.last 19)-(weightedEval (mirror A) b (formalPrimitive P)) (Fin.last 19)=0
      rw [h.terminal.trans_zero_terminal,weightedEval_apply,terminal_mirror_zero h.terminal,
        formalPrimitive_eval_zero,zero_mul,sub_zero]
    have a' : N v-weightedEval y b (formalPrimitive P)∈M (m+1) := by
      convert (M (m+1)).sub_mem a (mat_step (by omega) qpay) using 1
      rw [show N v=N (weightedEval y b P)-N (weightedEval y w Q) from map_sub N _ _]
      abel
    have ep : Pj v=weightedEval y (Pj b) P-weightedEval y (Pj w) Q := by
      change Pj (weightedEval y b P-weightedEval y w Q)=_
      rw [map_sub]
      exact congrArg₂ (· - ·) (remove_weighted loc b P) (remove_weighted loc w Q)
    have ej : Pj (weightedEval y b (formalPrimitive P)) =
        weightedEval y (Pj b) (formalPrimitive P) := remove_weighted loc b (formalPrimitive P)
    have e : N' (weightedEval y (Pj b) P-weightedEval y (Pj w) Q)-
        weightedEval y (Pj b) (formalPrimitive P) =
      Pj (N v-weightedEval y b (formalPrimitive P))-coefficient d i v • Pj (N d) := by
      rw [←ep,←ej,show N' (Pj v)=Pj (N v)-coefficient d i v • Pj (N d) from
        contracted_apply_remove N hi v]
      rw [show Pj (N v-weightedEval y b (formalPrimitive P))=
        Pj (N v)-Pj (weightedEval y b (formalPrimitive P)) from map_sub Pj _ _]
      abel
    have f : N' (weightedEval y (Pj b) P-weightedEval y (Pj w) Q)-
        weightedEval y (Pj b) (formalPrimitive P)∈Qsp (m+1) := by
      rw [e]
      exact (Qsp _).sub_mem (paid _ (m+1) (m+1) le_rfl (by omega) (by omega) a')
        ((Qsp _).smul_mem _ (paid _ 4 (m+1) (by omega) (by omega) (by omega) nd))
    have ar : m+1-3=m-2 := by omega
    simpa only [Qsp,ar] using f
  · intro m hm hm' P hp
    let v := weightedEval y b P
    have hR : commutatorR N C' v∈M (m+2) :=
      ⟨(ReverseTrace.scalar A b hp).commutator ho (by omega),
        prior_last_iff.mpr (physical_terminal_commutator_zero h.terminal v)⟩
    have h0 : Pj (commutatorR N C' v)∈Qsp (m+2) :=
      paid _ (m+2) (m+2) le_rfl (by omega) (by omega) hR
    have h1 : Pj (N d)∈Qsp (m+2) := paid _ 4 (m+2) (by omega) (by omega) (by omega) nd
    have h2 : Pj (C' (N d))∈Qsp (m+2) := paid _ 5 (m+2) (by omega) (by omega) (by omega) ynd
    have h3 : Pj (N (N d))∈Qsp (m+2) := paid _ 5 (m+2) (by omega) (by omega) (by omega) nnd
    have he : commutatorR N' C' (Pj v)-Pj (commutatorR N C' v)∈Qsp (m+2) := by
      change commutatorR (contracted N d i) (diag y) (remove d i v) -
        remove d i (commutatorR N (diag y) v) ∈ Qsp (m+2)
      rw [contracted_commutator_error N hi loc]
      exact (Qsp _).add_mem ((Qsp _).sub_mem ((Qsp _).smul_mem _ h1) ((Qsp _).smul_mem _ h2))
        ((Qsp _).smul_mem _ h3)
    have hv : commutatorR N' C' (Pj v)∈Qsp (m+2) := by
      have hh := (Qsp (m+2)).add_mem he h0
      simpa only [sub_add_cancel] using hh
    have ar : m+2-3=m-1 := by omega
    change commutatorR N' C' (weightedEval y (Pj b) P)∈chain C' ⊥ (Pj w) (m-1)
    rw [show weightedEval y (Pj b) P=Pj v from (remove_weighted loc b P).symm]
    simpa only [Qsp,ar] using hv

end RKCert.Paired
