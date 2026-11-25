module

public import RKCert.ReviewedNative.OptionalTerminalMark
public import RKCert.ReviewedNative.ClockHeadSupport

import RKCert.ReviewedNative.OddForwardBudget
import Mathlib.Algebra.Polynomial.OfFn
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Native first escape and pure paid head at width 19

The record retains only the original marked subspace, separation,
decomposition and ranks. No polynomial family, scalar mesh decoder,
or ghost route is part of this type or its construction.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}

/-- The first actual clock escape, with the optional terminal line. -/
abbrev escape (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K) :
    Submodule K (Fin 19 → K) :=
  (zeroSpace A 6 ⊔ (zeroSpace A 6).map (diag (nodes A))) ⊔ terminalMark A b

theorem escape_paid (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K) :
    escape A b ≤ markedDefectSpace A b 7 :=
  sup_le_sup (sup_le (zeroSpace_mono A (by decide : 6≤7))
    (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6))) le_rfl

/-- The exact rank entries consumed by the first-escape split. -/
structure PaidRankInput (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K) : Prop where
  lastActive : LastActive b (Fin.last 18)
  rankMid : finrank K (markedTreeSpace A b 6) = 13 + terminalDebit A b
  defectRank : finrank K (markedDefectSpace A b 6) = 6 + terminalDebit A b
  escapeRank : finrank K (escape A b) = 7 + terminalDebit A b
  upperSeven : finrank K (markedTreeSpace A b 7) ≤ 14 + terminalDebit A b

structure FirstEscape (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K)
    (a : ℕ) (G : K[X]) : Prop where
  width : a = 6 ∨ (a = 5 ∧ firstSeed A b = 0)
  degree : G.natDegree = a + 1
  paid : evalNodes A G ∈ escape A b
  lowSeparation : ∀ P : K[X], P.natDegree ≤ a → evalNodes A P ∈ escape A b → P = 0
  decomposition : markedTreeSpace A b (a+1) = (coeffEval A a).range ⊔ escape A b
  rank : finrank K (markedTreeSpace A b (a+1)) = a+8+terminalDebit A b

private theorem eval_ofFn (A : Matrix (Fin 19) (Fin 19) K) (q : ℕ) (v : Fin (q+1) → K) :
    evalNodes A (ofFn (q+1) v) = coeffEval A q v := by
  rw [evalNodes_eq_coeffEval A _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) v))]
  congr 1
  ext i
  exact ofFn_coeff_eq_val_of_lt _ i.isLt

private theorem band_in_tree {a j : ℕ} (h : a≤j) :
    (coeffEval A a).range ≤ markedTreeSpace A b j := by
  rintro _ ⟨t,rfl⟩
  exact (show treeSpace A j≤markedTreeSpace A b j from le_sup_left)
    (treeSpace_mono A h (coeffEval_mem_treeSpace A a t))

private theorem coeff_of_poly_sep {a : ℕ} {W : Submodule K (Fin 19 → K)}
    (sep : ∀ P : K[X], P.natDegree≤a → evalNodes A P∈W → P=0)
    (y : Fin (a+1) → K) (hy : coeffEval A a y∈W) : y=0 := by
  apply injective_ofFn (a+1)
  rw [ofFn_zero]
  exact sep (ofFn (a+1) y) (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) y))
    (by rwa [eval_ofFn])

/-- A degree-six first escape needs the physical terminal mark. The proof
uses the ordinary next-grade Cauchy separation, not a scalar shape decoder. -/
theorem firstEscape_of_paid_rank (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 13 A b) (F : PaidRankInput A b) :
    ∃ a G, FirstEscape A b a G := by
  let W := escape A b
  have wR : finrank K W = 7+terminalDebit A b := F.escapeRank
  have ePay : W ≤ markedDefectSpace A b 7 := escape_paid A b
  have s5 (x : Fin 6 → K) (hx : coeffEval A 5 x∈W) : x=0 :=
    marked_coeff_separated (q:=5) (j:=7) ha ho F.lastActive
      (by decide) (by decide) (by decide) x (ePay hx)
  have low5 := eval_eq_zero_of_coeff_separated (V:=W) s5
  by_cases aliasOne : ∃ G : K[X], G.natDegree≤6 ∧ evalNodes A G∈W ∧ G≠0
  · obtain ⟨G,gd,gW,gn⟩ := aliasOne
    have dG : G.natDegree=6 := by
      by_contra nd
      exact gn (low5 G (by omega) gW)
    have seed : firstSeed A b=0 := by
      by_contra nz
      have op : evalNodes A G∈zeroSpace A 7 := by
        simpa only [markedDefectSpace,terminalMark,if_neg nz,sup_bot_eq] using ePay gW
      exact gn (eval_eq_zero_of_coeff_separated
        (coeff_separated_next (q:=6) ha ho (by decide)) G gd op)
    let D := markedDefectSpace A b 6
    have nD : evalNodes A G∉D := by
      intro hd
      exact gn (eval_eq_zero_of_coeff_separated
        (marked_coeff_separated (q:=6) (j:=6) ha ho F.lastActive
          (by decide) (by decide) (by decide)) G gd hd)
    have edge : W = D ⊔ Submodule.span K {evalNodes A G} := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le (sup_le_sup le_sup_left le_rfl)
          ((Submodule.span_singleton_le_iff_mem ..).mpr gW)
      · rw [Submodule.finrank_sup_span_singleton nD,wR]
        change _ ≤ finrank K (markedDefectSpace A b 6)+1
        rw [F.defectRank]
        omega
    have hW : W≤markedTreeSpace A b 6 := by
      rw [edge]
      refine sup_le (sup_le_sup (zeroSpace_le_treeSpace A 6) le_rfl)
        ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
      exact (show treeSpace A 6≤markedTreeSpace A b 6 from le_sup_left)
        (evalNodes_mem_treeSpace A G gd)
    have inc := sup_le (band_in_tree (A:=A) (b:=b) (a:=5) (j:=6) (by decide)) hW
    have rank := rank_coeff_sup_of_separated W s5
    have eq := (Submodule.eq_of_le_of_finrank_le inc (by rw [F.rankMid,rank,wR]; omega)).symm
    exact ⟨5,G,⟨Or.inr ⟨rfl,seed⟩,dG,gW,low5,eq,F.rankMid⟩⟩
  · have none (P : K[X]) (pd : P.natDegree≤6) (e : evalNodes A P∈W) : P=0 := by
      by_contra nz
      exact aliasOne ⟨P,pd,e,nz⟩
    have sep := coeff_of_poly_sep none
    have inc : (coeffEval A 6).range ⊔ W ≤ markedTreeSpace A b 7 :=
      sup_le (band_in_tree (by decide))
        (ePay.trans (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl))
    have r := rank_coeff_sup_of_separated W sep
    have low : finrank K ((coeffEval A 6).range⊔W : Submodule K (Fin 19→K)) =
        14+terminalDebit A b := by rw [r,wR]; omega
    have eq := (Submodule.eq_of_le_of_finrank_le inc (F.upperSeven.trans_eq low.symm)).symm
    have rank : finrank K (markedTreeSpace A b 7)=14+terminalDebit A b := by rw [eq,low]
    have mem : evalNodes A (X^7 : K[X])∈(coeffEval A 6).range⊔W := eq ▸
      (show treeSpace A 7≤markedTreeSpace A b 7 from le_sup_left)
        (evalNodes_mem_treeSpace A _ (by simp))
    obtain ⟨_,⟨x,rfl⟩,v,hv,hEq⟩ := Submodule.mem_sup.mp mem
    let P := ofFn 7 x
    have pd : P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) x)
    let G : K[X] := X^7-P
    have dG : G.natDegree=7 := by
      rw [show G=X^7-P from rfl,natDegree_sub_eq_left_of_natDegree_lt,natDegree_X_pow]
      simpa only [natDegree_X_pow] using Nat.lt_succ_of_le pd
    have gW : evalNodes A G∈W := by
      change evalNodes A (X^7-P)∈W
      rw [map_sub,show evalNodes A P=coeffEval A 6 x from eval_ofFn A 6 x,
        ←hEq,add_sub_cancel_left]
      exact hv
    exact ⟨6,G,⟨Or.inl rfl,dG,gW,none,eq,rank⟩⟩

/-- The literal factor in the pure head branch. Only the actual paid
square and two physical band lengths are used. The head-site count is
about distinct clocks of original nonzero head rows. -/
theorem pure_quartic_factor {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {G : K[X]}
    (gd : G.natDegree = 7)
    (sites : 8 ≤ (HeadFiber.physicalSites (nodes A) w).card)
    (off : ∀ i, (∃ u∈U, u i≠0) → w i=0)
    (square : w*w ∈ chain (diag (nodes A)) U w 5)
    (mesh : evalNodes A G ∈ chain (diag (nodes A)) U w 4) :
    ∃ P Q : K[X], P.natDegree=4 ∧ Q.natDegree=3 ∧ G=P*Q ∧
      ∀ i, w i≠0 → w i=P.eval (nodes A i) := by
  classical
  let S := HeadFiber.physicalSites (nodes A) w
  have s8 : 8≤S.card := sites
  obtain ⟨P,cap,repr⟩ := HeadFiber.multiplier_polynomial
    (n:=5) (a:=w) (d:=0) off (by omega : 5<S.card)
    (fun k hk => by
      have z : k=0 := by omega
      rw [z,pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
      exact square)
  have stage (x : K) (hx : x∈S) : ∃ i : Fin 19, w i≠0 ∧ nodes A i=x := by
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp hx
    exact ⟨i,(Finset.mem_filter.mp hi).2,eq⟩
  have pn : P≠0 := by
    intro pz
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<S.card by omega)
    obtain ⟨i,hi,_⟩ := stage x hx
    exact hi (by rw [repr i hi,pz,eval_zero])
  have pd : P.natDegree≤4 := by have h := cap.resolve_left pn; omega
  obtain ⟨u,hu,Q,degQ,expr⟩ := HeadFiber.exists_poly mesh
  have qd : Q.natDegree≤3 := by
    by_cases z : Q=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr degQ)
  have fit : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq S
    · apply degree_le_natDegree.trans_lt
      rw [gd]
      exact_mod_cast (show 7<S.card by omega)
    · apply degree_le_natDegree.trans_lt
      have pay := natDegree_mul_le (p:=P) (q:=Q)
      exact_mod_cast (show (P*Q).natDegree<S.card by omega)
    · intro x hx
      obtain ⟨i,wi,rfl⟩ := stage x hx
      have ui : u i=0 := by
        by_contra nz
        exact wi (off i ⟨u,hu,nz⟩)
      have e := congrFun expr i
      rw [evalNodes_apply,Pi.add_apply,weightedEval_apply,ui,zero_add,repr i wi] at e
      simpa only [eval_mul,mul_comm] using e
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have qn : Q≠0 := fun z => gn (by rw [fit,z,mul_zero])
  have sum := congrArg natDegree fit
  rw [natDegree_mul pn qn,gd] at sum
  exact ⟨P,Q,by omega,by omega,fit,repr⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
