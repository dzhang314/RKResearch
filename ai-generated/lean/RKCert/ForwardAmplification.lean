module

public import RKCert.NodeCompletion
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Two-node chronological amplification of an invariant defect space -/
namespace RKCert.Paired
open Polynomial
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
/-- A one-dimensional extension is obtained by adjoining any new vector. -/
theorem sup_singleton_eq_of_rank {V W : Submodule K (Vec K s)} {w : Vec K s}
    (hVW : V≤W) (hw : w∈W) (hout : w∉V) (h : finrank K W≤finrank K V+1) :
    W = V ⊔ Submodule.span K {w} := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le hVW ((Submodule.span_singleton_le_iff_mem ..).mpr hw)
  · rwa [Submodule.finrank_sup_span_singleton hout]

omit [CharZero K] in
/-- Invariance and polynomial separation force at least two different nonzero
represented nodes. This conclusion does not require an ambient basis. -/
theorem two_nonzero_completions {A : Fin s → Fin s → K} {j : ℕ}
    (hJ : 2≤j) (hsep : Separated A j)
    (hC : ∀ v ∈ zeroSpace A j, diag (nodes A) v ∈ zeroSpace A j) :
    ∃ u k l v k' l', u≠0 ∧ v≠0 ∧ u≠v ∧
      NodeCompletion A (zeroSpace A j) u k l ∧ NodeCompletion A (zeroSpace A j) v k' l' := by
  have hf (P : Polynomial K) (hp : P.natDegree≤j) (hP : P≠0) :
      ∃ x k l, P.eval x≠0 ∧ NodeCompletion A (zeroSpace A j) x k l := by
    by_contra! h
    apply hP
    apply hsep P hp
    apply row_annih_test
    intro w hw
    refine row_vanish_by_completions hC P (fun _ => True) hw (by simp) ?_
    intro x k l hc _
    by_contra hn
    exact h x k l hn hc
  obtain ⟨u,k,l,hu,hl⟩ := hf X (by simpa using (show 1≤j by omega)) X_ne_zero
  have hu' : u≠0 := by simpa using hu
  let P : Polynomial K := X * (X - C u)
  have hpd : P.natDegree≤j := (Polynomial.natDegree_mul_le_of_le (by simp)
    (Polynomial.natDegree_X_sub_C_le u)).trans hJ
  have hpn : P≠0 := mul_ne_zero X_ne_zero (Polynomial.X_sub_C_ne_zero u)
  obtain ⟨v,k',l',hPv,hl'⟩ := hf P hpd hpn
  refine ⟨u,k,l,v,k',l',hu',?_,?_,hl,hl'⟩
  · rintro rfl; exact hPv (by simp [P])
  · rintro rfl; exact hPv (by simp [P])

omit [CharZero K] in
/-- Select the first two chronologically distinguishable nonzero nodes.
Rows supported before the first see only 0; those before the second can
additionally see the first node. -/
theorem earliest_two_completions {A : Fin s → Fin s → K} {j : ℕ}
    (hJ : 2≤j) (hsep : Separated A j)
    (hC : ∀ v ∈ zeroSpace A j, diag (nodes A) v ∈ zeroSpace A j) :
    ∃ u k l v k' l', u≠0 ∧ v≠0 ∧ u≠v ∧ k < k' ∧
      NodeCompletion A (zeroSpace A j) u k l ∧ NodeCompletion A (zeroSpace A j) v k' l' ∧
      (∀ x i a, NodeCompletion A (zeroSpace A j) x i a → i < k → x=0) ∧
      (∀ x i a, NodeCompletion A (zeroSpace A j) x i a → i < k' → x=0 ∨ x=u) := by
  obtain ⟨x,i,w,y,i',w',hx,hy,hxy,hw,hw'⟩ := two_nonzero_completions hJ hsep hC
  let S : Set (Fin s) := {k | ∃ x l, x≠0 ∧ NodeCompletion A (zeroSpace A j) x k l}
  obtain ⟨k,⟨u,l,hu,hl⟩,hk⟩ := wellFounded_lt.has_min S ⟨i,x,w,hx,hw⟩
  let T : Set (Fin s) := {k | ∃ x l, x≠0 ∧ x≠u ∧ NodeCompletion A (zeroSpace A j) x k l}
  have hT : T.Nonempty := by
    by_cases hxu : x=u
    · exact ⟨i',y,w',hy,fun h => hxy (hxu.trans h.symm),hw'⟩
    · exact ⟨i,x,w,hx,hxu,hw⟩
  obtain ⟨k',⟨v,l',hv,hvu,hl'⟩,hk'⟩ := wellFounded_lt.has_min T hT
  have hne : k≠k' := by
    intro he; exact hvu (hl'.node_at_last.symm.trans (he ▸ hl.node_at_last))
  have hlt : k < k' := lt_of_le_of_ne (le_of_not_gt (hk k' ⟨v,l',hv,hl'⟩)) hne
  refine ⟨u,k,l,v,k',l',hu,hv,Ne.symm hvu,hlt,hl,hl',?_,?_⟩
  · intro x i a h hi
    by_contra he
    exact hk i ⟨x,a,he,h⟩ hi
  · intro x i a h hi
    by_cases h0 : x=0
    · exact Or.inl h0
    · right
      by_contra he
      exact hk' i ⟨x,a,h0,he,h⟩ hi

theorem evaluation_after_row_transport {A : Fin s → Fin s → K} {j : ℕ}
    {w : Vec K s} (hw : w∈annih (zeroSpace A (j+1)))
    (P : Polynomial K) (hP : P.natDegree≤j) :
    row (transMat A w) (evalNodes A P) = row w (evalNodes A (primitive P)) := by
  rw [row_flip_mat,← sub_eq_zero,← map_sub]
  exact mem_annih.mp hw _ (primitive_defect A P hP)

/-- A C-invariant F_j, j≥3, cannot have at most one new rank in F_{j+1}.
No order, positivity, compressed-basis or support-multiplicity assumption is
used; all nonzero nodes are selected by their actual first completion. -/
theorem invariant_forces_two_forward {A : Fin s → Fin s → K} {j : ℕ}
    (ha : StrictLower A) (hj : 3≤j) (hsep : Separated A j)
    (hC : ∀ v ∈ zeroSpace A j, diag (nodes A) v ∈ zeroSpace A j) :
    finrank K (zeroSpace A j)+2 ≤ finrank K (zeroSpace A (j+1)) := by
  by_contra! hdim
  let U := zeroSpace A j
  let V := zeroSpace A (j+1)
  have hUV : U≤V := zeroSpace_mono _ (by omega)
  have hline : ∃ w : Vec K s, V = U ⊔ Submodule.span K {w} := by
    by_cases h : U=V
    · exact ⟨0,by simp [h]⟩
    · have he : ∃ w ∈ V, w∉U := by
        by_contra! h'
        exact h (le_antisymm hUV h')
      obtain ⟨w,hw,hout⟩ := he
      exact ⟨w,sup_singleton_eq_of_rank hUV hw hout (by dsimp [U,V]; omega)⟩
  obtain ⟨w,hw⟩ := hline
  obtain ⟨u,k,l,v,k',l',hu,hv,huv,hkk,hl,hl',hfirst,hsecond⟩ :=
    earliest_two_completions (by omega) hsep hC
  let a := row l w
  let b := row l' w
  let beta := a • l' - b • l
  have hbeta : beta∈annih V := by
    rw [hw]
    apply mem_annih.mpr
    intro x hx
    obtain ⟨x,hxU,y,hy,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [beta,row_sub_col,row_smul_col,map_add,map_smul,smul_eq_mul,
      mem_annih.mp hl.annihilates _ hxU, mem_annih.mp hl'.annihilates _ hxU]
    dsimp [a,b]; ring
  have hvbeta : transMat A beta ∈ annih U := by
    apply mem_annih.mpr
    intro z hz
    rw [row_flip_mat]
    exact mem_annih.mp hbeta _ (mat_zeroSpace_charZero A j hz)
  have hlate : ∀ i, k' < i → beta i=0 := by
    intro i hi; simp [beta,hl.laterZero i (hkk.trans hi),hl'.laterZero i hi]
  have hpref : ∀ i, (transMat A beta) i≠0 → i < k' := by
    intro i hi
    by_contra! h
    exact hi (transMat_vanish ha k' beta hlate i h)
  let P : Polynomial K := X^2 * (X-C u)^2
  let G := derivative P
  have hdP : P.natDegree≤4 := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_pow_le_of_le 2 (show (X:Polynomial K).natDegree≤1 by simp))
    (Polynomial.natDegree_pow_le_of_le 2 (Polynomial.natDegree_X_sub_C_le u))
  have hdG : G.natDegree≤j := by
    have hd := Polynomial.natDegree_derivative_le P
    dsimp [G]; omega
  have hprimitive : primitive G = P := primitive_derivative _ (by
    rw [coeff_zero_eq_eval_zero]; simp [P])
  have hGx (x : K) : G.eval x = 2*x*(x-u)^2 + x^2 * (2*(x-u)) := by
    simp [G,P,Polynomial.derivative_mul,Polynomial.derivative_pow,Polynomial.derivative_sub,
      Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul]
  have hG0 : G.eval 0=0 := by rw [hGx]; ring
  have hGu : G.eval u=0 := by rw [hGx]; ring
  have hzero := row_vanish_by_completions hC G (fun i => i < k') hvbeta hpref
    (fun x i m hc hi => by
      rcases hsecond _ _ _ hc hi with rfl|rfl
      · exact hG0
      · exact hGu)
  rw [evaluation_after_row_transport hbeta G hdG,hprimitive] at hzero
  have hp0 : P.eval u=0 := by simp [P]
  have hpn : P.eval v≠0 := by
    simp only [P,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C]
    exact mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm huv)))
  simp only [beta,row_sub_col,row_smul_col,hl.eval P,hl'.eval P,hp0,mul_zero,sub_zero] at hzero
  have ha0 : row l w=0 := (mul_eq_zero.mp hzero).resolve_right hpn
  have hlV : l∈annih V := by
    rw [hw]
    apply mem_annih.mpr
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add,map_smul,mem_annih.mp hl.annihilates _ hy,ha0,smul_zero,add_zero]
  have hlA : transMat A l ∈ annih U := by
    apply mem_annih.mpr
    intro z hz
    rw [row_flip_mat]
    exact mem_annih.mp hlV _ (mat_zeroSpace_charZero A j hz)
  have hlpre : ∀ i, (transMat A l) i≠0 → i < k := by
    intro i hi
    by_contra! h
    exact hi (transMat_vanish ha k l hl.laterZero i h)
  have hc0 := row_vanish_by_completions hC X (fun i => i < k) hlA hlpre
    (fun x i a h hi => by simpa using hfirst _ _ _ h hi)
  rw [evaluation_after_row_transport hlV X (by simpa using (show 1≤j by omega)),
    hl.eval] at hc0
  have he : (X : Polynomial K) = monomial 1 1 := by
    simpa using (Polynomial.X_pow_eq_monomial (R:=K) 1)
  rw [he,primitive_monomial] at hc0
  simp only [Polynomial.eval_monomial] at hc0
  exact (mul_ne_zero (div_ne_zero one_ne_zero (by norm_num))
    (pow_ne_zero _ hu)) hc0

end RKCert.Paired
