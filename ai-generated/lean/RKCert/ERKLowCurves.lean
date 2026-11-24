module

public import RKCert.ERKLowSaturation

@[expose] public section

/-! # The low-order two-curve chart of actual explicit stage weights -/
namespace RKCert.Paired
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- The nonzero part of a stage column, projected to its distinct nodes. -/
noncomputable def supportedNodes (A : Fin s → Fin s → K) (d : Vec K s) : Finset K :=
  (Finset.univ.filter fun i => d i≠0).image (nodes A)

omit [CharZero K] in
theorem mem_supportedNodes {A : Fin s → Fin s → K} {d : Vec K s} {x : K} :
    x∈supportedNodes A d ↔ ∃ i : Fin s, d i≠0 ∧ nodes A i=x := by
  simp [supportedNodes,Finset.mem_image,Finset.mem_filter]

omit [CharZero K] in
/-- Three distinct supported knots give three linearly independent clock
columns, with no assumption of distinctness of the physical rows. -/
theorem chainSpan_rank_on_supportedNodes (A : Fin s → Fin s → K) (d : Vec K s) (q : ℕ)
    (hn : q+1 ≤ (supportedNodes A d).card) :
    finrank K (chainSpan A d q)=q+1 := by
  have hli : LinearIndependent K (fun i : Fin (q+1) => signal A d i.val) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    let P := Polynomial.ofFn (q+1) a
    have hp : P.natDegree ≤ q := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) a)
    have he : diag d (evalNodes A P) = 0 := by
      rw [evalNodes_ofFn,polyEval_apply,map_sum,← ha]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      congr 1
      ext j; simp [normTree_bush,signal]
    have hroot (x : K) (hx : x∈supportedNodes A d) : P.eval x=0 := by
      obtain ⟨i,hi,rfl⟩ := mem_supportedNodes.mp hx
      have h := congrFun he i
      change d i * P.eval (nodes A i)=0 at h
      exact (mul_eq_zero.mp h).resolve_left hi
    have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P _ hroot (by omega)
    have ha0 : a=0 := Polynomial.injective_ofFn (q+1) (hz.trans (Polynomial.ofFn_zero _).symm)
    intro i; exact congrFun ha0 i
  unfold chainSpan
  rw [finrank_span_eq_card hli,Fintype.card_fin]

omit [CharZero K] in
theorem chainSpan_le_zeroSpace {A : Fin s → Fin s → K} {d : Vec K s} {r : ℕ}
    (h : d∈zeroSpace A r) (q : ℕ) :
    chainSpan A d q ≤ zeroSpace A (r+q) := by
  have hstep (j : ℕ) : signal A d j∈zeroSpace A (r+j) := by
    induction j with
    | zero => simpa only [signal_zero,Nat.add_zero] using h
    | succ j ih =>
      rw [← signal_step]
      exact diag_zeroSpace A (r+j) ih
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact zeroSpace_mono _ (by have := i.isLt; omega) (hstep i.val)

/-- There cannot be exactly two distinct quadratic-defect abscissas in
the saturated grade-three/grade-four chart. -/
theorem no_two_off_nodes {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hsep : Separated A 3)
    (h3 : finrank K (zeroSpace A 3)=2) (h4 : finrank K (zeroSpace A 4)=3) :
    (supportedNodes A (qdef A)).card≠2 := by
  intro hcard
  let d := qdef A
  change (supportedNodes A d).card = 2 at hcard
  have hR := chainSpan_rank_on_supportedNodes A d 1 (by omega)
  have he : chainSpan A d 1 = zeroSpace A 3 := Submodule.eq_of_le_of_finrank_le
    (chainSpan_le_zeroSpace (qdef_mem A) 1) (by simp [hR,h3])
  obtain ⟨u,v,_,hT⟩ := Finset.card_eq_two.mp hcard
  have hD : signal A d 2 = (u+v) • signal A d 1 - (u*v) • signal A d 0 := by
    ext i
    simp only [signal,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pow_zero,pow_one,mul_one]
    by_cases hi : d i=0
    · simp [hi]
    · have hn : nodes A i∈supportedNodes A d := mem_supportedNodes.mpr ⟨i,hi,rfl⟩
      change supportedNodes A d = {u,v} at hT
      rw [hT] at hn
      rcases (by simpa using hn : nodes A i=u ∨ nodes A i=v) with h|h <;> rw [h] <;> ring
  have hmem : signal A d 2∈chainSpan A d 1 := by
    rw [hD]
    exact (chainSpan A d 1).sub_mem ((chainSpan A d 1).smul_mem _ (signal_mem_chainSpan A d le_rfl))
      ((chainSpan A d 1).smul_mem _ (signal_mem_chainSpan A d (by decide : 0 ≤ 1)))
  have hf := chainSpan_diag_stable (U:=chainSpan A d 1) le_rfl hmem
  have hi := invariant_forces_two_forward ha (j:=3) (by decide) hsep (fun w hw => by
    rw [← he] at hw ⊢
    exact hf hw)
  change finrank K (zeroSpace A 3)+2 ≤ finrank K (zeroSpace A 4) at hi
  omega

/-- With three or more off nodes the lower actual tree spaces force the
same quadratic defect at every physical occurrence of a given off node. -/
theorem two_curve_head {A : Fin s → Fin s → K}
    (h3 : finrank K (zeroSpace A 3)=2) (h4 : finrank K (zeroSpace A 4)=3)
    (hc : 3 ≤ (supportedNodes A (qdef A)).card) :
    ∃ P : Polynomial K, P.natDegree ≤ 2 ∧ P≠0 ∧
      zeroSpace A 3=chainSpan A (qdef A) 1 ∧ zeroSpace A 4=chainSpan A (qdef A) 2 ∧
      (∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) := by
  let d := qdef A
  change 3 ≤ (supportedNodes A d).card at hc
  have hR1 := chainSpan_rank_on_supportedNodes A d 1 (by omega)
  have hR2 := chainSpan_rank_on_supportedNodes A d 2 hc
  have he3 : chainSpan A d 1=zeroSpace A 3 := Submodule.eq_of_le_of_finrank_le
    (chainSpan_le_zeroSpace (qdef_mem A) 1) (by simp [h3,hR1])
  have he4 : chainSpan A d 2=zeroSpace A 4 := Submodule.eq_of_le_of_finrank_le
    (chainSpan_le_zeroSpace (qdef_mem A) 2) (by simp [h4,hR2])
  have hsq : d*d∈zeroSpace A 4 := zeroSpace_mul (A:=A) (m:=2) (n:=2) (v:=d) (w:=d) (qdef_mem A) (qdef_mem A)
  rw [← he4,chainSpan_iff_polynomial] at hsq
  obtain ⟨P,hP,hEq⟩ := hsq
  have he (i) (hi : d i≠0) : P.eval (nodes A i)=d i := by
    have h := congrFun hEq i
    change d i*d i=d i*P.eval (nodes A i) at h
    exact (mul_left_cancel₀ hi h).symm
  refine ⟨P,hP,?_,he3.symm,he4.symm,he⟩
  intro h0
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (supportedNodes A d).card)
  obtain ⟨i,hi,_⟩ := mem_supportedNodes.mp hx
  exact hi (by simpa [h0] using (he i hi).symm)

/-- At a clean physical row in the two-curve chart, all fourth-grade
primitive tests and the two necessary defect-direction tests are exact. -/
theorem on_row_quartic_conditions {A : Fin s → Fin s → K} {i : Fin s}
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2) (hi : qdef A i=0) :
    (∀ k : ℕ, k ≤ 3 → mat A (fun j => nodes A j^k) i = nodes A i^(k+1) / ((k+1:ℕ):K)) ∧
      mat A (qdef A) i=0 ∧ mat A (diag (nodes A) (qdef A)) i=0 := by
  have hvan (v : Vec K s) (hv : v∈zeroSpace A 4) : v i=0 := by
    rw [hF,chainSpan_iff_polynomial] at hv
    obtain ⟨P,_,rfl⟩ := hv
    simp [hi]
  have hl : mat A (qdef A)∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 (qdef_mem A)
  have hr : mat A (diag (nodes A) (qdef A))∈zeroSpace A 4 :=
    mat_zeroSpace_charZero A 3 (diag_zeroSpace A 2 (qdef_mem A))
  refine ⟨?_,hvan _ (zeroSpace_mono A (by decide) hl),hvan _ hr⟩
  intro k hk
  have h := hvan _ (zeroSpace_mono A (by omega : k+1 ≤ 4) (primitive_mem_zeroSpace A k))
  change ((k+1:ℕ):K)*(mat A (fun j => nodes A j^k)) i - nodes A i^(k+1)=0 at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (by omega))).mpr
  rw [mul_comm]
  exact sub_eq_zero.mp h

end RKCert.Paired
