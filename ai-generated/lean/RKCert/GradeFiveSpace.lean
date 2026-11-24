module

public import RKCert.ReceiverPrefix
public import RKCert.ForwardAmplification

@[expose] public section

/-! # The two possible minimal forward profiles at grade five -/
namespace RKCert.Paired
open Polynomial
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- The ordinary quadratic primitive defect. -/
noncomputable def qdef (A : Fin s → Fin s → K) : Vec K s :=
  mat A (nodes A) - ((2:K)⁻¹ : K) • (nodes A)^2

theorem qdef_mem (A : Fin s → Fin s → K) : qdef A ∈ zeroSpace A 2 := by
  have hm := primitive_defect A (monomial 1 (1:K))
    (by exact Polynomial.natDegree_monomial_le _)
  have e0 : evalNodes A (monomial 1 (1:K)) = nodes A := by ext i; simp
  have e1 : evalNodes A (primitive (monomial 1 (1:K))) =
      ((2:K)⁻¹ : K) • (nodes A)^2 := by
    ext i
    rw [primitive_monomial,evalNodes_apply,eval_monomial]
    simp
  simpa [e0,e1,qdef] using hm

theorem qdef_seed (A : Fin s → Fin s → K) :
    (2:K) • qdef A = (2:K) • mat A (diag (nodes A) 1) -
      diag (nodes A) (diag (nodes A) 1) := by
  ext i
  have h : diag (nodes A) (1 : Vec K s) = nodes A := by ext j; simp
  rw [h]
  simp only [qdef,Pi.smul_apply,Pi.sub_apply,Pi.pow_apply,smul_eq_mul,diag_apply]
  rw [mul_sub,← mul_assoc,mul_inv_cancel₀ (by norm_num : (2:K)≠0),one_mul]
  ring

theorem qdef_ne_zero {A : Fin s → Fin s → K} (ha : StrictLower A)
    (hsep : Separated A 5) : qdef A ≠ 0 := by
  intro hq
  apply nodes_not_zeroSpace hsep (by decide)
  have h1 : diag (nodes A) (1 : Vec K s) = nodes A := by ext i; simp
  have hz : diag (nodes A) (1 : Vec K s) ∈ (⊥ : Submodule K (Vec K s)) := by
    apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 ⊥
    · intro v hv; rw [(Submodule.mem_bot K).mp hv,map_zero]; simp
    · intro v hv; rw [(Submodule.mem_bot K).mp hv,map_zero]; simp
    · rw [← qdef_seed,hq,smul_zero]; simp
  rw [h1,Submodule.mem_bot] at hz
  rw [hz]; exact (zeroSpace A 5).zero_mem

theorem minimal_five_ranks {A : Fin s → Fin s → K} (ha : StrictLower A)
    (hsep : Separated A 5) (hr : finrank K (zeroSpace A 5) ≤ 4) :
    zeroSpace A 2 = Submodule.span K {qdef A} ∧
    finrank K (zeroSpace A 2)=1 ∧ finrank K (zeroSpace A 3)=2 ∧
    finrank K (zeroSpace A 4)=3 ∧ finrank K (zeroSpace A 5)=4 := by
  have h1 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha hsep (j:=1) (by decide) (by decide))
  have h2 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha hsep (j:=2) (by decide) (by decide))
  have h3 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha hsep (j:=3) (by decide) (by decide))
  have h4 := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha hsep (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 1) < finrank K (zeroSpace A 2) at h1
  change finrank K (zeroSpace A 2) < finrank K (zeroSpace A 3) at h2
  change finrank K (zeroSpace A 3) < finrank K (zeroSpace A 4) at h3
  change finrank K (zeroSpace A 4) < finrank K (zeroSpace A 5) at h4
  have hF2 : finrank K (zeroSpace A 2)=1 := by omega
  refine ⟨?_,hF2,by omega,by omega,by omega⟩
  symm
  apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr (qdef_mem A))
  rw [finrank_span_singleton (qdef_ne_zero ha hsep),hF2]

def signal (A : Fin s → Fin s → K) (d : Vec K s) (k : ℕ) : Vec K s :=
  fun i => d i * nodes A i ^ k

omit [CharZero K] in
theorem signal_zero (A : Fin s → Fin s → K) (d : Vec K s) : signal A d 0=d := by
  ext i; simp [signal]

omit [CharZero K] in
theorem signal_step (A : Fin s → Fin s → K) (d : Vec K s) (k : ℕ) :
    diag (nodes A) (signal A d k) = signal A d (k+1) := by
  ext i; simp [signal,pow_succ']; ring

def chainSpan (A : Fin s → Fin s → K) (d : Vec K s) (q : ℕ) : Submodule K (Vec K s) :=
  Submodule.span K (Set.range fun i : Fin (q+1) => signal A d i.val)

omit [CharZero K] in
theorem signal_mem_chainSpan (A : Fin s → Fin s → K) (d : Vec K s) {j q : ℕ}
    (h : j≤q) : signal A d j∈chainSpan A d q := Submodule.subset_span ⟨⟨j,by omega⟩,rfl⟩

omit [CharZero K] in
theorem chainSpan_zero (A : Fin s → Fin s → K) (d : Vec K s) :
    chainSpan A d 0=Submodule.span K {d} := by
  unfold chainSpan
  congr 1
  ext v
  simp [signal_zero]

omit [CharZero K] in
theorem chainSpan_succ (A : Fin s → Fin s → K) (d : Vec K s) (q : ℕ) :
    chainSpan A d (q+1) = chainSpan A d q ⊔ Submodule.span K {signal A d (q+1)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change signal A d i.val ∈ chainSpan A d q ⊔ Submodule.span K {signal A d (q+1)}
    by_cases hi : i.val≤q
    · exact (show chainSpan A d q ≤ _ from le_sup_left) (signal_mem_chainSpan A d hi)
    · have he : i.val=q+1 := by have := i.isLt; omega
      rw [he]
      exact (show Submodule.span K {signal A d (q+1)} ≤ _ from le_sup_right)
        (Submodule.mem_span_singleton_self _)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact signal_mem_chainSpan A d (by omega)
    · exact (Submodule.span_singleton_le_iff_mem ..).mpr (signal_mem_chainSpan A d le_rfl)

omit [CharZero K] in
theorem chainSpan_diag_stable {A : Fin s → Fin s → K} {d : Vec K s} {q : ℕ}
    {U : Submodule K (Vec K s)} (hu : chainSpan A d q ≤ U)
    (h : signal A d (q+1)∈U) :
    chainSpan A d q ≤ U.comap (diag (nodes A)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change diag (nodes A) (signal A d i.val)∈U
  rw [signal_step]
  by_cases hi : i.val+1≤q
  · exact hu (signal_mem_chainSpan A d hi)
  · rwa [show i.val+1=q+1 by have := i.isLt; omega]

omit [CharZero K] in
/-- A pure chain is a polynomial multiple of its head, with the exact degree cap. -/
theorem chainSpan_iff_polynomial {A : Fin s → Fin s → K} {d v : Vec K s} {q : ℕ} :
    v∈chainSpan A d q ↔ ∃ P : Polynomial K, P.natDegree≤q ∧ v=diag d (evalNodes A P) := by
  classical
  have hh (a : Fin (q+1) → K) :
      (∑ i : Fin (q+1), a i • signal A d i.val) = diag d (polyEval A q a) := by
    rw [polyEval_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    ext j; simp [signal,normTree_bush]
  constructor
  · intro hv
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    refine ⟨Polynomial.ofFn (q+1) a,?_,?_⟩
    · have := Polynomial.ofFn_natDegree_lt (by omega : 1≤q+1) a; omega
    · rw [evalNodes_ofFn,← hh,ha]
  · rintro ⟨P,hP,rfl⟩
    rw [evalNodes_eq_polyEval A P hP,← hh]
    exact (chainSpan A d q).sum_mem (fun i _ => (chainSpan A d q).smul_mem _
      (signal_mem_chainSpan A d (by omega)))

omit [CharZero K] in
/-- Push forward a strictly explicit tableau to its distinct chronological
evaluation rows, preserving separation and not increasing defect rank. -/
theorem exists_compressed_separated {A : Fin s → Fin s → K} {q : ℕ}
    (ha : StrictLower A) (hsep : Separated A q) :
    ∃ (n : ℕ) (B : Fin n → Fin n → K), StrictLower B ∧ Separated B q ∧
      finrank K (zeroSpace B q)≤finrank K (zeroSpace A q) ∧
      (∀ i j : Fin n, i<j → ∃ t : Tree, t.order≤q+1 ∧ stageWeight B t i≠stageWeight B t j) := by
  obtain ⟨n,e,w,hw,hR,hP⟩ := exists_causal_coord_family (treeSpace A q)
  let B := compressMat A e w
  have hmat : ∀ v∈treeSpace A q, mat B (restrictCol e v)=restrictCol e (mat A v) :=
    fun v hv => compress_mat_comm A e w hR v hv
  have hF := restrict_zeroSpace A B e (by omega : q≤q+1) hmat
  refine ⟨n,B,compress_strict ha e w hw,?_,?_,fun i j hij =>
    compressed_rows_distinct A B e q hmat hP hij⟩
  · apply (separated_iff_coeff B q).mpr
    intro a ha
    rw [← restrict_polyEval A B e q hmat,← hF] at ha
    obtain ⟨v,hv,he⟩ := ha
    have hEq := restrictCol_inj_on hR (zeroSpace_le_treeSpace _ _ hv) (polyEval_mem_treeSpace _ _ _) he
    subst v
    exact (separated_iff_coeff A q).mp hsep a hv
  · rw [← hF]
    exact Submodule.finrank_map_le (restrictCol e) _

/-- Minimal ranks and amplification identify all grades for the two cases. -/
theorem minimal_five_chain_case {A : Fin s → Fin s → K} (ha : StrictLower A)
    (hsep : Separated A 5) (hR : finrank K (zeroSpace A 5)≤4)
    (hind : signal A (qdef A) 1 ∉ Submodule.span K {qdef A}) :
    zeroSpace A 4 = chainSpan A (qdef A) 2 ∧
    zeroSpace A 5 = chainSpan A (qdef A) 3 := by
  obtain ⟨h2,r2,r3,r4,r5⟩ := minimal_five_ranks ha hsep hR
  let d := qdef A
  have hd : signal A d 1∈zeroSpace A 3 := by
    rw [← signal_step A d 0,signal_zero]
    exact diag_zeroSpace A 2 (qdef_mem A)
  have h3 : zeroSpace A 3 = chainSpan A d 1 := by
    rw [chainSpan_succ,chainSpan_zero,← h2]
    exact sup_singleton_eq_of_rank (zeroSpace_mono _ (by decide)) hd
      (by rw [h2]; exact hind) (by omega)
  have adv {j k : ℕ} (hj : 3≤j) (h5 : j≤5) (hE : zeroSpace A j=chainSpan A d k)
      (hrk : finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1) :
      zeroSpace A (j+1)=chainSpan A d (k+1) := by
    have hv : signal A d (k+1)∈zeroSpace A (j+1) := by
      rw [← signal_step]
      exact diag_zeroSpace A j (hE.symm ▸ signal_mem_chainSpan A d (le_refl k))
    have hnot : signal A d (k+1)∉zeroSpace A j := by
      intro hx
      have hC := chainSpan_diag_stable (hE ▸ le_rfl) hx
      have hd := invariant_forces_two_forward ha hj (hsep.mono h5) (fun v hv =>
        hC (hE ▸ hv))
      omega
    rw [chainSpan_succ,← hE]
    exact sup_singleton_eq_of_rank (zeroSpace_mono _ (by omega)) hv hnot hrk
  have h4 := adv (by decide) (by decide) h3 (by
    change finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1; omega)
  exact ⟨h4,adv (by decide) (by decide) h4 (by
    change finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1; omega)⟩

end RKCert.Paired
