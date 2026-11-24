module

public import RKCert.GradeFiveSpace
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Preparation of the dependent-quadratic grade-five profile -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
theorem mat_first_of_strict {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A)
    (v : Vec K (s+5)) : mat A v 0 = 0 := by
  rw [mat_apply]
  exact Finset.sum_eq_zero (fun j _ => by rw [ha _ _ (Nat.zero_le _),zero_mul])

omit [CharZero K] in
theorem mat_second_of_strict {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A)
    (v : Vec K (s+5)) : mat A v 1 = A 1 0 * v 0 := by
  have h : 1≤s+5 := by omega
  rw [mat_apply]
  symm
  have he := sum_on_prefix h (fun j => A 1 j*v j)
    (fun j hj => by rw [ha _ _ hj,zero_mul])
  rw [Fin.sum_univ_succ] at he
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero] at he
  exact he

omit [CharZero K] in
theorem nodes_first_of_strict {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A) :
    nodes A 0=0 := by
  simpa [nodes] using mat_first_of_strict ha (1 : Vec K (s+5))

omit [CharZero K] in
theorem nodes_second_of_strict {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A) :
    nodes A 1=A 1 0 := by
  simpa [nodes] using mat_second_of_strict ha (1 : Vec K (s+5))

omit [CharZero K] in
theorem distinct_second_node {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A)
    (hrows : ∀ i j, i < j → ∃ t : Tree, t.order≤6 ∧ stageWeight A t i≠stageWeight A t j) :
    nodes A 1≠0 := by
  intro h
  have hrow : A 1 0=0 := (nodes_second_of_strict ha).symm.trans h
  obtain ⟨t,_,ht⟩ := hrows 0 1 (by change (0:ℕ)<1; decide)
  apply ht
  cases t with
  | leaf => rfl
  | attach c r =>
    change mat A (stageWeight A c) 0 * stageWeight A r 0 =
      mat A (stageWeight A c) 1 * stageWeight A r 1
    rw [mat_first_of_strict ha,mat_second_of_strict ha,hrow,zero_mul,zero_mul,zero_mul]

omit [CharZero K] in
theorem no_repeat_scale {A : Fin s → Fin s → K} {r : K} (hr : r≠0)
    (hrows : ∀ i j, i < j → ∃ t : Tree,t.order≤6 ∧ stageWeight A t i≠stageWeight A t j) :
    ∀ i j, i < j → ∃ t : Tree,t.order≤6 ∧
      stageWeight (scaleTableau r A) t i≠stageWeight (scaleTableau r A) t j := by
  intro i j hij
  obtain ⟨t,ht,hne⟩ := hrows i j hij
  refine ⟨t,ht,?_⟩
  intro he
  rw [stageWeight_scale,Pi.smul_apply,Pi.smul_apply] at he
  exact hne (mul_left_cancel₀ (pow_ne_zero _ hr) he)

omit [CharZero K] in
theorem qdef_second_normalized {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A)
    (hc : nodes A 1=1) : qdef A 1 = -((2:K)⁻¹ : K) := by
  rw [qdef,Pi.sub_apply,mat_second_of_strict ha,nodes_first_of_strict ha,mul_zero,
    Pi.smul_apply,Pi.pow_apply,smul_eq_mul,hc,one_pow,mul_one,zero_sub]

def mixedSpan (A : Fin s → Fin s → K) (d w : Vec K s) (q : ℕ) :
    Submodule K (Vec K s) := Submodule.span K {d} ⊔ chainSpan A w q

omit [CharZero K] in
theorem mixedSpan_succ (A : Fin s → Fin s → K) (d w : Vec K s) (q : ℕ) :
    mixedSpan A d w (q+1)=mixedSpan A d w q ⊔ Submodule.span K {signal A w (q+1)} := by
  simp only [mixedSpan,chainSpan_succ,sup_assoc]

omit [CharZero K] in
theorem mixedSpan_diag_stable {A : Fin s → Fin s → K} {d w : Vec K s} {q : ℕ}
    (hd : diag (nodes A) d=d) (hw : signal A w (q+1)∈mixedSpan A d w q) :
    mixedSpan A d w q ≤ (mixedSpan A d w q).comap (diag (nodes A)) := by
  apply sup_le
  · apply (Submodule.span_singleton_le_iff_mem ..).mpr
    change diag (nodes A) d∈mixedSpan A d w q
    rw [hd]
    exact (show Submodule.span K {d}≤mixedSpan A d w q from le_sup_left) (Submodule.mem_span_singleton_self _)
  · exact chainSpan_diag_stable (show chainSpan A w q≤mixedSpan A d w q from le_sup_right) hw

/-- Under quadratic dependence and normalization the actual rank pattern
identifies F3, F4, F5 and every nonzero quadratic head entry. -/
theorem normalized_minimal_five_dependent {A : Fin (s+5) → Fin (s+5) → K} (ha : StrictLower A)
    (hsep : Separated A 5) (hR : finrank K (zeroSpace A 5)≤4)
    (h1 : nodes A 1=1) (hdep : signal A (qdef A) 1 ∈ Submodule.span K {qdef A}) :
    (zeroSpace A 3 = mixedSpan A (qdef A) (mat A (qdef A)) 0) ∧
    (zeroSpace A 4 = mixedSpan A (qdef A) (mat A (qdef A)) 1) ∧
    (zeroSpace A 5 = mixedSpan A (qdef A) (mat A (qdef A)) 2) ∧
    (∀ i, qdef A i=0 ∨ nodes A i=1 ∧ qdef A i=-((2:K)⁻¹ : K)) := by
  obtain ⟨h2,r2,r3,r4,r5⟩ := minimal_five_ranks ha hsep hR
  let d := qdef A
  let w := mat A d
  have hdm : d∈zeroSpace A 2 := qdef_mem A
  have hd1 : d 1 = -((2:K)⁻¹ : K) := qdef_second_normalized ha h1
  have hd1ne : d 1≠0 := by rw [hd1]; exact neg_ne_zero.mpr (inv_ne_zero (by norm_num))
  obtain ⟨a,ha'⟩ := Submodule.mem_span_singleton.mp hdep
  have hsc := congrFun ha' (1 : Fin (s+5))
  change a * d 1 = d 1 * nodes A 1 ^ 1 at hsc
  rw [h1,one_pow,mul_one] at hsc
  have ha1 : a=1 := by
    apply mul_right_cancel₀ hd1ne
    simpa using hsc
  have hd : diag (nodes A) d=d := by
    calc
      _ = signal A d 1 := by rw [← signal_step A d 0,signal_zero]
      _ = a • d := ha'.symm
      _ = d := by rw [ha1,one_smul]
  have heig (i : Fin (s+5)) (h : d i≠0) : nodes A i=1 := by
    have he := congrFun hd i
    change nodes A i * d i = d i at he
    apply mul_right_cancel₀ h
    simpa using he
  have hwout : w∉zeroSpace A 2 := by
    intro h
    have hN (v) (hv : v∈zeroSpace A 2) : mat A v∈zeroSpace A 2 := by
      rw [h2] at hv
      obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul]
      exact (zeroSpace A 2).smul_mem r h
    have hC (v) (hv : v∈zeroSpace A 2) : diag (nodes A) v∈zeroSpace A 2 := by
      rw [h2] at hv
      obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,hd]
      exact (zeroSpace A 2).smul_mem r hdm
    have hz := mem_of_invariant_seed (Equiv.refl _) _ (causal_mat ha) (nodes A) 1
      (zeroSpace A 2) hN hC (forward_seed_mem A)
    have hcEq : diag (nodes A) (1:Vec K (s+5)) = nodes A := by ext i; simp
    rw [hcEq] at hz
    exact nodes_not_zeroSpace hsep (by decide) (zeroSpace_mono _ (by decide : 2≤5) hz)
  have hw : w∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 hdm
  have h3 : zeroSpace A 3=mixedSpan A d w 0 := by
    rw [mixedSpan,chainSpan_zero,← h2]
    exact sup_singleton_eq_of_rank (zeroSpace_mono _ (by decide)) hw hwout (by omega)
  have step {j k : ℕ} (hj : 3≤j) (hj5 : j≤5) (hU : zeroSpace A j=mixedSpan A d w k)
      (hr : finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1) :
      zeroSpace A (j+1)=mixedSpan A d w (k+1) := by
    have ht : signal A w (k+1)∈zeroSpace A (j+1) := by
      rw [← signal_step]
      apply diag_zeroSpace A j
      rw [hU]
      exact (show chainSpan A w k≤mixedSpan A d w k from le_sup_right) (signal_mem_chainSpan A w le_rfl)
    have hout : signal A w (k+1)∉zeroSpace A j := by
      intro hx
      have hC (v) (hv : v∈zeroSpace A j) : diag (nodes A) v∈zeroSpace A j := by
        rw [hU] at hv ⊢
        exact mixedSpan_diag_stable hd (hU ▸ hx) hv
      have h := invariant_forces_two_forward ha hj (hsep.mono hj5) hC
      omega
    rw [mixedSpan_succ,← hU]
    exact sup_singleton_eq_of_rank (zeroSpace_mono _ (by omega)) ht hout hr
  have h4 := step (by decide) (by decide) h3 (by
    change finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1; omega)
  have h5 := step (by decide) (by decide) h4 (by
    change finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1; omega)
  refine ⟨h3,h4,h5,?_⟩
  have ht (u : K) (hknots : ∀ i, w i=0 ∨ nodes A i=1 ∨ nodes A i=u) : False := by
    have hA : signal A w 2 = (1+u) • signal A w 1 - u • signal A w 0 := by
      ext i
      simp only [signal,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,pow_zero,mul_one,pow_one]
      rcases hknots i with hh|hh|hh <;> rw [hh] <;> ring
    have hm : signal A w 2∈zeroSpace A 4 := by
      rw [hA,h4]
      have hc (k : ℕ) (hk : k≤1) : signal A w k∈mixedSpan A d w 1 :=
        (show chainSpan A w 1≤mixedSpan A d w 1 from le_sup_right) (signal_mem_chainSpan A w hk)
      exact (mixedSpan A d w 1).sub_mem ((mixedSpan A d w 1).smul_mem _ (hc 1 le_rfl))
        ((mixedSpan A d w 1).smul_mem _ (hc 0 (by decide)))
    have hC (x) (hx : x∈zeroSpace A 4) : diag (nodes A) x∈zeroSpace A 4 := by
      rw [h4] at hx ⊢
      exact mixedSpan_diag_stable hd (h4 ▸ hm) hx
    have hz := invariant_forces_two_forward ha (j:=4) (by decide) (hsep.mono (by decide)) hC
    change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at hz
    omega
  have hp : ∃ i, w i≠0 ∧ nodes A i≠1 := by
    by_contra! h
    apply ht 1
    intro i
    by_cases hi : w i=0
    · exact Or.inl hi
    · exact Or.inr (Or.inl (h i hi))
  obtain ⟨i,hiw,hic⟩ := hp
  have hh : ∃ j, w j≠0 ∧ nodes A j≠1 ∧ nodes A j≠nodes A i := by
    by_contra! h
    apply ht (nodes A i)
    intro j
    by_cases hjw : w j=0
    · exact Or.inl hjw
    · by_cases hjc : nodes A j=1
      · exact Or.inr (Or.inl hjc)
      · exact Or.inr (Or.inr (h j hjw hjc))
  obtain ⟨j,hjw,hjc,hij⟩ := hh
  have hdi : d i=0 := by by_contra h; exact hic (heig i h)
  have hdj : d j=0 := by by_contra h; exact hjc (heig j h)
  have hsq : d*d∈zeroSpace A 4 := zeroSpace_mul (A:=A) (m:=2) (n:=2) (v:=d) (w:=d) hdm hdm
  rw [h4,mixedSpan,chainSpan_succ,chainSpan_zero] at hsq
  obtain ⟨D,hD,W,hW,hEq⟩ := Submodule.mem_sup.mp hsq
  obtain ⟨x,hx⟩ := Submodule.mem_span_singleton.mp hD
  obtain ⟨W0,hW0,W1,hW1,hW'⟩ := Submodule.mem_sup.mp hW
  obtain ⟨y,hy⟩ := Submodule.mem_span_singleton.mp hW0
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp hW1
  have hE : x • d + (y • w + z • signal A w 1)=d*d := by rw [hx,hy,hz,hW',hEq]
  have hu (l : Fin (s+5)) (hwl : w l≠0) (hdl : d l=0) : y + z*nodes A l=0 := by
    have h := congrFun hE l
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,signal,pow_one,hdl,mul_zero,zero_add] at h
    apply mul_right_cancel₀ hwl
    rw [zero_mul]
    linear_combination h
  have hzi : z=0 := (mul_eq_zero.mp (show z*(nodes A j-nodes A i)=0 by
    linear_combination hu j hjw hdj - hu i hiw hdi)).resolve_right (sub_ne_zero.mpr hij)
  have hyi : y=0 := by simpa [hzi] using hu i hiw hdi
  have hD (l : Fin (s+5)) (hn : d l≠0) : x=d l := by
    have h := congrFun hE l
    simp only [hzi,hyi,zero_smul,add_zero,Pi.smul_apply,smul_eq_mul,Pi.mul_apply] at h
    exact mul_right_cancel₀ hn h
  intro l
  by_cases hl : d l=0
  · exact Or.inl hl
  · exact Or.inr ⟨heig l hl,(hD l hl).symm.trans ((hD 1 hd1ne).trans hd1)⟩

end RKCert.Paired
