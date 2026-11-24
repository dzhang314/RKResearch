module

public import RKCert.ERKLowBase

@[expose] public section

/-! # Saturated physical rank charts at orders eight and nine

These are necessary conditions on actual tableaux. They do not assert
that the remaining ten-stage or twelve-stage branches are impossible.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p : ℕ}

/-- If a stage annihilator has room for exactly the first two quadratic
backward directions, the linear backward seed is forced to vanish. -/
theorem reverse_capacity_two {A : Fin s → Fin s → K} {b : Vec K s} {j : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hj : j+4 ≤ p)
    (hcap : s ≤ finrank K (treeSpace A j)+2) :
    backSeed1 A b=0 ∧ back A b 2 = annih (treeSpace A j) := by
  have hb := backward_count ha ho j 2 (by omega)
  have hzero : backSeed1 A b=0 := by
    by_contra hn
    have he : finrank K (back A b 0)=1 := finrank_span_singleton hn
    omega
  refine ⟨hzero,?_⟩
  have he := finrank_add_annih_eq (treeSpace A j)
  have hdim := back_finrank ha ho 2 (by omega)
  exact Submodule.eq_of_le_of_finrank_le (back_annih ho j 2 (by omega)) (by omega)

theorem reverse_capacity_terminal {A : Fin (s+1) → Fin (s+1) → K}
    {b : Vec K (s+1)} {j : ℕ} (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hj : j+4 ≤ p) (hcap : s+1 ≤ finrank K (treeSpace A j)+2) (hb : b (Fin.last s)≠0) :
    backSeed1 A b=0 ∧ nodes A (Fin.last s)=1 ∧
      Pi.single (Fin.last s) 1 ∈ treeSpace A j ∧ back A b 2 = annih (treeSpace A j) := by
  obtain ⟨hzero,he⟩ := reverse_capacity_two ha ho hj hcap
  have hsup (i : Fin (s+1)) (hi : Fin.last s < i) : b i=0 := by
    have h := i.isLt
    change s < i.val at hi
    omega
  have hc : nodes A (Fin.last s)=1 := (sub_eq_zero.mp (last_mirror_zero ha hb hsup hzero)).symm
  refine ⟨hzero,hc,?_,he⟩
  apply row_annih_test
  intro w hw
  rw [← he] at hw
  have hz := back_vanish ha hb hsup hzero 2 hw (Fin.last s) le_rfl
  simpa [row_apply,Pi.single_apply] using hz

section CharZero
variable [CharZero K]

theorem midpoint_four_minimal_ranks {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p) (hs : 0 < s)
    (hcap : finrank K (treeSpace A 4) ≤ 8) :
    finrank K (zeroSpace A 3)=2 ∧ finrank K (zeroSpace A 4)=3 ∧
    finrank K (treeSpace A 3)=6 ∧ finrank K (treeSpace A 4)=8 := by
  have h4 := explicit_treeSpace_finrank_eq ha ho 4 hs (by omega) (by omega)
  have h3 := explicit_treeSpace_finrank_eq ha ho 3 hs (by omega) (by omega)
  have hf4 := zeroSpace_finrank ha ho (n:=3) (by omega)
  have hf3 := zeroSpace_finrank ha ho (n:=2) (by omega)
  change 3 ≤ finrank K (zeroSpace A 4) at hf4
  change 2 ≤ finrank K (zeroSpace A 3) at hf3
  have hsep : Separated A 4 := explicit_separated ha ho (by omega) hs
  have hlt := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha hsep (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3) < finrank K (zeroSpace A 4) at hlt
  omega

/-- The exact eight-order ten-stage chart, including D(1), a genuine last
stage at node one, and the endpoint that lies in E4 but not E3. -/
theorem order8_ten_stage_chart {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    b (Fin.last 9)≠0 ∧ backSeed1 A b=0 ∧ nodes A (Fin.last 9)=1 ∧
    Pi.single (Fin.last 9) 1 ∈ treeSpace A 4 ∧ Pi.single (Fin.last 9) 1 ∉ treeSpace A 3 ∧
    finrank K (zeroSpace A 3)=2 ∧ finrank K (zeroSpace A 4)=3 ∧
    finrank K (treeSpace A 3)=6 ∧ finrank K (treeSpace A 4)=8 ∧
    finrank K (treeSpace A 5) ≤ 9 ∧ back A b 2 = annih (treeSpace A 4) := by
  have hb := last_weight_of_uniform_equality ha ho (by decide)
  have hr := backward_count ha ho 4 2 (by decide)
  obtain ⟨hf3,hf4,he3,he4⟩ := midpoint_four_minimal_ranks ha ho (by decide) (by decide) (by omega)
  have hr5 := backward_count ha ho 5 1 (by decide)
  have hcap : 10 ≤ finrank K (treeSpace A 4) + 2 := by rw [he4]
  obtain ⟨hzero,hc,he,heq⟩ := reverse_capacity_terminal (s:=9) ha ho (j:=4) (by decide) hcap hb
  have hout := terminal_single_not_mem ha ho (q:=3) (by decide) (Fin.last 9) hb hc
  exact ⟨hb,hzero,hc,he,hout,hf3,hf4,he3,he4,by omega,heq⟩

/-- The medium grades in the hypothetical twelve-stage order-nine
chart. Bounds refer to actual full-coordinate tree spans. -/
theorem order9_twelve_stage_chart {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    b (Fin.last 11)≠0 ∧
    finrank K (zeroSpace A 3)=2 ∧ finrank K (zeroSpace A 4)=3 ∧
    finrank K (treeSpace A 3)=6 ∧ finrank K (treeSpace A 4)=8 ∧
    9 ≤ finrank K (treeSpace A 5) ∧ finrank K (treeSpace A 5) ≤ 10 ∧
    finrank K (treeSpace A 6) ≤ 11 := by
  have hb := last_weight_of_uniform_equality ha ho (by decide)
  have hc := backward_endpoint_count ha ho 4 3 (by decide) (by decide)
  obtain ⟨hf3,hf4,he3,he4⟩ := midpoint_four_minimal_ranks ha ho (by decide) (by decide) (by omega)
  have hr5 := backward_count ha ho 5 2 (by decide)
  have hr6 := backward_count ha ho 6 1 (by decide)
  have hl5 : 9 ≤ finrank K (treeSpace A 5) := by
    by_contra! h
    have ee : treeSpace A 4 = treeSpace A 5 :=
      Submodule.eq_of_le_of_finrank_le (treeSpace_mono _ (by decide)) (by omega)
    have ht := dim_of_invariant_stage_space ha ho (treeSpace A 4)
      (stageWeight_mem_space A .leaf (by decide)) (fun v hv => ee.symm ▸ mat_treeSpace A 4 hv)
    omega
  exact ⟨hb,hf3,hf4,he3,he4,hl5,by omega,by omega⟩

omit [CharZero K] in
/-- If the rank-five space reaches its upper limit at order nine,
there is an anchored terminal and no nonzero invariant reverse line. -/
theorem order9_rank_five_full {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hr : finrank K (treeSpace A 5)=10) :
    backSeed1 A b=0 ∧ nodes A (Fin.last 11)=1 ∧
    Pi.single (Fin.last 11) 1 ∈ treeSpace A 5 ∧
    Pi.single (Fin.last 11) 1 ∉ treeSpace A 4 ∧
    back A b 2 = annih (treeSpace A 5) ∧
    (∀ U : Submodule K (Vec K 12), U ≤ annih (treeSpace A 5) →
      (∀ v∈U, transMat A v∈U) → (∀ v∈U, diag (mirror A) v∈U) → U=⊥) := by
  have hb := last_weight_of_uniform_equality ha ho (by decide)
  have hcap : 12 ≤ finrank K (treeSpace A 5) + 2 := by rw [hr]
  obtain ⟨hzero,hc,hm,he⟩ := reverse_capacity_terminal (s:=11) ha ho (j:=5) (by decide) hcap hb
  have haR := finrank_add_annih_eq (treeSpace A 5)
  exact ⟨hzero,hc,hm,terminal_single_not_mem ha ho (q:=4) (by decide) (Fin.last 11) hb hc,
    he,annih_invariant_rank_two ha ho (j:=5) (by decide) (by omega)⟩

end CharZero
end RKCert.Paired
