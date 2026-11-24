module

public import RKCert.ReviewedNative.DIRKSmall
public import RKCert.ReviewedNative.DIRKForwardRank
public import RKCert.ReviewedNative.GradedSeparation

public section

/-! # Five stages at order six for lower triangular tableaux

The proof uses the reviewed tree columns throughout. At the even midpoint,
a nonzero quadratic defect buys an extra defect dimension; if that defect
vanishes, the actual zero first row buys an extra clock column instead.
Neither argument uses row reduction, an ordering on the field, or assumptions
on the nodes, weights, or remaining diagonal entries. -/

namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree Module
open scoped Matrix FiniteRootedTree

section Origin

variable {ι R : Type*} [Fintype ι] [CommRing R] {A : Matrix ι ι R}

/-- A single zero physical row annihilates every homogeneous tree difference;
the other rows need not be strictly triangular (or triangular at all). -/
theorem zeroSpace_at_zero_row {i : ι} (hr : ∀ j, A i j = 0) (q : ℕ) :
    zeroSpace A q ≤ (LinearMap.proj i).ker := by
  have dead (t : FiniteRootedTree) (hnt : t ≠ .leaf) : Φ t A i = 0 := by
    cases t with
    | leaf => exact (hnt rfl).elim
    | butcherProduct t u => simp [Φ, Matrix.mulVec, dotProduct, hr]
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,_,rfl⟩
  change normTree A t i - normTree A u i = 0
  by_cases et : t = .leaf
  · have eu : u = .leaf := (coe_order_eq_one_iff_leaf u).mp (by rw [← he, et]; rfl)
    rw [et, eu, sub_self]
  · have eu : u ≠ .leaf := by
      intro hu
      exact et ((coe_order_eq_one_iff_leaf t).mp (by rw [he, hu]; rfl))
    simp [normTree, dead t et, dead u eu]

theorem coeffEval_at_zero_row {i : ι} (hr : ∀ j, A i j = 0) (q : ℕ) (a : Fin (q+1) → R) :
    coeffEval A q a i = a 0 := by
  have hc : nodes A i = 0 := by simp [nodes, Matrix.mulVec, dotProduct, hr]
  rw [coeffEval_apply, Fin.sum_univ_succ]
  simp only [normTree_clockTree, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hc]
  simp

end Origin

section Field

variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- C(2) on the first physical row forces that entire row to vanish. -/
theorem dirk_first_row_of_zero_quadratic {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : A.IsLowerTriangular) (hc2 : monomialStageDefect A 1 0 = 0) : ∀ j, A 0 j = 0 := by
  have pivot (v : Fin (s+1) → K) : (A *ᵥ v) 0 = A 0 0 * v 0 :=
    lowerTriangular_mulVec_pivot ha 0 v (fun j hj => (Fin.not_lt_zero j hj).elim)
  have hc : nodes A 0 = A 0 0 := by
    change (A *ᵥ (1 : Fin (s+1) → K)) 0 = _
    rw [pivot, Pi.one_apply, mul_one]
  change (2:K) * (A *ᵥ (nodes A)^1) 0 - (nodes A 0)^2 = 0 at hc2
  rw [pow_one, pivot, hc] at hc2
  have hd : (A 0 0)^2 = 0 := by linear_combination hc2
  intro j
  rcases eq_or_lt_of_le (Fin.zero_le j) with hj | hj
  · rw [← hj]
    exact sq_eq_zero_iff.mp hd
  · exact ha hj

/-- Ordinary (unanchored) clock separation at possibly unequal grades. -/
theorem coeff_defect_separated_paid (ho : HasOrder A b p) {q j : ℕ}
    (hm : 2*q+1 ≤ p) (hd : q+j+1 ≤ p) (a : Fin (q+1) → K)
    (h : coeffEval A q a ∈ zeroSpace A j) : a = 0 := by
  ext l
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i k => by omega) a _ l
  intro i
  have hz : probe A b i.val (coeffEval A q a) = 0 := probe_zeroSpace ho (by omega) h
  rwa [probe_coeffEval ho (by omega)] at hz

/-- A zero physical row supplies the constant coefficient. The other q
coefficients are detected by exactly q shifted Cauchy moments. -/
theorem coeff_defect_separated_zero_row (ho : HasOrder A b p) {i : Fin s}
    (hr : ∀ j, A i j = 0) {q j : ℕ} (hm : 2*q ≤ p) (hd : q+j ≤ p)
    (a : Fin (q+1) → K) (h : coeffEval A q a ∈ zeroSpace A j) : a = 0 := by
  have hz : coeffEval A q a i = 0 := zeroSpace_at_zero_row hr j h
  rw [coeffEval_at_zero_row hr] at hz
  have rows (k : Fin q) : (∑ l : Fin q, a l.succ / ((k.val+l.val+2 : ℕ) : K)) = 0 := by
    have z : probe A b k.val (coeffEval A q a) = 0 := probe_zeroSpace ho (by omega) h
    rw [probe_coeffEval ho (by omega), Fin.sum_univ_succ, hz, zero_div, zero_add] at z
    simpa only [Fin.val_succ, Nat.add_assoc] using z
  have tail := moments_detect ho (d:=2) (by decide) (by omega)
    (fun k l => by have := k.isLt; have := l.isLt; omega) (fun l : Fin q => a l.succ) rows
  ext l
  exact Fin.cases hz tail l

/-- A separated polynomial frame and a defect subspace pay distinct
dimensions in the original (untrimmed) stage vector space. -/
theorem coeff_defect_stage_count {q j : ℕ}
    (sep : ∀ a, coeffEval A q a ∈ zeroSpace A j → a = 0) :
    q+1 + finrank K (zeroSpace A j) ≤ s := by
  let F := zeroSpace A j
  let L := (coeffEval A q).coprod F.subtype
  have hin : Function.Injective L := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨a,z⟩ h
    change coeffEval A q a + (z : Fin s → K) = 0 at h
    have eqz := eq_neg_of_add_eq_zero_left h
    have az := sep a (eqz ▸ F.neg_mem z.property)
    have zz : (z : Fin s → K) = 0 := by simpa only [az, map_zero, zero_add] using h
    exact Prod.ext az (Subtype.ext zz)
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hin)

/-- At a paid even midpoint, one obtains 2m-1 stages solely from forward
columns. At m=3 this gives the full published order-six lower endpoint. -/
theorem dirk_even_forward_stage_count (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {m : ℕ} (hm : 2 ≤ m) (pay : 2*m ≤ p) : 2*m-1 ≤ s := by
  have rank := dirk_forward_zeroSpace_rank_floor ha ho (q:=m) hm (by omega)
  by_cases hq : monomialStageDefect A 1 = 0
  · cases s with
    | zero =>
      have h3 : HasOrder A b 3 := fun t ht => ho t (ht.trans (by omega))
      exact False.elim (by have := h3.order_three_stages_field; omega)
    | succ s =>
      have hr := dirk_first_row_of_zero_quadratic ha
        (show monomialStageDefect A 1 0 = 0 from congrFun hq 0)
      have count := coeff_defect_stage_count
        (coeff_defect_separated_zero_row ho hr (q:=m) (j:=m) pay (by omega))
      omega
  · have extra := rank.2 hq
    have count := coeff_defect_stage_count
      (coeff_defect_separated_paid ho (q:=m-1) (j:=m) (by omega) (by omega))
    omega

end Field
end RKResearch.Certified.Graded

namespace RKResearch

/-- A lower triangular order-six tableau over any field needs five stages. -/
theorem HasOrder.dirk_order_six_stages_field {K : Type*} [Field K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 6) (ha : A.IsLowerTriangular) : 5 ≤ s :=
  Certified.Graded.dirk_even_forward_stage_count ha h (m:=3) (by decide) (by decide)

/-- Five physical stages are necessary at order six over every nontrivial
commutative ring, with no separate characteristic or invertibility condition. -/
theorem HasOrder.dirk_order_six_stages {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b 6) (ha : A.IsLowerTriangular) : 5 ≤ s :=
  h.lower_triangular_of_all_fields ha (fun _ _ _ _ ht h' => h'.dirk_order_six_stages_field ht)

end RKResearch
