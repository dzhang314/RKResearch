module
public import RKCert.DirkReverseMoments
public import RKCert.BackwardGrowth
public import RKCert.TableauHermiteGain

@[expose] public section
/-! # Reflected polynomial primitive rows at the genuine degree-four budget -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K : Type*} [Field K] {s p : ℕ}

theorem reflected_4 (A : Fin s → Fin s → K) (b x : Vec K s) :
    row (reflWeight A b 4) x = probe A b 0 x - 4*probe A b 1 x + 6*probe A b 2 x -
      4*probe A b 3 x + probe A b 4 x := by
  simp only [reflWeight,reflNode,row_apply,probe,Finset.mul_sum,
    ←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

/-- Reflection of integration by parts at cubic degree. Order supplies all denominators. -/
theorem cubic_tree {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (hp : t.order+4≤p) :
    row (reflected A b 3) (normTree A t)=0 := by
  rw [reflected_apply,reflected_3,reflected_4]
  let d : K := t.order
  have h0 (k : ℕ) (hk : k≤4) :
      probe A b k (normTree A t)=(d+(k:K))⁻¹ := probe_norm_inv ho t k (by omega)
  have h1 (k : ℕ) (hk : k≤3) :
      probe A b k (mat A (normTree A t))=(d+(k+1:ℕ))⁻¹/d := by
    simpa only [d,Nat.cast_add,Nat.cast_one,add_right_comm _ (1:K),add_assoc] using
      probe_mat_norm_inv ho t k (by omega)
  have hden (k : ℕ) (hk : k≤4) : d+(k:K)≠0 := by
    change (t.order:K)+(k:K)≠0
    rw [←Nat.cast_add]
    exact cast_ne_zero_of_budget ho (Nat.add_pos_left t.order_pos _) (by omega)
  have h0' := hden 0 (by decide); have h1' := hden 1 (by decide)
  have h2' := hden 2 (by decide); have h3' := hden 3 (by decide)
  have h4' := hden 4 (by decide)
  rw [h0 0 (by decide),h0 1 (by decide),h0 2 (by decide),h0 3 (by decide),h0 4 (by decide),
    h1 0 (by decide),h1 1 (by decide),h1 2 (by decide),h1 3 (by decide)]
  norm_num at h0' h1' h2' h3' h4' ⊢
  field_simp
  ring

theorem reflected_annih {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {k j : ℕ} (hk : k≤3) (hp : j+k+2≤p) :
    reflected A b k ∈ annih (treeSpace A j) := by
  by_cases ht : k≤2
  · exact mem_annih.mpr (fun _ hv => reflected_treeSpace ho j k ht hp hv)
  · have he : k=3 := by omega
    subst k
    exact annih_of_norm ho (by omega) (fun t h => cubic_tree ho t (by omega))

variable [CharZero K]
omit [CharZero K] in
theorem weighted_monomial (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) (r : K) :
    weightedEval (mirror A) b (monomial k r)=r • reflWeight A b k := by
  ext i
  simp only [weightedEval_apply,eval_monomial,reflWeight,reflNode,mirror,Pi.smul_apply,
    Pi.sub_apply,Pi.one_apply,smul_eq_mul]
  ring

/-- Every polynomial of degree at most three, not only power generators. -/
theorem reverse_primitive_annih {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (j : ℕ) (hp : j+5≤p) (P : K[X]) (hP : P.natDegree≤3) :
    transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)
      ∈ annih (treeSpace A j) := by
  let E := weightedEval (mirror A) b
  let D := (transMat A).comp E - E.comp formalPrimitiveLinear
  change D P ∈ _
  rw [P.as_sum_range' 4 (by omega),map_sum]
  apply (annih (treeSpace A j)).sum_mem
  intro k hk
  have hle : k≤3 := by have := Finset.mem_range.mp hk; omega
  let r := P.coeff k
  have hn : ((k+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hh := (annih (treeSpace A j)).smul_mem (r/((k+1:ℕ):K)) (reflected_annih ho hle (by omega))
  change transMat A (weightedEval (mirror A) b (monomial k r)) -
    weightedEval (mirror A) b (formalPrimitive (monomial k r))∈_
  rw [formalPrimitive_eq_treePrimitive,primitive_monomial,weighted_monomial,weighted_monomial,map_smul]
  convert hh using 1
  rw [reflected,smul_sub,smul_smul,div_mul_cancel₀ _ hn]

end RKCert.Paired.ReverseHull
