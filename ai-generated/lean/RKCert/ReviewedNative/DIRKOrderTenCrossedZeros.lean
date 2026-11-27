module

public import RKCert.ReviewedNative.DIRKOrderTenKernelSeeds
public import RKCert.ReviewedNative.DIRKCrossedCubicPivot

@[expose] public section

/-! # Four actual zero diagonals at the eleven-stage order-ten boundary -/
namespace RKResearch.Certified.Graded.CrossedOrderTen
open RKResearch FiniteRootedTree Reverse Module
open scoped Matrix FiniteRootedTree BigOperators
noncomputable section

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

private def clockAct (A : Matrix (Fin 11) (Fin 11) K) (n : Nat) :=
  diag ((nodes A)^n)

private theorem clockAct_step (n : Nat) :
    clockAct A (n+1) = (diag (nodes A)).comp (clockAct A n) := by
  apply LinearMap.ext
  intro v
  ext i
  simp only [clockAct,LinearMap.comp_apply,diag_apply,Pi.pow_apply,Pi.mul_apply,pow_succ']
  ring

private theorem clockAct_tree {q : Nat} {v : Fin 11 → K}
    (h : v∈treeSpace A q) (n : Nat) : clockAct A n v∈treeSpace A (q+n) := by
  induction n with
  | zero =>
    have e : clockAct A 0 v=v := by ext i; simp [clockAct]
    simpa only [e,Nat.add_zero] using h
  | succ n ih =>
    rw [clockAct_step,LinearMap.comp_apply,Nat.add_succ]
    exact diag_treeSpace A (q+n) ih

private theorem clockAct_defect {q : Nat} {v : Fin 11 → K}
    (h : v∈zeroSpace A q) (n : Nat) : clockAct A n v∈zeroSpace A (q+n) := by
  induction n with
  | zero =>
    have e : clockAct A 0 v=v := by ext i; simp [clockAct]
    simpa only [e,Nat.add_zero] using h
  | succ n ih =>
    rw [clockAct_step,LinearMap.comp_apply,Nat.add_succ]
    exact diag_zeroSpace A (q+n) ih

private theorem clockAct_power (j d : Nat) :
    clockAct A j ((nodes A)^d) = (nodes A)^(d+j) := by
  ext i
  simp only [clockAct,diag_apply,Pi.pow_apply,pow_add]
  ring

private theorem probe_clockAct (i k : Nat) (v : Fin 11 → K) :
    probe A b i (clockAct A k v)=probe A b (i+k) v := by
  simp only [probe,row_apply,dotProduct,clockAct,diag_apply,Pi.pow_apply,pow_add]
  apply Finset.sum_congr rfl
  intro z _
  ring

private def mu (K : Type*) [Field K] (n : Nat) : K := (((n+1:Nat):K))⁻¹

private theorem mu_paid (ho : HasOrder 10 A b) (n : Nat) (pay : n<10) :
    (((n+1:Nat):K))*mu K n=1 := by
  exact mul_inv_cancel₀ (ho.natCast_isUnit (n:=n+1) (by omega) (by omega)).ne_zero

private theorem probe_pow (ho : HasOrder 10 A b) (i d : Nat) (pay : i+d<10) :
    probe A b i ((nodes A)^d) = mu K (i+d) := by
  have mp := ho.hasQuadratureOrder (i+d) pay
  have e : probe A b i ((nodes A)^d)=b ⬝ᵥ (nodes A)^(i+d) := by
    simp only [probe,row_apply,dotProduct,Pi.pow_apply,pow_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e]
  exact eq_inv_of_mul_eq_one_right mp

private theorem probe_primitive (ho : HasOrder 10 A b) (i d : Nat) (pay : i+d+2 ≤ 10) :
    probe A b i (mat A ((nodes A)^d)) = mu K d * mu K (i+d+1) := by
  have z := probe_zeroSpace ho (k:=i) (by omega) (monomialStageDefect_mem A d)
  change probe A b i ((((d+1:Nat):K) • mat A ((nodes A)^d)) - (nodes A)^(d+1))=0 at z
  rw [map_sub,map_smul,smul_eq_mul,probe_pow ho i (d+1) (by omega)] at z
  apply mul_left_cancel₀ (ho.natCast_isUnit (n:=d+1) (by omega) (by omega)).ne_zero
  rw [←mul_assoc,mu_paid ho d (by omega),one_mul]
  simpa only [Nat.add_assoc] using sub_eq_zero.mp z

private theorem coeff_polynomial (a : Fin 4 → K) :
    coeffEval A 3 a =
      a 0 • (1 : Fin 11 → K) + (a 1 • nodes A + (a 2 • (nodes A)^2 + a 3 • (nodes A)^3)) := by
  ext i
  simp [coeffEval_apply,Fin.sum_univ_succ,normTree_clock,normTree_leaf]
  ring

private theorem front_expansion (F : FrontSeed A) :
    F.v=F.a 1 • nodes A +(F.a 2 • (nodes A)^2 + F.a 3 • (nodes A)^3) +
      F.d • monomialStageDefect A 2 := by
  rw [F.form,coeff_polynomial,F.a0,zero_smul,zero_add]

private def h (B : BackSeed A b) : K := B.a 0
private def l (B : BackSeed A b) : K := B.a 0+B.a 1
private def m (B : BackSeed A b) : K := B.a 0+B.a 1+B.a 2

private theorem back_const_sum (S : Saturated A b) (B : BackSeed A b) :
    B.a 0+B.a 1+B.a 2+B.a 3=0 := by
  have e := B.a_last
  rw [coeff_polynomial] at e
  simp only [Pi.add_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul,Pi.one_apply,S.last_node,
    one_pow,mul_one] at e
  linear_combination e

private theorem back_coeffs_live (S : Saturated A b) (B : BackSeed A b) :
    h B≠0 ∨ l B≠0 ∨ m B≠0 := by
  by_contra! z
  have s := back_const_sum S B
  apply B.a_live
  ext i
  change B.a i=0
  have i4 : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  rcases i4 i with rfl|rfl|rfl|rfl
  · exact z.1
  · exact (by unfold h l at z; linear_combination z.2.1-z.1)
  · exact (by unfold l m at z; linear_combination z.2.2-z.2.1)
  · exact (by unfold m at z; linear_combination s-z.2.2)

private theorem back_polynomial (S : Saturated A b) (B : BackSeed A b) :
    coeffEval A 3 B.a =
      reflectedClock A * (h B • (1:Fin 11→K) + (l B • nodes A + m B • (nodes A)^2)) := by
  have e : B.a 3 = -m B := by unfold m; linear_combination back_const_sum S B
  rw [coeff_polynomial]
  ext i
  simp only [Pi.mul_apply,Pi.add_apply,Pi.smul_apply,Pi.pow_apply,Pi.one_apply,smul_eq_mul,
    reflectedClock,Pi.sub_apply,e]
  unfold h l m
  ring

private theorem profile_row (S : Saturated A b) (B : BackSeed A b) (v : Fin 11 → K) :
    row (diag b (coeffEval A 3 B.a)) v =
      h B*(probe A b 0 v-probe A b 1 v)
      +l B*(probe A b 1 v-probe A b 2 v)
      +m B*(probe A b 2 v-probe A b 3 v) := by
  rw [back_polynomial S B]
  simp only [probe,row_apply,dotProduct,diag_apply,Pi.mul_apply,Pi.add_apply,Pi.smul_apply,
    Pi.one_apply,Pi.pow_apply,Pi.sub_apply,smul_eq_mul,reflectedClock,pow_zero,mul_one,pow_one,
    ←Finset.sum_sub_distrib,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def mixed (A : Matrix (Fin 11) (Fin 11) K) (j k : Nat) :=
  (clockAct A k).comp ((mat A).comp (clockAct A j))

private theorem mix_read (ho : HasOrder 10 A b) (S : Saturated A b)
    (F : FrontSeed A) (B : BackSeed A b) (j k : Nat) (paid : j+k ≤ 2) :
    row B.v (mixed A j k F.v) =
      F.a 1 * mu K (j+1) * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (j+k+2)
      + F.a 2 * mu K (j+2) * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (j+k+3)
      + F.a 3 * mu K (j+3) * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (j+k+4) := by
  have fv : F.v∈treeSpace A 3 := by
    rw [F.form]
    exact (treeSpace A 3).add_mem (coeffEval_mem_treeSpace _ _ _)
      ((zeroSpace_le_treeSpace _ _) ((zeroSpace A 3).smul_mem _ (monomialStageDefect_mem _ _)))
  have tre : mixed A j k F.v∈treeSpace A (3+j+1+k) :=
    clockAct_tree (mat_treeSpace A (3+j) (clockAct_tree fv j)) k
  have dead := reflectedStageRow_treeSpace ho (3+j+1+k) 2 (by omega) tre
  change row (reflectedStageRow A b 2) (mixed A j k F.v)=0 at dead
  rw [B.form]
  simp only [row_apply,add_dotProduct,smul_dotProduct,smul_eq_mul]
  rw [show (reflectedStageRow A b 2) ⬝ᵥ mixed A j k F.v=0 from dead,mul_zero,add_zero]
  change row (diag b (coeffEval A 3 B.a)) (mixed A j k F.v)=_
  rw [profile_row S B]
  have f (i : Nat) (ip : i≤3) :
      probe A b i (mixed A j k F.v) =
        F.a 1*mu K (j+1)*mu K (j+k+2+i) +
        F.a 2*mu K (j+2)*mu K (j+k+3+i) +
        F.a 3*mu K (j+3)*mu K (j+k+4+i) := by
    have ghost : mixed A j k (monomialStageDefect A 2)∈zeroSpace A (3+j+1+k) :=
      clockAct_defect (mat_zeroSpace ho (3+j) (by omega)
        (clockAct_defect (monomialStageDefect_mem A 2) j)) k
    have gz : probe A b i (mixed A j k (monomialStageDefect A 2))=0 :=
      probe_zeroSpace ho (by omega) ghost
    rw [front_expansion]
    simp only [map_add,map_smul,smul_eq_mul,gz,mul_zero,add_zero]
    have q (d : Nat) (dp : 1≤d ∧ d≤3) :
        probe A b i (mixed A j k ((nodes A)^d)) =
          mu K (j+d)*mu K (j+k+d+1+i) := by
      change probe A b i (clockAct A k (mat A (clockAct A j ((nodes A)^d))))=_
      rw [probe_clockAct,clockAct_power,probe_primitive ho (i+k) (d+j) (by omega)]
      congr 1 <;> apply congrArg (mu K) <;> omega
    have q1 := q 1 (by decide)
    rw [pow_one] at q1
    rw [q1,q 2 (by decide),q 3 (by decide)]
    ring
  rw [f 0 (by decide),f 1 (by decide),f 2 (by decide),f 3 (by decide)]
  simp only [CrossedCubicPivot.moment]
  ring

private theorem mix_zero_crossed (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (cross : B.pivot≤F.pivot) (j k : Nat) :
    row B.v (mixed A j k F.v)=0 := by
  rw [row_apply,dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : B.pivot < i
  · rw [B.after i hi,zero_mul]
  · have ip : i≤F.pivot := (le_of_not_gt hi).trans cross
    have zero : mat A (clockAct A j F.v) i=0 := by
      rw [mat_apply,Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro u _
      by_cases hp : u < F.pivot
      · rw [clockAct,diag_apply,F.before u hp,mul_zero,mul_zero]
      · by_cases hq : i < u
        · rw [ha hq,zero_mul]
        · have eq : i=F.pivot := le_antisymm ip ((le_of_not_gt hp).trans (le_of_not_gt hq))
          have eq2 : u=F.pivot := le_antisymm ((le_of_not_gt hq).trans ip) (le_of_not_gt hp)
          rw [eq,eq2,F.explicit,zero_mul]
    simp only [mixed,LinearMap.comp_apply,clockAct,diag_apply]
    change B.v i * (((nodes A)^k) i * mat A (clockAct A j F.v) i)=0
    rw [zero,mul_zero,mul_zero]


private theorem front_coeffs_live (F : FrontSeed A) :
    F.a 1≠0 ∨ F.a 2≠0 ∨ F.a 3≠0 := by
  by_contra! z
  apply F.a_live
  ext i
  change F.a i=0
  have i4 : ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  rcases i4 i with rfl|rfl|rfl|rfl
  · exact F.a0
  · exact z.1
  · exact z.2.1
  · exact z.2.2

private theorem scale_mu (ho : HasOrder 10 A b) (L q n : Nat)
    (paid : n<10) (id : L=(n+1)*q) : (L:K)*mu K n=(q:K) := by
  rw [id,Nat.cast_mul,mul_comm (((n+1:Nat):K)) (q:K),mul_assoc,mu_paid ho n paid,mul_one]

private theorem ordered_pivots (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) : F.pivot<B.pivot := by
  by_contra! cross
  let M := CrossedCubicPivot.moment (mu K) (h B) (l B) (m B)
  have eval (j k : Nat) (paid : j+k ≤ 2) :
      F.a 1*mu K (j+1)*M (j+k+2)+F.a 2*mu K (j+2)*M (j+k+3)+
        F.a 3*mu K (j+3)*M (j+k+4)=0 := by
    exact (mix_read ho S F B j k paid).symm.trans (mix_zero_crossed ha F B cross j k)
  have tests : CrossedCubicPivot.Tests (F.a 1) (F.a 2) (F.a 3) M := by
    constructor
    · intro t ht
      have e := eval 0 t (by omega)
      simp only [Nat.zero_add] at e
      have s1 : (12:K)*mu K 1=6 := scale_mu ho 12 6 1 (by decide) (by decide)
      have s2 : (12:K)*mu K 2=4 := scale_mu ho 12 4 2 (by decide) (by decide)
      have s3 : (12:K)*mu K 3=3 := scale_mu ho 12 3 3 (by decide) (by decide)
      rw [←s1,←s2,←s3]
      linear_combination 12*e
    · intro t ht1 ht2
      have e := eval 1 (t-1) (by omega)
      rw [show 1+(t-1)=t by omega] at e
      have s1 : (60:K)*mu K 2=20 := scale_mu ho 60 20 2 (by decide) (by decide)
      have s2 : (60:K)*mu K 3=15 := scale_mu ho 60 15 3 (by decide) (by decide)
      have s3 : (60:K)*mu K 4=12 := scale_mu ho 60 12 4 (by decide) (by decide)
      rw [←s1,←s2,←s3]
      linear_combination 60*e
    · have e := eval 2 0 (by decide)
      have s1 : (60:K)*mu K 3=15 := scale_mu ho 60 15 3 (by decide) (by decide)
      have s2 : (60:K)*mu K 4=12 := scale_mu ho 60 12 4 (by decide) (by decide)
      have s3 : (60:K)*mu K 5=10 := scale_mu ho 60 10 5 (by decide) (by decide)
      rw [←s1,←s2,←s3]
      linear_combination 60*e
  have z := CrossedCubicPivot.no_crossed (mu K)
    (fun t ht => by rw [Lean.Grind.Semiring.ofNat_eq_natCast]; exact mu_paid ho t ht)
    (F.a 1) (F.a 2) (F.a 3) (h B) (l B) (m B) (front_coeffs_live F) tests
  rcases back_coeffs_live S B with h | l | m
  · exact h z.1
  · exact l z.2.1
  · exact m z.2.2

/-- An actual eleven-stage order-ten DIRK tableau must have two distinct
interior zero diagonals as well as its first and last zero diagonals. -/
theorem crossed_zero_sites (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    ∃ i j : Fin 11, 0 < i ∧ i < j ∧ j < Fin.last 10 ∧
      A 0 0=0 ∧ A i i=0 ∧ A j j=0 ∧ A (Fin.last 10) (Fin.last 10)=0 := by
  let S := saturated ha ho
  let F := Classical.choice (exists_front_seed ha ho S)
  let B := Classical.choice (exists_back_seed ha ho S)
  exact ⟨F.pivot,B.pivot,F.interior,ordered_pivots ha ho S F B,B.interior,
    S.physical_origin 0,F.explicit,B.explicit,S.last_column _⟩

open scoped Classical

/-- The full equality-face diagonal census. No sign, distinctness,
nonsingularity or full-weight assumptions are required. -/
theorem four_zeros (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    4 ≤ (Finset.univ.filter (fun i : Fin 11 => A i i=0)).card := by
  classical
  obtain ⟨i,j,hi,hij,hj,e0,ei,ej,et⟩ := crossed_zero_sites ha ho
  have ht : (0:Fin 11) < Fin.last 10 := hi.trans (hij.trans hj)
  have h0j : (0:Fin 11)<j := hi.trans hij
  have hit : i<Fin.last 10 := hij.trans hj
  let S : Finset (Fin 11) := {0,i,j,Fin.last 10}
  have ejN : j ∉ ({Fin.last 10}:Finset (Fin 11)) := by
    simpa only [Finset.mem_singleton] using ne_of_lt hj
  have eiN : i ∉ ({j,Fin.last 10}:Finset (Fin 11)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨ne_of_lt hij,ne_of_lt hit⟩
  have e0N : (0:Fin 11) ∉ ({i,j,Fin.last 10}:Finset (Fin 11)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨ne_of_lt hi,ne_of_lt h0j,ne_of_lt ht⟩
  have n : S.card=4 := by
    dsimp only [S]
    rw [Finset.card_insert_of_notMem e0N,Finset.card_insert_of_notMem eiN,
      Finset.card_insert_of_notMem ejN,Finset.card_singleton]
  have contained : S⊆Finset.univ.filter (fun i : Fin 11 => A i i=0) := by
    intro z hz
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact e0
    · exact ei
    · exact ej
    · exact et
  rw [←n]
  exact Finset.card_le_card contained


/-- Over a nontrivial commutative ring the consequence is four nonunit
entries, not four entries literally equal to zero: a nonunit may be
nonzero in the original coefficient ring. -/
theorem four_nonunit_diagonals {R : Type*} [CommRing R] [Nontrivial R]
    {D : Matrix (Fin 11) (Fin 11) R} {w : Fin 11 → R}
    (ha : D.IsLowerTriangular) (ho : HasOrder 10 D w) :
    4 ≤ (Finset.univ.filter (fun i : Fin 11 => ¬IsUnit (D i i))).card := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  have z := four_zeros (ha.map f) (ho.map f)
  refine z.trans (Finset.card_le_card ?_)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1,?_⟩
  intro hu
  exact (hu.map f).ne_zero hi.2


end
end RKResearch.Certified.Graded.CrossedOrderTen
