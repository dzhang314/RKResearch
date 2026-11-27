module

public import RKCert.ReviewedNative.DIRKOrderTenKernelSeeds
public import RKCert.ReviewedNative.DIRKCrossedCubicPivot
public import RKCert.ReviewedNative.DIRKAdjacentCubicScalar
public import RKCert.ReviewedNative.DIRKTwoClockPrimitiveOverlap
public import RKCert.ReviewedNative.DIRKThreeStageOverlap
import Mathlib.Tactic.FieldSimp

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

private theorem no_all_zero_mixes (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b)
    (Z : ∀ (j k : Nat), row B.v (mixed A j k F.v)=0) : False := by
  let M := CrossedCubicPivot.moment (mu K) (h B) (l B) (m B)
  have eval (j k : Nat) (paid : j+k ≤ 2) :
      F.a 1*mu K (j+1)*M (j+k+2)+F.a 2*mu K (j+2)*M (j+k+3)+
        F.a 3*mu K (j+3)*M (j+k+4)=0 := by
    exact (mix_read ho S F B j k paid).symm.trans (Z j k)
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

private theorem ordered_pivots (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) : F.pivot < B.pivot := by
  by_contra! cross
  exact no_all_zero_mixes ho S F B (mix_zero_crossed ha F B cross)

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


private theorem front_is_tree (F : FrontSeed A) : F.v∈treeSpace A 3 := by
  rw [F.form]
  exact (treeSpace A 3).add_mem (coeffEval_mem_treeSpace _ _ _)
    ((zeroSpace_le_treeSpace _ _) ((zeroSpace A 3).smul_mem _ (monomialStageDefect_mem _ _)))

private theorem plain_read (ho : HasOrder 10 A b) (S : Saturated A b)
    (F : FrontSeed A) (B : BackSeed A b) (k : Nat) (paid : k ≤ 3) :
    row B.v (clockAct A k F.v) =
      F.a 1 * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (k+1)
      + F.a 2 * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (k+2)
      + F.a 3 * CrossedCubicPivot.moment (mu K) (h B) (l B) (m B) (k+3) := by
  have tre := clockAct_tree (front_is_tree F) k
  have dead := reflectedStageRow_treeSpace ho (3+k) 2 (by omega) tre
  change row (reflectedStageRow A b 2) (clockAct A k F.v)=0 at dead
  rw [B.form]
  simp only [row_apply,add_dotProduct,smul_dotProduct,smul_eq_mul]
  rw [show (reflectedStageRow A b 2) ⬝ᵥ clockAct A k F.v=0 from dead,mul_zero,add_zero]
  change row (diag b (coeffEval A 3 B.a)) (clockAct A k F.v)=_
  rw [profile_row S B]
  have f (i : Nat) (ip : i ≤ 3) :
      probe A b i (clockAct A k F.v) =
        F.a 1*mu K (k+1+i) + F.a 2*mu K (k+2+i) + F.a 3*mu K (k+3+i) := by
    have ghost := clockAct_defect (monomialStageDefect_mem A 2) k
    have gz : probe A b i (clockAct A k (monomialStageDefect A 2))=0 :=
      probe_zeroSpace ho (by omega) ghost
    rw [front_expansion]
    simp only [map_add,map_smul,smul_eq_mul,gz,mul_zero,add_zero]
    have q (d : Nat) (dp : 1 ≤ d ∧ d ≤ 3) :
        probe A b i (clockAct A k ((nodes A)^d)) = mu K (k+d+i) := by
      rw [probe_clockAct,probe_pow ho (i+k) d (by omega)]
      congr 1
      omega
    have q1 := q 1 (by decide)
    rw [pow_one] at q1
    rw [q1,q 2 (by decide),q 3 (by decide)]
    ring
  rw [f 0 (by decide),f 1 (by decide),f 2 (by decide),f 3 (by decide)]
  simp only [CrossedCubicPivot.moment,Nat.add_zero]
  ring

private theorem mat_vanish_through (ha : A.IsLowerTriangular) {v : Fin 11→K}
    {i : Fin 11} (hz : ∀ j < i, v j=0) (hd : A i i=0) {u : Fin 11} (ui : u ≤ i) :
    mat A v u=0 := by
  have pre : ∀ j < u, v j=0 := fun j hj => hz j (hj.trans_le ui)
  rw [mat_apply,lowerTriangular_mulVec_pivot ha u _ pre]
  rcases lt_or_eq_of_le ui with lt|rfl
  · rw [hz u lt,mul_zero]
  · rw [hd,zero_mul]

private theorem clock_seed_before (F : FrontSeed A) (j : Nat) :
    ∀ u < F.pivot, clockAct A j F.v u=0 := by
  intro u hu
  rw [clockAct,diag_apply,F.before u hu,mul_zero]

private theorem adjacent_cases {i j u : Fin 11} (adj : j.val=i.val+1)
    (hi : i ≤ u) (hj : u ≤ j) : u=i ∨ u=j := by
  have vi : i.val ≤ u.val := hi
  have vj : u.val ≤ j.val := hj
  by_cases h : u.val=i.val
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by omega))

private theorem adjacent_inner (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (adj : B.pivot.val=F.pivot.val+1) (j : Nat) :
    mat A (clockAct A j F.v) B.pivot =
      A B.pivot F.pivot * ((nodes A F.pivot)^j * F.v F.pivot) := by
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  rw [Finset.sum_eq_single F.pivot]
  · rfl
  · intro w _ wne
    by_cases hh : w < F.pivot
    · rw [clock_seed_before F j w hh,mul_zero]
    · by_cases hi : B.pivot < w
      · rw [ha hi,zero_mul]
      · rcases adjacent_cases adj (le_of_not_gt hh) (le_of_not_gt hi) with q|rfl
        · exact False.elim (wne q)
        · rw [B.explicit,zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private theorem adjacent_read (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (adj : B.pivot.val=F.pivot.val+1) (j k : Nat) :
    row B.v (mixed A j k F.v) =
      (B.v B.pivot * A B.pivot F.pivot * F.v F.pivot)
        *(nodes A B.pivot)^k*(nodes A F.pivot)^j := by
  rw [row_apply,dotProduct,Finset.sum_eq_single B.pivot]
  · simp only [mixed,LinearMap.comp_apply,clockAct,diag_apply,Pi.pow_apply]
    have a := adjacent_inner ha F B adj j
    change mat A (diag ((nodes A)^j) F.v) B.pivot = _ at a
    rw [a]
    ring
  · intro u _ une
    by_cases h : B.pivot < u
    · rw [B.after u h,zero_mul]
    · have le : u.val ≤ B.pivot.val := le_of_not_gt h
      have lt : u.val < B.pivot.val := lt_of_le_of_ne le (fun eq => une (Fin.ext eq))
      have ui : u ≤ F.pivot := show u.val ≤ F.pivot.val by omega
      have z := mat_vanish_through ha (clock_seed_before F j) F.explicit ui
      change B.v u * (clockAct A k (mat A (clockAct A j F.v))) u=0
      rw [clockAct,diag_apply,z,mul_zero,mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private theorem adjacent_plain (F : FrontSeed A) (B : BackSeed A b)
    (adj : B.pivot.val=F.pivot.val+1) (same : nodes A B.pivot=nodes A F.pivot) (k : Nat) :
    row B.v (clockAct A k F.v) =
      (row B.v F.v)*(nodes A F.pivot)^k := by
  simp only [row_apply,dotProduct,Finset.sum_mul,clockAct,diag_apply,Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hi : u < F.pivot
  · rw [F.before u hi]
    ring
  · by_cases hj : B.pivot < u
    · rw [B.after u hj]
      ring
    · rcases adjacent_cases adj (le_of_not_gt hi) (le_of_not_gt hj) with rfl|rfl
      · ring
      · rw [same]
        ring

private theorem adjacent_double_zero (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (adj : B.pivot.val=F.pivot.val+1) :
    row B.v (mat A (mat A F.v))=0 := by
  rw [row_apply,dotProduct]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hi : B.pivot < u
  · rw [B.after u hi,zero_mul]
  · have up : u ≤ B.pivot := le_of_not_gt hi
    have z : mat A (mat A F.v) u=0 := by
      apply mat_vanish_through ha _ B.explicit up
      intro w hw
      have v : w.val < B.pivot.val := hw
      have wp : w ≤ F.pivot := by
        change w.val ≤ F.pivot.val
        omega
      exact mat_vanish_through ha F.before F.explicit wp
    rw [z,mul_zero]

private theorem back_volterra_paid_zero (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) :
    row B.v (volterra A F.v)=0 := by
  have p := volterra_treeSpace ho 3 (by decide) (front_is_tree F)
  have tre := zeroSpace_le_treeSpace _ _ p
  have d := reflectedStageRow_treeSpace ho 5 2 (by decide) tre
  change row (reflectedStageRow A b 2) (volterra A F.v)=0 at d
  rw [B.form]
  simp only [row_apply,add_dotProduct,smul_dotProduct,smul_eq_mul]
  rw [show (reflectedStageRow A b 2) ⬝ᵥ volterra A F.v=0 from d,mul_zero,add_zero]
  change row (diag b (coeffEval A 3 B.a)) (volterra A F.v)=0
  rw [profile_row S B]
  have w (n : Nat) (hn : n≤3) : probe A b n (volterra A F.v)=0 :=
    probe_zeroSpace ho (by omega) p
  rw [w 0 (by decide),w 1 (by decide),w 2 (by decide),w 3 (by decide)]
  ring

private theorem adjacent_same_clock (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b)
    (adj : B.pivot.val=F.pivot.val+1) :
    (B.v B.pivot * A B.pivot F.pivot * F.v F.pivot) ≠ 0 ∧
      nodes A B.pivot=nodes A F.pivot := by
  set d := B.v B.pivot * A B.pivot F.pivot * F.v F.pivot
  have dn : d≠0 := by
    intro z
    exact no_all_zero_mixes ho S F B (fun j k => by
      rw [adjacent_read ha F B adj,show B.v B.pivot * A B.pivot F.pivot * F.v F.pivot=d from rfl,
        z,zero_mul,zero_mul])
  have vk := back_volterra_paid_zero ho S F B
  have id0 (v : Fin 11 → K) : clockAct A 0 v=v := by ext i; simp [clockAct]
  have id1 (v : Fin 11 → K) : clockAct A 1 v=diag (nodes A) v := by simp [clockAct]
  have eq (j k : Nat) :
      row B.v (clockAct A k (mat A (clockAct A j F.v))) =
        d*(nodes A B.pivot)^k*(nodes A F.pivot)^j :=
    adjacent_read ha F B adj j k
  change row B.v (diag (nodes A) (mat A F.v) - mat A (diag (nodes A) F.v)
    - mat A (mat A F.v))=0 at vk
  rw [map_sub,map_sub,adjacent_double_zero ha F B adj,sub_zero,←id1,←id1] at vk
  have x := eq 0 1
  have y := eq 1 0
  rw [id0,pow_zero,pow_one,mul_one] at x y
  rw [x,y] at vk
  have e : d*(nodes A B.pivot - nodes A F.pivot)=0 := by linear_combination vk
  exact ⟨dn,sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left dn)⟩

private def adjacent_products (F : FrontSeed A) (B : BackSeed A b) (i : Fin 9) : K :=
  if i=0 then F.a 1*h B else if i=1 then F.a 1*l B else if i=2 then F.a 1*m B
  else if i=3 then F.a 2*h B else if i=4 then F.a 2*l B else if i=5 then F.a 2*m B
  else if i=6 then F.a 3*h B else if i=7 then F.a 3*l B else F.a 3*m B

private theorem adjacent_products_rankone (F : FrontSeed A) (B : BackSeed A b) :
    AdjacentCubicScalar.RankOne (adjacent_products F B) := by
  constructor <;> norm_num [adjacent_products] <;> ring

private theorem adjacent_products_live (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) :
    ∃ i, adjacent_products F B i≠0 := by
  rcases front_coeffs_live F with h1|h2|h3 <;> rcases back_coeffs_live S B with hh|hl|hm
  · exact ⟨0,by simpa [adjacent_products] using mul_ne_zero h1 hh⟩
  · exact ⟨1,by simpa [adjacent_products] using mul_ne_zero h1 hl⟩
  · exact ⟨2,by simpa [adjacent_products] using mul_ne_zero h1 hm⟩
  · exact ⟨3,by simpa [adjacent_products] using mul_ne_zero h2 hh⟩
  · exact ⟨4,by simpa [adjacent_products] using mul_ne_zero h2 hl⟩
  · exact ⟨5,by simpa [adjacent_products] using mul_ne_zero h2 hm⟩
  · exact ⟨6,by simpa [adjacent_products] using mul_ne_zero h3 hh⟩
  · exact ⟨7,by simpa [adjacent_products] using mul_ne_zero h3 hl⟩
  · exact ⟨8,by simpa [adjacent_products] using mul_ne_zero h3 hm⟩

set_option maxHeartbeats 1000000 in
private theorem adjacent_impossible (ha : A.IsLowerTriangular)
    (ho : HasOrder 10 A b) (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b)
    (adj : B.pivot.val=F.pivot.val+1) : False := by
  let x := nodes A F.pivot
  let u := adjacent_products F B
  let d := B.v B.pivot * A B.pivot F.pivot * F.v F.pivot
  let V := CrossedCubicPivot.moment (mu K) (h B) (l B) (m B)
  let L (k : Nat) := F.a 1*V (k+1) + F.a 2*V (k+2) + F.a 3*V (k+3)
  let J (j k : Nat) := F.a 1*mu K (j+1)*V (j+k+2) + F.a 2*mu K (j+2)*V (j+k+3) +
        F.a 3*mu K (j+3)*V (j+k+4)
  obtain ⟨_,same⟩ := adjacent_same_clock ha ho S F B adj
  have lEq (k : Nat) (paid : k≤3) : L k = (row B.v F.v)*x^k :=
    (plain_read ho S F B k paid).symm.trans (adjacent_plain F B adj same k)
  have mEq (j k : Nat) (paid : j+k≤2) : J j k = d*x^(j+k) := by
    rw [show J j k = row B.v (mixed A j k F.v) from (mix_read ho S F B j k paid).symm]
    rw [adjacent_read ha F B adj,same,pow_add]
    dsimp only [x,d]
    ring
  have lStep (k : Nat) (paid : k ≤ 2) : L (k+1)-x*L k=0 := by
    rw [lEq (k+1) (by omega),lEq k (by omega),pow_succ]
    ring
  have j3 : J 0 1-x*J 0 0=0 := by rw [mEq 0 1 (by decide),mEq 0 0 (by decide)]; ring
  have j4 : J 1 0-J 0 1=0 := by rw [mEq 1 0 (by decide),mEq 0 1 (by decide)]; ring
  have j5 : J 0 2-x*J 0 1=0 := by rw [mEq 0 2 (by decide),mEq 0 1 (by decide)]; ring
  have j6 : J 1 1-J 0 2=0 := by rw [mEq 1 1 (by decide),mEq 0 2 (by decide)]; ring
  have j7 : J 2 0-J 0 2=0 := by rw [mEq 2 0 (by decide),mEq 0 2 (by decide)]; ring
  have nz2 : (2:K) ≠ 0 := (ho.natCast_isUnit (n:=2) (by decide) (by decide)).ne_zero
  have nz3 : (3:K) ≠ 0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have nz4 : (4:K) ≠ 0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have nz5 : (5:K) ≠ 0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have nz6 : (6:K) ≠ 0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have nz7 : (7:K) ≠ 0 := (ho.natCast_isUnit (n:=7) (by decide) (by decide)).ne_zero
  have nz8 : (8:K) ≠ 0 := (ho.natCast_isUnit (n:=8) (by decide) (by decide)).ne_zero
  have nz9 : (9:K) ≠ 0 := (ho.natCast_isUnit (n:=9) (by decide) (by decide)).ne_zero
  have nz10 : (10:K) ≠ 0 := (ho.natCast_isUnit (n:=10) (by decide) (by decide)).ne_zero
  have r0 : AdjacentCubicScalar.row0 x u=0 := by
    calc
      _ = (840:K)*(L 1-x*L 0) := by
        norm_num [AdjacentCubicScalar.row0,u,adjacent_products,L,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [lStep 0 (by decide),mul_zero]
  have r1 : AdjacentCubicScalar.row1 x u=0 := by
    calc
      _ = (2520:K)*(L 2-x*L 1) := by
        norm_num [AdjacentCubicScalar.row1,u,adjacent_products,L,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [lStep 1 (by decide),mul_zero]
  have r2 : AdjacentCubicScalar.row2 x u=0 := by
    calc
      _ = (2520:K)*(L 3-x*L 2) := by
        norm_num [AdjacentCubicScalar.row2,u,adjacent_products,L,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [lStep 2 (by decide),mul_zero]
  have r3 : AdjacentCubicScalar.row3 x u=0 := by
    calc
      _ = (10080:K)*(J 0 1-x*J 0 0) := by
        norm_num [AdjacentCubicScalar.row3,u,adjacent_products,J,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [j3,mul_zero]
  have r4 : AdjacentCubicScalar.row4 x u=0 := by
    calc
      _ = (10080:K)*(J 1 0-J 0 1) := by
        norm_num [AdjacentCubicScalar.row4,u,adjacent_products,J,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [j4,mul_zero]
  have r5 : AdjacentCubicScalar.row5 x u=0 := by
    calc
      _ = (30240:K)*(J 0 2-x*J 0 1) := by
        norm_num [AdjacentCubicScalar.row5,u,adjacent_products,J,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [j5,mul_zero]
  have r6 : AdjacentCubicScalar.row6 x u=0 := by
    calc
      _ = (151200:K)*(J 1 1-J 0 2) := by
        norm_num [AdjacentCubicScalar.row6,u,adjacent_products,J,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [j6,mul_zero]
  have r7 : AdjacentCubicScalar.row7 x u=0 := by
    calc
      _ = (30240:K)*(J 2 0-J 0 2) := by
        norm_num [AdjacentCubicScalar.row7,u,adjacent_products,J,V,CrossedCubicPivot.moment,mu]
        field_simp [nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,nz10]
        ring
      _ = 0 := by rw [j7,mul_zero]

  have z := AdjacentCubicScalar.zero_of_tests ⟨nz2,nz3,nz5,nz7⟩ x u
    ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩ (adjacent_products_rankone F B)
  obtain ⟨i,ine⟩ := adjacent_products_live S F B
  exact ine (z i)

/-- The two interior zero diagonals have at least one physical row
strictly between them. No assumption on its diagonal or weights is used. -/
theorem crossed_zero_sites_buffer (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    ∃ i j : Fin 11, 0 < i ∧ i.val+2 ≤ j.val ∧ j < Fin.last 10 ∧
      A 0 0=0 ∧ A i i=0 ∧ A j j=0 ∧ A (Fin.last 10) (Fin.last 10)=0 := by
  let S := saturated ha ho
  let F := Classical.choice (exists_front_seed ha ho S)
  let B := Classical.choice (exists_back_seed ha ho S)
  have lt : F.pivot.val < B.pivot.val := ordered_pivots ha ho S F B
  have nq : B.pivot.val ≠ F.pivot.val+1 := adjacent_impossible ha ho S F B
  refine ⟨F.pivot,B.pivot,F.interior,by omega,B.interior,
    S.physical_origin 0,F.explicit,B.explicit,S.last_column _⟩

/-- Spatial ring consequence under the same residue-field transport:
the two interior nonunit diagonals are not consecutive. -/
theorem crossed_nonunit_sites_buffer {R : Type*} [CommRing R] [Nontrivial R]
    {D : Matrix (Fin 11) (Fin 11) R} {w : Fin 11 → R}
    (ha : D.IsLowerTriangular) (ho : HasOrder 10 D w) :
    ∃ i j : Fin 11, 0 < i ∧ i.val+2 ≤ j.val ∧ j < Fin.last 10 ∧
      ¬IsUnit (D 0 0) ∧ ¬IsUnit (D i i) ∧ ¬IsUnit (D j j)
        ∧ ¬IsUnit (D (Fin.last 10) (Fin.last 10)) := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  obtain ⟨i,j,hi,hij,hj,e0,ei,ej,et⟩ := crossed_zero_sites_buffer (ha.map f) (ho.map f)
  have n (k : Fin 11) (die : f (D k k)=0) : ¬IsUnit (D k k) :=
    fun hu => (hu.map f).ne_zero die
  exact ⟨i,j,hi,hij,hj,n 0 e0,n i ei,n j ej,n _ et⟩

private theorem no_geometric_overlap (ho : HasOrder 10 A b) (S : Saturated A b)
    (F : FrontSeed A) (B : BackSeed A b) (x eta T U W : K)
    (L : ∀ k : Nat, row B.v (clockAct A k F.v)=T*x^k+U*eta^k)
    (J : ∀ j k : Nat, row B.v (mixed A j k F.v)=W*x^(j+k)) : False := by
  have nw : W≠0 := by
    intro h
    exact no_all_zero_mixes ho S F B (fun j k => by rw [J j k,h,zero_mul])
  let M := CrossedCubicPivot.moment (mu K) (h B) (l B) (m B)
  have mEq (j k : Nat) (paid : j+k ≤ 2) :
      F.a 1*mu K (j+1)*M (j+k+2)+F.a 2*mu K (j+2)*M (j+k+3)
        +F.a 3*mu K (j+3)*M (j+k+4)=W*x^(j+k) :=
    (mix_read ho S F B j k paid).symm.trans (J j k)
  have row0 (k : Nat) (hk : k ≤ 2) :
      6*(F.a 1*M (k+2))+4*(F.a 2*M (k+3))+3*(F.a 3*M (k+4))=12*W*x^k := by
    have e := mEq 0 k (by omega)
    simp only [Nat.zero_add] at e
    have e1 : (12:K)*mu K 1=6 := scale_mu ho 12 6 1 (by decide) (by decide)
    have e2 : (12:K)*mu K 2=4 := scale_mu ho 12 4 2 (by decide) (by decide)
    have e3 : (12:K)*mu K 3=3 := scale_mu ho 12 3 3 (by decide) (by decide)
    rw [←e1,←e2,←e3]
    linear_combination 12*e
  have row1 (k : Nat) (hk : k ≤ 1) :
      20*(F.a 1*M (1+k+2))+15*(F.a 2*M (1+k+3))+12*(F.a 3*M (1+k+4))=60*W*x^(1+k) := by
    have e := mEq 1 k (by omega)
    have e1 : (60:K)*mu K 2=20 := scale_mu ho 60 20 2 (by decide) (by decide)
    have e2 : (60:K)*mu K 3=15 := scale_mu ho 60 15 3 (by decide) (by decide)
    have e3 : (60:K)*mu K 4=12 := scale_mu ho 60 12 4 (by decide) (by decide)
    rw [←e1,←e2,←e3]
    linear_combination 60*e
  have row2 : 15*(F.a 1*M 4)+12*(F.a 2*M 5)+10*(F.a 3*M 6)=60*W*x^2 := by
    have e := mEq 2 0 (by decide)
    have e1 : (60:K)*mu K 3=15 := scale_mu ho 60 15 3 (by decide) (by decide)
    have e2 : (60:K)*mu K 4=12 := scale_mu ho 60 12 4 (by decide) (by decide)
    have e3 : (60:K)*mu K 5=10 := scale_mu ho 60 10 5 (by decide) (by decide)
    rw [←e1,←e2,←e3]
    linear_combination 60*e
  have eq : TwoClockPrimitive.Geometric (F.a 1) (F.a 2) (F.a 3) M W x :=
    ⟨by simpa only [pow_zero,mul_one] using row0 0 (by decide),
      by simpa only [pow_one] using row0 1 (by decide),
      by simpa only [Nat.add_zero,pow_one] using row1 0 (by decide),
      row0 2 (by decide),row1 1 (by decide),row2⟩
  have p (k : Nat) (paid : k≤3) :
      TwoClockPrimitive.plain (F.a 1) (F.a 2) (F.a 3) M k=T*x^k+U*eta^k :=
    (plain_read ho S F B k paid).symm.trans (L k)
  have z := TwoClockPrimitive.no_two_clock_geometric (mu K) (mu_paid ho)
    (F.a 1) (F.a 2) (F.a 3) (h B) (l B) (m B) W x eta T U nw (front_coeffs_live F) eq p
  rcases back_coeffs_live S B with h|l|m
  · exact h z.1
  · exact l z.2.1
  · exact m z.2.2

private theorem triplet_cases {i k j u : Fin 11} (ik : k.val=i.val+1)
    (kj : j.val=k.val+1) (hu : i ≤ u) (uj : u ≤ j) : u=i ∨ u=k ∨ u=j := by
  have t1 : i.val ≤ u.val := hu
  have t2 : u.val ≤ j.val := uj
  rcases (show u.val=i.val ∨ u.val=k.val ∨ u.val=j.val by omega) with h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem triple_mat_middle (ha : A.IsLowerTriangular) {i k : Fin 11}
    (ik : k.val=i.val+1) (v : Fin 11→K) (pre : ∀ t < i, v t=0) :
    mat A v k=A k i*v i+A k k*v k := by
  classical
  have lt : i < k := show i.val<k.val by omega
  have ni := ne_of_lt lt
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  calc
    _ = ∑ t∈({i,k}:Finset (Fin 11)), A k t*v t := by
      symm
      apply Finset.sum_subset (by simp)
      intro u _ nu
      by_cases hi : u < i
      · rw [pre u hi,mul_zero]
      · by_cases hk : k < u
        · rw [ha hk,zero_mul]
        · rcases adjacent_cases ik (le_of_not_gt hi) (le_of_not_gt hk) with h|h
          · subst u
            exact False.elim (nu (by simp))
          · subst u
            exact False.elim (nu (by simp))
    _ = _ := by simp [ni]

private theorem triple_mat_last (ha : A.IsLowerTriangular) {i k j : Fin 11}
    (ik : k.val=i.val+1) (kj : j.val=k.val+1)
    (v : Fin 11→K) (pre : ∀ t < i, v t=0) (d : A j j=0) :
    mat A v j=A j i*v i+A j k*v k := by
  classical
  have lt : i < k := show i.val<k.val by omega
  have ni := ne_of_lt lt
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  calc
    _ = ∑ t∈({i,k}:Finset (Fin 11)), A j t*v t := by
      symm
      apply Finset.sum_subset (by simp)
      intro u _ nu
      by_cases hi : u < i
      · rw [pre u hi,mul_zero]
      · by_cases hj : j < u
        · rw [ha hj,zero_mul]
        · rcases triplet_cases ik kj (le_of_not_gt hi) (le_of_not_gt hj) with rfl|rfl|rfl
          · exact False.elim (nu (by simp))
          · exact False.elim (nu (by simp))
          · rw [d,zero_mul]
    _ = _ := by simp [ni]

private theorem triple_transpose_middle (ha : A.IsLowerTriangular) {k j : Fin 11}
    (kj : j.val=k.val+1) (v : Fin 11→K) (after : ∀ t, j < t → v t=0) :
    mat A.transpose v k=A k k*v k+A j k*v j := by
  classical
  have lt : k < j := show k.val<j.val by omega
  have ni := ne_of_lt lt
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  calc
    _ = ∑ t∈({k,j}:Finset (Fin 11)), A t k*v t := by
      symm
      apply Finset.sum_subset (by simp)
      intro u _ nu
      by_cases hk : u < k
      · rw [ha hk,zero_mul]
      · by_cases hj : j < u
        · rw [after u hj,mul_zero]
        · rcases adjacent_cases kj (le_of_not_gt hk) (le_of_not_gt hj) with h|h
          · subst u
            exact False.elim (nu (by simp))
          · subst u
            exact False.elim (nu (by simp))
    _ = _ := by simp [ni]

private theorem triple_observe {i k j : Fin 11}
    (ik : k.val=i.val+1) (kj : j.val=k.val+1) (l v : Fin 11→K)
    (pre : ∀ t < i, v t=0) (after : ∀ t, j < t → l t=0) :
    row l v=l i*v i+l k*v k+l j*v j := by
  classical
  have lt : i < k := show i.val<k.val by omega
  have lj : k < j := show k.val<j.val by omega
  rw [row_apply,dotProduct]
  calc
    _ = ∑ t∈({i,k,j}:Finset (Fin 11)), l t*v t := by
      symm
      apply Finset.sum_subset (by simp)
      intro u _ nu
      by_cases hi : u < i
      · rw [pre u hi,mul_zero]
      · by_cases hj : j < u
        · rw [after u hj,zero_mul]
        · rcases triplet_cases ik kj (le_of_not_gt hi) (le_of_not_gt hj) with h|h|h
          · subst u
            exact False.elim (nu (by simp))
          · subst u
            exact False.elim (nu (by simp))
          · subst u
            exact False.elim (nu (by simp))
    _ = _ := by
      simp [ne_of_lt lt,ne_of_lt lj,ne_of_lt (lt.trans lj)]
      ring

private def triple_packet (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11) :
    ThreeStageOverlap.Packet K where
  x := nodes A F.pivot
  y := nodes A k
  z := nodes A B.pivot
  d := A k k
  p := A k F.pivot
  q := A B.pivot k
  w := A B.pivot F.pivot
  f := F.v F.pivot
  g := F.v k
  h := F.v B.pivot
  alpha := B.v F.pivot
  beta := B.v k
  gamma := B.v B.pivot

private theorem triple_clipped_plain (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11)
    (ik : k.val=F.pivot.val+1) (kj : B.pivot.val=k.val+1) (r : Nat) :
    row B.v (clockAct A r F.v)=(triple_packet F B k).plain r := by
  rw [triple_observe ik kj _ _ (clock_seed_before F r) B.after]
  simp only [ThreeStageOverlap.Packet.plain,triple_packet,clockAct,diag_apply,Pi.pow_apply]
  ring

private theorem triple_clipped_primitive (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11)
    (ik : k.val=F.pivot.val+1) (kj : B.pivot.val=k.val+1) (r s : Nat) :
    row B.v (mixed A r s F.v)=(triple_packet F B k).primitive r s := by
  have pre : ∀ t < F.pivot, mixed A r s F.v t=0 := by
    intro t tl
    have f := mat_vanish_through ha (clock_seed_before F r) F.explicit tl.le
    simp only [mixed,LinearMap.comp_apply,clockAct,diag_apply] at f ⊢
    rw [f,mul_zero]
  rw [triple_observe ik kj _ _ pre B.after]
  have e0 := mat_vanish_through ha (clock_seed_before F r) F.explicit (u:=F.pivot) le_rfl
  have e1 := triple_mat_middle ha ik (clockAct A r F.v) (clock_seed_before F r)
  have e2 := triple_mat_last ha ik kj (clockAct A r F.v) (clock_seed_before F r) B.explicit
  simp only [mixed,LinearMap.comp_apply,clockAct,diag_apply] at e0 e1 e2 ⊢
  rw [e0,e1,e2]
  simp only [ThreeStageOverlap.Packet.primitive,triple_packet,Pi.pow_apply]
  ring

private theorem triple_kernel_cut (ha : A.IsLowerTriangular)
    (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11)
    (ik : k.val=F.pivot.val+1) (kj : B.pivot.val=k.val+1) :
    ThreeStageOverlap.KernelCut (triple_packet F B k) := by
  let N := diag (nodes A)
  let Y := diag (reflectedClock A)
  let L := mat A
  let T := mat A.transpose
  have nv : ∀ t < F.pivot, N F.v t=0 := by
    intro t ht
    simp only [N,diag_apply,F.before t ht,mul_zero]
  have lv0 : L F.v F.pivot=0 := mat_vanish_through ha F.before F.explicit le_rfl
  have lv : ∀ t < F.pivot, L F.v t=0 := by
    intro t ht
    exact mat_vanish_through ha F.before F.explicit ht.le
  have yv : ∀ t, B.pivot < t → Y B.v t=0 := by
    intro t ht
    simp only [Y,diag_apply,B.after t ht,mul_zero]
  have tv : ∀ t, B.pivot < t → T B.v t=0 := by
    intro t ht
    change mat A.transpose B.v t=0
    rw [transpose_mat_pivot ha t _ (fun u hu => B.after u (ht.trans hu)),B.after t ht,mul_zero]
  have tv0 : T B.v B.pivot=0 := by
    change mat A.transpose B.v B.pivot=0
    rw [transpose_mat_pivot ha B.pivot _ B.after,B.explicit,zero_mul]
  have g1 := triple_mat_middle ha ik F.v F.before
  have can := triple_mat_middle ha ik (N F.v) nv
  have gan := triple_mat_middle ha ik (L F.v) lv
  have g2 := triple_mat_last ha ik kj F.v F.before B.explicit
  have can2 := triple_mat_last ha ik kj (N F.v) nv B.explicit
  have gan2 := triple_mat_last ha ik kj (L F.v) lv B.explicit
  have d1 := triple_transpose_middle ha kj B.v B.after
  have yd := triple_transpose_middle ha kj (Y B.v) yv
  have dd := triple_transpose_middle ha kj (T B.v) tv
  have H1 := congrFun F.kernel k
  have H2 := congrFun B.kernel k
  have H3 := congrFun F.kernel B.pivot
  refine ⟨F.live,B.live,?_,?_,?_⟩
  · change (N (L F.v) k-L (N F.v) k-L (L F.v) k)=0 at H1
    change L F.v k=_ at g1
    change L (N F.v) k=_ at can
    change L (L F.v) k=_ at gan
    unfold N at H1
    rw [diag_apply] at H1
    change nodes A k*L F.v k-L (N F.v) k-L (L F.v) k=0 at H1
    rw [can,gan,g1,lv0] at H1
    simp only [N,diag_apply] at H1
    dsimp only [triple_packet]
    linear_combination H1
  · change (Y (T B.v) k-T (Y B.v) k-T (T B.v) k)=0 at H2
    change T B.v k=_ at d1
    change T (Y B.v) k=_ at yd
    change T (T B.v) k=_ at dd
    unfold Y at H2
    rw [diag_apply] at H2
    change reflectedClock A k*T B.v k-T (Y B.v) k-T (T B.v) k=0 at H2
    rw [yd,dd,d1,tv0] at H2
    simp only [Y,diag_apply,reflectedClock,Pi.sub_apply,Pi.one_apply] at H2
    dsimp only [triple_packet]
    linear_combination H2
  · change (N (L F.v) B.pivot-L (N F.v) B.pivot-L (L F.v) B.pivot)=0 at H3
    change L F.v B.pivot=_ at g2
    change L (N F.v) B.pivot=_ at can2
    change L (L F.v) B.pivot=_ at gan2
    unfold N at H3
    rw [diag_apply] at H3
    change nodes A B.pivot*L F.v B.pivot-L (N F.v) B.pivot-L (L F.v) B.pivot=0 at H3
    rw [can2,gan2,g2,g1,lv0] at H3
    simp only [N,diag_apply] at H3
    dsimp only [triple_packet]
    linear_combination H3

private theorem forbidden_triple_shape (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11)
    (ik : k.val=F.pivot.val+1) (kj : B.pivot.val=k.val+1) :
    ¬ ((triple_packet F B k).NoPrimitive ∨ (triple_packet F B k).Geometric) := by
  intro e
  rcases e with n|v
  · exact no_all_zero_mixes ho S F B
      (fun j k' => (triple_clipped_primitive ha F B k ik kj j k').trans (n j k'))
  · obtain ⟨x,eta,T,U,W,q,p⟩ := v
    exact no_geometric_overlap ho S F B x eta T U W
      (fun r => (triple_clipped_plain F B k ik kj r).trans (q r))
      (fun j k' => (triple_clipped_primitive ha F B k ik kj j k').trans (p j k'))

private theorem required_middle (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) (F : FrontSeed A) (B : BackSeed A b) (k : Fin 11)
    (ik : k.val=F.pivot.val+1) (kj : B.pivot.val=k.val+1) :
    A k k≠0 ∧ A k F.pivot≠0 ∧ A B.pivot k≠0 ∧
      nodes A k≠nodes A F.pivot ∧ nodes A B.pivot≠nodes A k ∧
        nodes A B.pivot≠nodes A F.pivot := by
  have K := triple_kernel_cut ha F B k ik kj
  have no := forbidden_triple_shape ha ho S F B k ik kj
  have hd : A k k≠0 := fun h => no (ThreeStageOverlap.split_if_zero_middle _ K h)
  have hp : A k F.pivot≠0 :=
    fun h => no (ThreeStageOverlap.split_if_hop_missing _ K hd (Or.inl h))
  have hq : A B.pivot k≠0 :=
    fun h => no (ThreeStageOverlap.split_if_hop_missing _ K hd (Or.inr h))
  have first : nodes A k≠nodes A F.pivot :=
    fun h => no (ThreeStageOverlap.split_if_first_repeat _ K hd h)
  have last : nodes A B.pivot≠nodes A k :=
    fun h => no (ThreeStageOverlap.split_if_last_repeat _ K hd h)
  have outer : nodes A B.pivot≠nodes A F.pivot :=
    fun h => first (ThreeStageOverlap.middle_eq_of_outer_repeat _ K hp hq h)
  exact ⟨hd,hp,hq,first,last,outer⟩

/-- If just one stage lies between the two earned interior zero pivots,
it must be implicit, both neighboring taps must be live, and the three
clocks must be pairwise distinct. No other stage clock is constrained. -/
theorem crossed_zero_sites_three_stage (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    ∃ i j : Fin 11, 0 < i ∧ i.val+2 ≤ j.val ∧ j < Fin.last 10 ∧
      A 0 0=0 ∧ A i i=0 ∧ A j j=0 ∧ A (Fin.last 10) (Fin.last 10)=0 ∧
      (∀ k : Fin 11, k.val=i.val+1 → j.val=k.val+1 →
        A k k≠0 ∧ A k i≠0 ∧ A j k≠0 ∧
        nodes A k≠nodes A i ∧ nodes A j≠nodes A k ∧ nodes A j≠nodes A i) := by
  let S := saturated ha ho
  let F := Classical.choice (exists_front_seed ha ho S)
  let B := Classical.choice (exists_back_seed ha ho S)
  have lt : F.pivot.val < B.pivot.val := ordered_pivots ha ho S F B
  have nq : B.pivot.val ≠ F.pivot.val+1 := adjacent_impossible ha ho S F B
  exact ⟨F.pivot,B.pivot,F.interior,by omega,B.interior,
    S.physical_origin 0,F.explicit,B.explicit,S.last_column _,
    required_middle ha ho S F B⟩

/-- The same counted residue field witnesses nonzero taps and a
nonzero middle diagonal in the coefficient ring. No assertion is made
that these three entries must be units in the original ring. -/
theorem crossed_nonunit_sites_three_stage {R : Type*} [CommRing R] [Nontrivial R]
    {D : Matrix (Fin 11) (Fin 11) R} {w : Fin 11 → R}
    (ha : D.IsLowerTriangular) (ho : HasOrder 10 D w) :
    ∃ i j : Fin 11, 0 < i ∧ i.val+2 ≤ j.val ∧ j < Fin.last 10 ∧
      ¬IsUnit (D 0 0) ∧ ¬IsUnit (D i i) ∧ ¬IsUnit (D j j)
        ∧ ¬IsUnit (D (Fin.last 10) (Fin.last 10))
        ∧ (∀ k : Fin 11, k.val=i.val+1 → j.val=k.val+1 →
          D k k≠0 ∧ D k i≠0 ∧ D j k≠0 ∧
          nodes D k≠nodes D i ∧ nodes D j≠nodes D k ∧ nodes D j≠nodes D i) := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  obtain ⟨i,j,hi,hij,hj,e0,ei,ej,et,trip⟩ := crossed_zero_sites_three_stage (ha.map f) (ho.map f)
  have n (k : Fin 11) (die : f (D k k)=0) : ¬IsUnit (D k k) :=
    fun hu => (hu.map f).ne_zero die
  refine ⟨i,j,hi,hij,hj,n 0 e0,n i ei,n j ej,n _ et,?_⟩
  intro k ik kj
  obtain ⟨hd,hp,hq,first,last,outer⟩ := trip k ik kj
  have nonzero {x : R} (hz : f x≠0) : x≠0 := fun e => hz (e ▸ map_zero f)
  have clock_map (u : Fin 11) : nodes (D.map f) u=f (nodes D u) := by
    simp [nodes,Matrix.mulVec_apply_eq_sum,map_sum]
  have pull {u v : Fin 11} (nn : nodes (D.map f) u≠nodes (D.map f) v) :
      nodes D u≠nodes D v := fun e => nn (by rw [clock_map,clock_map,e])
  exact ⟨nonzero hd,nonzero hp,nonzero hq,pull first,pull last,pull outer⟩

end
end RKResearch.Certified.Graded.CrossedOrderTen
