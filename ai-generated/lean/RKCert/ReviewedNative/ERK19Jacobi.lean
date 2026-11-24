module

public import RKCert.ReviewedNative.ERK19Midpoint
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! # Consecutive native Jacobi aliases on the nonzero order-19 branch

A positive grade-eleven surplus is *not* needed as a premise to obtain
the second alias. A single paid primitive and one clock shift of the
grade-ten alias suffice. Both vectors are genuine physical defects. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse
noncomputable section

section Detection
variable {K : Type*} [Field K] {n q j p : ℕ}
variable {A : Matrix (Fin (n+1)) (Fin (n+1)) K} {b : Fin (n+1)→K}

private theorem coeff_by_origin_probes (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder p A b) (budget : 2*q≤p) (a : Fin (q+1)→K)
    (h0 : coeffEval A q a 0=0)
    (hit : ∀i : Fin q, probe A b i.val (coeffEval A q a)=0) : a=0 := by
  rw [coeffEval_origin ha] at h0
  have hz (i : Fin q) : (∑ t : Fin q, a t.succ/((i.val+t.val+2:ℕ):K))=0 := by
    have m := hit i
    rw [probe_coeffEval ho (by have := i.isLt; omega),
      Fin.sum_univ_succ,h0,zero_div,zero_add] at m
    simpa only [Fin.val_succ,Nat.add_assoc] using m
  have out := moments_detect ho (n:=q) (d:=2) (by decide) (by omega)
    (fun i t => by have := i.isLt; have := t.isLt; omega) _ hz
  ext i
  exact Fin.cases h0 out i

theorem paid_origin_coeff_separation (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder p A b) (budget : 2*q≤p) (pay : q+j≤p)
    (a : Fin (q+1)→K) (mem : coeffEval A q a∈zeroSpace A j) : a=0 :=
  coeff_by_origin_probes ha ho budget a (origin_zeroSpace ha _ mem)
    (fun i => probe_zeroSpace ho (by have := i.isLt; omega) mem)

/-- Under numerical band saturation, a zero physical origin and the
actual available output probes identify the entire pure component. -/
theorem pure_of_paid_probes (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder p A b) (budget : 2*q≤p) (pay : q+j≤p) {v : Fin (n+1)→K}
    (mem : v∈(coeffEval A q).range ⊔ zeroSpace A j) (h0 : v 0=0)
    (hit : ∀i : Fin q, probe A b i.val v=0) : v∈zeroSpace A j := by
  obtain ⟨_,⟨a,rfl⟩,w,hw,rfl⟩ := Submodule.mem_sup.mp mem
  change coeffEval A q a 0 + w 0 = 0 at h0
  have w0 : w 0 = 0 := origin_zeroSpace ha j hw
  rw [w0,add_zero] at h0
  have z := coeff_by_origin_probes ha ho budget a h0 (fun i => by
    have h := hit i
    have wq : probe A b i.val w = 0 := probe_zeroSpace ho (by have := i.isLt; omega) hw
    rw [map_add,wq,add_zero] at h
    exact h)
  rw [z,map_zero,zero_add]
  exact hw

end Detection

section Arithmetic
variable {K : Type*} [Field K]

/-- Coefficients, in ascending order, of x times the shifted Jacobi
polynomial of degree nine for the weight x dx (integer scaling). -/
def mesh9Data (K : Type*) [Ring K] : Fin 11→K :=
  ![0,-10,495,-7920,60060,-252252,630630,-960960,875160,-437580,92378]

def mesh8Data (K : Type*) [Ring K] : Fin 11→K :=
  ![0,9,-360,4620,-27720,90090,-168168,180180,-102960,24310,0]

def mesh9 (K : Type*) [Field K] : K[X] := by classical exact ofFn 11 (mesh9Data K)
def mesh8 (K : Type*) [Field K] : K[X] := by classical exact ofFn 11 (mesh8Data K)

private theorem mesh9_coeff (n : ℕ) : (mesh9 K).coeff n =
    if h : n < 11 then mesh9Data K ⟨n,h⟩ else 0 := by
  classical
  split <;> rename_i h
  · exact ofFn_coeff_eq_val_of_lt _ h
  · exact ofFn_coeff_eq_zero_of_ge _ (by omega)

private theorem mesh8_coeff (n : ℕ) : (mesh8 K).coeff n =
    if h : n < 11 then mesh8Data K ⟨n,h⟩ else 0 := by
  classical
  split <;> rename_i h
  · exact ofFn_coeff_eq_val_of_lt _ h
  · exact ofFn_coeff_eq_zero_of_ge _ (by omega)

theorem mesh9_degree [CharZero K] : (mesh9 K).natDegree=10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun _ h => by rw [mesh9_coeff,dite_eq_right (by omega)]
  · norm_num [mesh9_coeff,mesh9Data]

set_option maxHeartbeats 900000 in
private theorem mesh9_moment_sum [CharZero K] (i : Fin 9) :
    (∑ t : Fin 11, mesh9Data K t / ((i.val+t.val+1:ℕ):K))=0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ,mesh9Data]

set_option maxHeartbeats 900000 in
/-- A paid primitive and a paid clock shift propagate the exact
lower-degree alias. No grade-eleven dimension bound is an input. -/
theorem jacobi_primitive_step [CharZero K] :
    (10:K) • mesh8 K =
      (19:K) • (X*mesh9 K) - (9:K) • mesh9 K - (209:K) • primitive (mesh9 K) := by
  ext n
  cases n with
  | zero => norm_num [AddMonoidAlgebra.coeff_smul_apply,mesh9_coeff,mesh8_coeff,mesh9Data,mesh8Data]
  | succ k =>
    simp only [AddMonoidAlgebra.coeff_smul_apply,coeff_sub,coeff_X_mul,primitive_coeff_succ,smul_eq_mul]
    by_cases h : k < 11
    · interval_cases k <;> norm_num [mesh9_coeff,mesh8_coeff,mesh9Data,mesh8Data]
    · rw [mesh8_coeff,dite_eq_right (by omega),mesh9_coeff,dite_eq_right h,
        mesh9_coeff,dite_eq_right (by omega)]
      simp

def jacobi9At (x : K) : K :=
  92378*x^9-437580*x^8+875160*x^7-960960*x^6+630630*x^5-
    252252*x^4+60060*x^3-7920*x^2+495*x-10

def jacobi8At (x : K) : K :=
  24310*x^8-102960*x^7+180180*x^6-168168*x^5+
    90090*x^4-27720*x^3+4620*x^2-360*x+9

private theorem mesh9_eval (x : K) : (mesh9 K).eval x = x*jacobi9At x := by
  classical
  rw [mesh9,ofFn_eq_sum_monomial,eval_finsetSum]
  simp [Fin.sum_univ_succ,mesh9Data,jacobi9At]
  ring

private theorem mesh8_eval (x : K) : (mesh8 K).eval x = x*jacobi8At x := by
  classical
  rw [mesh8,ofFn_eq_sum_monomial,eval_finsetSum]
  simp [Fin.sum_univ_succ,mesh8Data,jacobi8At]
  ring

/-- Tiny integer Bézout certificate for the fixed adjacent pair. -/
private theorem jacobi_no_common [CharZero K] {x : K} (a : jacobi9At x = 0)
    (b : jacobi8At x = 0) : False := by
  let U := -15315300*x^7+54654600*x^6-77927850*x^5+56576520*x^4-
    22042020*x^3+4439160*x^2-402039*x+11200
  let V := 58198140*x^8-236876640*x^7+396666270*x^6-352396044*x^5+
    178498320*x^4-51480000*x^3+7947225*x^2-563750*x+12474
  have e : U*jacobi9At x+V*jacobi8At x=266 := by
    dsimp [U,V,jacobi9At,jacobi8At]
    ring
  rw [a,b,mul_zero,mul_zero,add_zero] at e
  exact (by norm_num : (0:K)≠266) e

end Arithmetic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

/-- The actual nonzero-seed hypothesis suffices for the degree-ten
Jacobi alias, not merely the formal finite moment tests on a polynomial. -/
theorem nonzero_seed_first_alias (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) : evalNodes A (mesh9 K) ∈ zeroSpace A 10 := by
  have ev : evalNodes A (mesh9 K) = coeffEval A 10 (mesh9Data K) := by
    rw [evalNodes_eq_coeffEval A (mesh9 K) (mesh9_degree.le)]
    congr 1
    funext t
    rw [mesh9_coeff,dite_eq_left t.isLt]
  have he := (nonzero_seed_grade_ten ha ho nz).2.2
  apply pure_of_paid_probes ha ho (q:=9) (by decide) (by decide)
  · rw [←he]
    exact evalNodes_mem_treeSpace A _ mesh9_degree.le
  · rw [ev,coeffEval_origin ha]
    rfl
  · intro i
    rw [ev,probe_coeffEval ho (by have := i.isLt; omega)]
    exact mesh9_moment_sum i

theorem nonzero_seed_adjacent_aliases (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) :
    evalNodes A (mesh9 K) ∈ zeroSpace A 10 ∧ evalNodes A (mesh8 K) ∈ zeroSpace A 11 := by
  have h := nonzero_seed_first_alias ha ho nz
  refine ⟨h,?_⟩
  have cx : evalNodes A (X*mesh9 K) ∈ zeroSpace A 11 := by
    have e : evalNodes A (X*mesh9 K)=diag (nodes A) (evalNodes A (mesh9 K)) := by ext i; simp
    rw [e]
    exact diag_zeroSpace A 10 h
  have m : evalNodes A (primitive (mesh9 K)) ∈ zeroSpace A 11 := by
    have d := primitive_defect A (mesh9 K) (q:=10) mesh9_degree.le
    have e := (zeroSpace A 11).sub_mem (mat_zeroSpace_charZero A 10 h) d
    simpa only [sub_sub_cancel] using e
  have e := congrArg (evalNodes A) (jacobi_primitive_step (K:=K))
  simp only [map_smul,map_sub] at e
  apply ((zeroSpace A 11).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr (by norm_num : (10:K)≠0))).mp
  rw [e]
  exact (zeroSpace A 11).sub_mem ((zeroSpace A 11).sub_mem ((zeroSpace A 11).smul_mem _ cx)
    ((zeroSpace A 11).smul_mem _ ((zeroSpace_mono A (by decide : 10≤11)) h)))
    ((zeroSpace A 11).smul_mem _ m)

/-- There can be no nonzero physical clock at which *all* grade-eleven
ordinary defects vanish. This is not a claim that such a row exists. -/
theorem nonzero_seed_clean_eleven_clock_zero (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) (i : Fin 29)
    (clean : ∀ w∈zeroSpace A 11, w i=0) : nodes A i=0 := by
  obtain ⟨p,q⟩ := nonzero_seed_adjacent_aliases ha ho nz
  have a := clean _ (zeroSpace_mono A (by decide : 10≤11) p)
  have b := clean _ q
  rw [evalNodes_apply,mesh9_eval] at a
  rw [evalNodes_apply,mesh8_eval] at b
  by_contra z
  exact jacobi_no_common ((mul_eq_zero.mp a).resolve_left z) ((mul_eq_zero.mp b).resolve_left z)

end
end RKResearch.Certified.ERK19
