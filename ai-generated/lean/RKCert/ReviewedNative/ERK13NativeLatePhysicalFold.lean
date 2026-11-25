module

public import RKCert.ReviewedNative.HyperplanePhysicalLabels
public import RKCert.ReviewedNative.ERK13NativePaidFrame
public import RKCert.ReviewedNative.NativeFinalThreeCausal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Physical 18-class transpose at the late width-19 seam

The class matrix retains the first original row in each marked class.
There is exactly one nonrepresentative `m`; the literal last stage is its
own class. This leaf does not assert order for the class matrix. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse HyperplaneTerminal NativeFinalThree
open scoped Classical Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {e : Fin 18 → Fin 19} {r : Fin 19 → Fin 18} {m : Fin 19}

structure PairClasses (e : Fin 18 → Fin 19) (r : Fin 19 → Fin 18) (m : Fin 19) : Prop where
  ordered : Monotone e
  earlier : ∀ i, e (r i) ≤ i
  omitted : e (r m) ≠ m
  kept : ∀ i, i ≠ m → e (r i) = i

/-- The genuine, not already grouped, difference of the only replaced row. -/
def rowDelta (A : Matrix (Fin 19) (Fin 19) K)
    (e : Fin 18 → Fin 19) (r : Fin 19 → Fin 18) (m : Fin 19) : Fin 19 → K :=
  fun i => A m i - A (e (r m)) i

def foldLinear (r : Fin 19 → Fin 18) : (Fin 19 → K) →ₗ[K] (Fin 18 → K) where
  toFun := folded r
  map_add' u v := by
    ext i
    simp only [folded, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' k u := by
    ext i
    simp only [folded, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private theorem fold_pull (r : Fin 19 → Fin 18) (u : Fin 19 → K) (f : Fin 18 → K) (t : Fin 18) :
    foldLinear r (fun i => u i * f (r i)) t = foldLinear r u t * f t := by
  change (∑ i ∈ Finset.univ.filter (fun i => r i = t), u i * f (r i)) =
    (∑ i ∈ Finset.univ.filter (fun i => r i = t), u i) * f t
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Exact correction for arbitrary original signed weights, before any
reflected clock powers or marked reverse budgets are imposed. -/
theorem fold_adjoint (chart : PairClasses e r m) (u : Fin 19 → K) (t : Fin 18) :
    foldLinear r (mat A.transpose u) t =
      reverseSum (causalMergeMatrix A e r) (foldLinear r u) t +
        u m * foldLinear r (rowDelta A e r m) t := by
  classical
  let B := causalMergeMatrix A e r
  let D := rowDelta A e r m
  have swap : foldLinear r (mat A.transpose u) t =
      ∑ i, foldLinear r (A i) t * u i := by
    change (∑ j ∈ Finset.univ.filter (fun j => r j = t), mat A.transpose u j) =
      ∑ i, (∑ j ∈ Finset.univ.filter (fun j => r j = t), A i j) * u i
    simp only [mat_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  have merge (i : Fin 19) :
      foldLinear r (A i) t = B (r i) t + if i = m then foldLinear r D t else 0 := by
    by_cases hi : i = m
    · subst i
      have h : A m = A (e (r m)) + D := by
        ext j
        change A m j = A (e (r m)) j + (A m j - A (e (r m)) j)
        ring
      change foldLinear r (A m) t =
        foldLinear r (A (e (r m))) t + if m = m then foldLinear r D t else 0
      rw [if_pos rfl, h, map_add]
      rfl
    · rw [if_neg hi, add_zero]
      change foldLinear r (A i) t = foldLinear r (A (e (r i))) t
      rw [chart.kept i hi]
  have sum_fold :
      (∑ i : Fin 19, B (r i) t * u i) = reverseSum B (foldLinear r u) t := by
    have pair := folded_pair r u (fun i => B i t)
    simp only [row_apply, dotProduct] at pair
    change (∑ i : Fin 19, B (r i) t * u i) = ∑ j, B j t * folded r u j
    simpa only [mul_comm] using pair.symm
  have correction : (∑ i : Fin 19, (if i = m then foldLinear r D t else 0) * u i) =
      foldLinear r D t * u m := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hi
      simp only [if_neg hi, zero_mul]
    · simp
  rw [swap]
  simp_rw [merge, add_mul]
  rw [Finset.sum_add_distrib, sum_fold, correction, mul_comm (foldLinear r D t) (u m)]

/-- This is a genuine transpose on the retained representatives. The
correction from the omitted row is zero when its signed multiplier is zero. -/
theorem fold_adjoint_of_zero (chart : PairClasses e r m) (u : Fin 19 → K) (um : u m = 0)
    (t : Fin 18) :
    foldLinear r (mat A.transpose u) t =
      reverseSum (causalMergeMatrix A e r) (foldLinear r u) t := by
  rw [fold_adjoint chart, um, zero_mul, add_zero]

private theorem transpose_at_cut (ha : ∀ i j, i ≤ j → A i j = 0) (u : Fin 19 → K)
    (i : Fin 19) (quiet : ∀ j, i < j → u j = 0) : mat A.transpose u i = 0 := by
  change (∑ j : Fin 19, A j i * u j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j ≤ i
  · rw [ha j i hj, zero_mul]
  · rw [quiet j (lt_of_not_ge hj), mul_zero]

private theorem delta_tail (chart : PairClasses e r m) (ha : ∀ i j, i ≤ j → A i j = 0)
    (i : Fin 19) (hi : m ≤ i) : rowDelta A e r m i = 0 := by
  simp only [rowDelta, ha m i hi, ha (e (r m)) i ((chart.earlier m).trans hi), sub_self]

/-- Row 1 is zero on every marked grade-ten lifted coordinate. This uses
only the original reviewed order, and the literal last-coordinate payment. -/
theorem fold_first_paid (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b = 0)
    (lifts : ∀ t : Fin 18, (fun i => coordinate (K:=K) t (r i)) ∈
      treeSpace A 10 ⊔ K ∙ coordinate (Fin.last 18)) :
    ∀ t : Fin 18, foldLinear r (reflectedStageRow A b 1) t = 0 := by
  let L := Fin.last 18
  have cL := (ERK13NativeFirst.last_original_active ha ho).node_eq_one ha seed
  have yL : reflectedClock A L = 0 := by
    change 1 - nodes A L = 0
    rw [cL, sub_self]
  have noTail := transpose_at_cut ha (reflectedStageWeight A b 1) L
    (fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim)
  have rhoL : reflectedStageRow A b 1 L = 0 := by
    change (((1+1:ℕ):K) * mat A.transpose (reflectedStageWeight A b 1) L -
      b L * reflectedClock A L ^ 2) = 0
    rw [noTail, mul_zero, yL]
    simp
  let rho := reflectedStageRow A b 1
  have pay : rho ∈ annih (treeSpace A 10) :=
    reflectedStageRow_annih ho 10 1 (by decide)
  have paidPlus : rho ∈ annih (treeSpace A 10 ⊔ K ∙ coordinate L) := by
    rw [annih_sup_coordinate, mem_zeroAt]
    exact ⟨pay,rhoL⟩
  intro t
  change folded r rho t = 0
  rw [← row_coordinate (folded r rho) t, folded_pair]
  exact mem_annih.mp paidPlus _ (lifts t)

/-- The positive folded row, with the exact signed correction from the
physical weight of the one omitted stage. -/
theorem fold_original_row (chart : PairClasses e r m)
    (cy : ∀ i, reflectedClock A (e (r i)) = reflectedClock A i)
    (k : ℕ) (t : Fin 18) :
    foldLinear r (reflectedStageRow A b k) t =
      foldedRow (causalMergeMatrix A e r) (foldLinear r b)
        (fun h => reflectedClock A (e h)) k t +
      (((k + 1 : ℕ) : K) * b m * reflectedClock A m ^ k) *
        foldLinear r (rowDelta A e r m) t := by
  let y : Fin 18 → K := fun h => reflectedClock A (e h)
  have foldWeight (q : ℕ) :
      foldLinear r (reflectedStageWeight A b q) = fun h => foldLinear r b h * y h ^ q := by
    ext h
    have eq : reflectedStageWeight A b q = fun i => b i * (y (r i)) ^ q := by
      ext i
      simp only [reflectedStageWeight, y, cy]
    rw [eq]
    exact fold_pull r b (fun i => y i ^ q) h
  change foldLinear r
      ((((k+1:ℕ):K) • mat A.transpose (reflectedStageWeight A b k)) -
        reflectedStageWeight A b (k+1)) t = _
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, fold_adjoint chart]
  rw [foldWeight k, foldWeight (k+1)]
  change (((k+1:ℕ):K) *
      (reverseSum (causalMergeMatrix A e r) (fun h => foldLinear r b h * y h ^ k) t +
       (b m * reflectedClock A m ^ k) * foldLinear r (rowDelta A e r m) t) -
      foldLinear r b t * y t ^ (k+1)) =
    foldedRow (causalMergeMatrix A e r) (foldLinear r b) y k t +
    (((k+1:ℕ):K) * b m * reflectedClock A m ^ k) * foldLinear r (rowDelta A e r m) t
  unfold foldedRow
  ring

/-- Exact small reverse spans on the original 19 coordinates. This is a
deliberate upstream boundary: these covers come from the rank 2/3/4 flags
and their two measured noninvariance steps, not from a rank claim about B. -/
structure ReverseCover (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19 → K)
    (D : Fin 19 → K) : Prop where
  second : ∀ v ∈ primitiveBack A b 2, ∃ h p : K,
    ∀ i, v i = h * reflectedStageRow A b 1 i + D i * p
  third : ∀ v ∈ primitiveBack A b 3, ∃ h p q : K,
    ∀ i, v i = h * reflectedStageRow A b 1 i + D i * (p + q * reflectedClock A i)
  fourth : ∀ v ∈ primitiveBack A b 4, ∃ h p q s : K,
    ∀ i, v i = h * reflectedStageRow A b 1 i +
      D i * (p + q * reflectedClock A i + s * reflectedClock A i ^ 2)

private theorem row_mem_reverse (k : ℕ) :
    reflectedStageRow A b (k+1) ∈ primitiveBack A b (k+1) :=
  adjointFlag_credit _ k (monomial_mem_credit k (k+1) le_rfl)

private theorem rho_at_last_off_one (ha : ∀ i j, i ≤ j → A i j = 0)
    (tail : ∀ i, m < i → b i * reflectedClock A i = 0) :
    reflectedStageRow A b 1 m = - (b m * reflectedClock A m ^ 2) := by
  have noTail := transpose_at_cut ha (reflectedStageWeight A b 1) m (by
    intro j hj
    simpa only [reflectedStageWeight, pow_one] using tail j hj)
  change (((1+1:ℕ):K) * mat A.transpose (reflectedStageWeight A b 1) m -
    b m * reflectedClock A m ^ 2) = _
  rw [noTail, mul_zero, zero_sub]

/-- `HasOrder` is used at the actual E₁₀ payment, never on B. The positive
subsequent rows use reviewed monomial credits for budgets 9+2+2 and 8+3+2
on the original tableau, recorded in the genuine reverse covers. -/
theorem causalRows_of_original (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) (seed : firstSeed A b = 0)
    (cy : ∀ i, reflectedClock A (e (r i)) = reflectedClock A i)
    (live : b m ≠ 0) (offOne : reflectedClock A m ≠ 0)
    (tail : ∀ i, m < i → b i * reflectedClock A i = 0)
    (lifts : ∀ t : Fin 18, (fun i => coordinate (K:=K) t (r i)) ∈
      treeSpace A 10 ⊔ K ∙ coordinate (Fin.last 18))
    (inTwo : rowDelta A e r m ∈ primitiveBack A b 2)
    (covers : ReverseCover A b (rowDelta A e r m)) :
    CausalRows (causalMergeMatrix A e r) (foldLinear r b)
      (fun h => reflectedClock A (e h)) (foldLinear r (rowDelta A e r m)) := by
  let B := causalMergeMatrix A e r
  let y : Fin 18 → K := fun h => reflectedClock A (e h)
  let x := reflectedClock A
  let D := rowDelta A e r m
  let l := foldLinear r D
  let rho := reflectedStageRow A b 1
  change CausalRows B (foldLinear r b) y l
  have FoldRho : ∀ t, foldLinear r rho t = 0 := fold_first_paid ha ho seed lifts
  have rhoNe : rho m ≠ 0 := by
    change reflectedStageRow A b 1 m ≠ 0
    rw [rho_at_last_off_one ha tail]
    exact neg_ne_zero.mpr (mul_ne_zero live (pow_ne_zero _ offOne))
  have Dm : D m = 0 := delta_tail chart ha m le_rfl
  have pull (f : K → K) (t : Fin 18) :
      foldLinear r (fun i => D i * f (x i)) t = l t * f (y t) := by
    have eq : (fun i => D i * f (x i)) = fun i => D i * f (y (r i)) :=
      funext (fun i => congrArg (fun z => D i * f z) (cy i).symm)
    rw [eq]
    exact fold_pull r D (fun i => f (y i)) t
  have foldShape {v : Fin 19 → K} (h : K) (f : K → K)
      (hv : ∀ i, v i = h * rho i + D i * f (x i)) (t : Fin 18) :
      foldLinear r v t = l t * f (y t) := by
    have eq : v = h • rho + fun i => D i * f (x i) := funext hv
    rw [eq, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      FoldRho, mul_zero, zero_add, pull]
  have noRho {u : Fin 19 → K} (tailU : ∀ j, m < j → u j = 0) (h : K) (f : K → K)
      (hv : ∀ i, mat A.transpose u i = h * rho i + D i * f (x i)) : h = 0 := by
    have cut := hv m
    rw [transpose_at_cut ha u m tailU, Dm, zero_mul, add_zero] at cut
    exact (mul_eq_zero.mp cut.symm).resolve_right rhoNe
  let Dy := diag x D
  have DyApply (i : Fin 19) : Dy i = D i * x i := by
    change x i * D i = D i * x i
    exact mul_comm _ _
  have DyFold : foldLinear r Dy = diag y l := by
    ext t
    simp only [diag_apply]
    rw [show Dy = fun i => D i * x i from funext DyApply]
    change foldLinear r (fun i => D i * id (x i)) t = _
    rw [pull id t]
    simp only [id_eq]
    exact mul_comm _ _
  have DyM : Dy m = 0 := by rw [DyApply, Dm, zero_mul]
  -- Strict causality at m also kills the original ρ₁ coefficient before folding.
  have originalAdjointProfiles :
      (∃ p q : K, ∀ i, mat A.transpose D i = D i * (p + q*x i)) ∧
      (∃ p q s : K, ∀ i, mat A.transpose Dy i = D i * (p + q*x i + s*x i^2)) := by
    constructor
    · have mem : mat A.transpose D ∈ primitiveBack A b 3 :=
        adjointFlag_transpose _ 2 (Submodule.mem_map_of_mem inTwo)
      obtain ⟨h,p,q,hv⟩ := covers.third _ mem
      have hz := noRho (fun j hj => delta_tail chart ha j hj.le) h
        (fun z => p+q*z) hv
      exact ⟨p,q,fun i => by simpa only [hz,zero_mul,zero_add] using hv i⟩
    · have yMem : Dy ∈ primitiveBack A b 3 :=
        adjointFlag_clock _ 2 (Submodule.mem_map_of_mem inTwo)
      have mem : mat A.transpose Dy ∈ primitiveBack A b 4 :=
        adjointFlag_transpose _ 3 (Submodule.mem_map_of_mem yMem)
      obtain ⟨h,p,q,s,hv⟩ := covers.fourth _ mem
      have hz := noRho (fun j hj => by
        have hDj : D j = 0 := delta_tail chart ha j hj.le
        rw [DyApply, hDj, zero_mul]) h
        (fun z => p+q*z+s*z^2) hv
      exact ⟨p,q,s,fun i => by simpa only [hz,zero_mul,zero_add] using hv i⟩
  have gate₀ : ∃ p q : K, ∀ t, reverseSum B l t = l t * (p + q*y t) := by
    obtain ⟨p,q,hv⟩ := originalAdjointProfiles.1
    refine ⟨p,q,fun t => ?_⟩
    rw [← fold_adjoint_of_zero chart D Dm t,
      show mat A.transpose D = fun i => D i * (p+q*x i) from funext hv]
    exact pull (fun z => p+q*z) t
  have gate₁ : ∃ p q s : K, ∀ t, reverseSum B (diag y l) t = l t * (p+q*y t+s*y t^2) := by
    obtain ⟨p,q,s,hv⟩ := originalAdjointProfiles.2
    refine ⟨p,q,s,fun t => ?_⟩
    rw [← DyFold, ← fold_adjoint_of_zero chart Dy DyM t,
      show mat A.transpose Dy = fun i => D i * (p+q*x i+s*x i^2) from funext hv]
    exact pull (fun z => p+q*z+s*z^2) t
  refine ⟨?_,?_,?_,gate₀,?_⟩
  · refine ⟨-(2*b m*x m), neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (by norm_num) live) offOne), fun t => ?_⟩
    have h := fold_original_row chart cy (b:=b) 1 t
    change foldLinear r rho t = foldedRow B (foldLinear r b) y 1 t +
      (((1+1:ℕ):K)*b m*x m ^ 1)*l t at h
    rw [FoldRho] at h
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at h
    linear_combination -h
  · obtain ⟨h,p,hv⟩ := covers.second _ (row_mem_reverse (A:=A) (b:=b) 1)
    refine ⟨p-3*b m*x m^2,fun t => ?_⟩
    have h₂ := fold_original_row chart cy (b:=b) 2 t
    change foldLinear r (reflectedStageRow A b 2) t = foldedRow B (foldLinear r b) y 2 t +
      (((2+1:ℕ):K)*b m*x m ^ 2)*l t at h₂
    rw [foldShape h (fun _ => p) hv] at h₂
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h₂
    linear_combination -h₂
  · obtain ⟨h,p,q,hv⟩ := covers.third _ (row_mem_reverse (A:=A) (b:=b) 2)
    refine ⟨p-4*b m*x m^3,q,fun t => ?_⟩
    have h₃ := fold_original_row chart cy (b:=b) 3 t
    change foldLinear r (reflectedStageRow A b 3) t = foldedRow B (foldLinear r b) y 3 t +
      (((3+1:ℕ):K)*b m*x m ^ 3)*l t at h₃
    rw [foldShape h (fun z => p+q*z) hv] at h₃
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h₃
    linear_combination -h₃
  · obtain ⟨p,q,h₀⟩ := gate₀
    obtain ⟨a,d,s,h₁⟩ := gate₁
    intro Y
    refine ⟨fun z => a+d*z+s*z^2-Y*(p+q*z), fun t => ?_⟩
    have split : reverseSum B (fun j => (y j - Y) * l j) t =
        reverseSum B (diag y l) t - Y * reverseSum B l t := by
      simp only [reverseSum, diag_apply]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [split, h₀, h₁]
    ring

theorem impossible_of_original (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) (seed : firstSeed A b = 0)
    (cy : ∀ i, reflectedClock A (e (r i)) = reflectedClock A i)
    (live : b m ≠ 0) (offOne : reflectedClock A m ≠ 0)
    (tail : ∀ i, m < i → b i * reflectedClock A i = 0)
    (lifts : ∀ t : Fin 18, (fun i => coordinate (K:=K) t (r i)) ∈
      treeSpace A 10 ⊔ K ∙ coordinate (Fin.last 18))
    (inTwo : rowDelta A e r m ∈ primitiveBack A b 2)
    (covers : ReverseCover A b (rowDelta A e r m))
    (card : 3 ≤ (unionSupport (foldLinear r b) (fun h => reflectedClock A (e h))
      (foldLinear r (rowDelta A e r m))).card)
    (mass_support : ∀ t, foldLinear r (rowDelta A e r m) t = 0 →
      foldLinear r b t * reflectedClock A (e t) = 0)
    (ratios : DistinguishedRatios (foldLinear r b) (fun h => reflectedClock A (e h))
      (foldLinear r (rowDelta A e r m))) : False :=
  causal_impossible_of_mass_support (causalMerge_strict ha chart.ordered chart.earlier) card
    (causalRows_of_original chart ha ho seed cy live offOne tail lifts inTwo covers) mass_support ratios

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
