module

public import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank
public import RKCert.ReviewedNative.ReverseClockGain
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual-row and scalar adapters for the late six-ghost cut -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixPaid

open RKResearch Polynomial RKCert.Endpoint Reverse
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- A weighted primitive row is paid in the original rooted flag,
with its actual terminal debit. -/
theorem primitive_paid_at_terminal {A : Matrix (Fin 13) (Fin 13) K} {b : Fin 13 → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (norm : OrderElevenThirteen.Normalized A b)
    (P : K[X]) (j n : ℕ) (deg : P.natDegree ≤ n+1) (pay : j+n+3≤11) :
    mat A.transpose (weightedEval (reflectedClock A) b P) -
        weightedEval (reflectedClock A) b (primitive P)
      ∈ zeroAt (annih (treeSpace A j)) (Fin.last 12) := by
  let t : Fin 13 := Fin.last 12
  have census := OrderElevenThirteen.rank_census ha ho norm
  have ht : LastActive b t := ⟨census.terminalWeight, fun k h => False.elim
    ((not_lt_of_ge (Fin.le_last k)) h)⟩
  have raw : mat A.transpose (weightedEval (reflectedClock A) b P) -
      weightedEval (reflectedClock A) b (primitive P) ∈ primitiveBack A b (n+1) :=
    reverse_primitive_next n P deg
  exact mem_zeroAt.mpr ⟨primitiveBack_annih ho j (n+1) (by omega) raw,
    mem_tailZero.mp (ht.dirk_primitiveBack_tail ha norm.d1 norm.d2 (n+1) raw) t le_rfl⟩

/-- If the starting mark annihilates the next actual tree grade, its
compensated transpose image has exactly the ordinary primitive budget.
Neither the weighted mark nor the compensated array is claimed to
be another RK method. -/
theorem compensated_paid_at_terminal {A : Matrix (Fin 13) (Fin 13) K} {b : Fin 13 → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (norm : OrderElevenThirteen.Normalized A b)
    (P : K[X]) (j n : ℕ) (deg : P.natDegree ≤ n+1) (pay : j+n+3≤11)
    {m : Fin 13 → K} (hm : m∈annih (treeSpace A (j+1))) :
    mat A.transpose (m-weightedEval (reflectedClock A) b P) +
        weightedEval (reflectedClock A) b (primitive P)
      ∈ zeroAt (annih (treeSpace A j)) (Fin.last 12) := by
  let W := weightedEval (reflectedClock A) b
  let T := mat A.transpose
  let t : Fin 13 := Fin.last 12
  let Z := zeroAt (annih (treeSpace A j)) t
  have hP : T (W P)-W (primitive P)∈Z :=
    primitive_paid_at_terminal ha ho norm P j n deg (by omega)
  have hN : T m∈Z := by
    apply mem_zeroAt.mpr
    refine ⟨annih_map_transpose (mat_treeSpace A j) (Submodule.mem_map_of_mem hm),?_⟩
    have census := OrderElevenThirteen.rank_census ha ho norm
    rw [show T=mat A.transpose from rfl,mat_apply,Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [Matrix.transpose_apply,census.terminalColumn,zero_mul]
  change T (m-W P)+W (primitive P)∈Z
  have eq : T (m-W P)+W (primitive P)=T m-(T (W P)-W (primitive P)) := by
    rw [map_sub]
    abel
  rw [eq]
  exact Z.sub_mem hN hP

omit [CharZero K] in
/-- A genuine paid row that is zero at the first live ghost loses one
polynomial degree when expressed using the ghost-vanishing mark. -/
theorem calibrate_live_ghost {I : Type*} (y G H raw : I → K) (z : I)
    (P : K[X]) (d : ℕ) (a : K)
    (deg : P.natDegree≤d+1) (live : G z≠0) (head : H z=0) (at_z : raw z=0)
    (shape : ∀ i, raw i=P.eval (y i)*G i+a*H i) :
    ∃ Q : K[X], Q.natDegree≤d ∧
      ∀ i, raw i=Q.eval (y i)*((y i-y z)*G i)+a*H i := by
  have root : P.IsRoot (y z) := by
    have e := shape z
    rw [at_z,head,mul_zero,add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_right live
  obtain ⟨Q,hQ⟩ := dvd_iff_isRoot.mpr root
  have qd : Q.natDegree≤d := by
    by_cases qz : Q=0
    · simp [qz]
    · rw [hQ,natDegree_mul (X_sub_C_ne_zero _) qz,natDegree_X_sub_C] at deg
      omega
  refine ⟨Q,qd,fun i => ?_⟩
  rw [shape i,hQ,eval_mul,eval_sub,eval_X,eval_C]
  ring

omit [CharZero K] in
/-- Two positive-power nodal inputs after the third regular determine
an optional live ghost clock, independently of its actual tap. -/
theorem first_optional_clock (w x a e d q : K)
    (live : d≠0) (h0 : q= -d) (h1 : w*q= -(a+e*x)*d) :
    a+e*x=w := by
  have z : (a+e*x-w)*d=0 := by linear_combination h1-w*h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right live)

omit [CharZero K] in
/-- Reverse Volterra at a first optional ghost with one live nodal
donor forces the literal diagonal. It does not assume distinct
numerical ghost and ordinary clocks. -/
theorem first_optional_diagonal (x w d q : K)
    (live : q≠0) (comm : (x-w-d)*q=0) : d=x-w := by
  exact (sub_eq_zero.mp ((mul_eq_zero.mp comm).resolve_right live)).symm

omit [CharZero K] in
/-- The two zeroth/first moment taps are uniquely resolved even when a
node is zero. No weight or mark value is divided by. -/
theorem two_nodal_taps (r s x y p q : K) (distinct : r≠s)
    (h0 : x+y=p) (h1 : r*x+s*y=q) :
    x=(s*p-q)/(s-r) ∧ y=(q-r*p)/(s-r) := by
  constructor
  · apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm distinct))).mpr
    linear_combination s*h0-h1
  · apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm distinct))).mpr
    linear_combination h1-r*h0

end RKResearch.Certified.Graded.OrderElevenInvisibleSixPaid
