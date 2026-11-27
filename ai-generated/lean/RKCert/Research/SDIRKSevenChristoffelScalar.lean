module

public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.ZMod.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Christoffel and local descent checks for a seven-active order-seven chart

The elliptic two-isogeny rank theorem is used in the accompanying mathematical
proof, not treated as a new native axiom. This module checks the scalar change
of coordinates, the five-support rank gate, and the finite local obstructions.
-/

namespace RKResearch.Certified.SDIRKSevenChristoffelScalar
open Module Graded Reverse
open scoped BigOperators Matrix

def kernelFour {R : Type*} [CommRing R] (x y : R) : R :=
  175*x^3*y^3-105*x^3*y+45*x^2*y^2-15*x^2-105*x*y^3+75*x*y-15*y^2+9

def legendre (x : ℚ) (i : Fin 4) : ℚ :=
  ![1,x,(3*x^2-1)/2,(5*x^3-3*x)/2] i

theorem uniform_kernel (x y : ℚ) :
    4 * (∑ i : Fin 4, (2*(i.val : ℚ)+1)*legendre x i*legendre y i) = kernelFour x y := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, legendre, kernelFour,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

def productNumerator (p : ℚ) : ℚ := (5*p+3)*(35*p^2+30*p+3)

theorem product_sum (x y : ℚ) :
    kernelFour x y = productNumerator (x*y)-15*(7*x*y+1)*(x+y)^2 := by
  simp only [kernelFour,productNumerator]
  ring

theorem denominator_ne {x y : ℚ} (h : kernelFour x y=0) : 7*(x*y)+1≠0 := by
  intro e
  have p : x*y=-1/7 := by linear_combination (1/7:ℚ)*e
  rw [product_sum] at h
  rw [mul_assoc 7 x y,p] at h
  norm_num [productNumerator] at h

def curveX (p : ℚ) : ℚ := -105*(5*p+3)/(7*p+1)
def curveY (p s : ℚ) : ℚ := 12600*s/(7*p+1)

theorem kernel_to_curve {x y : ℚ} (h : kernelFour x y=0) :
    let X := curveX (x*y)
    let Y := curveY (x*y) (x+y)
    Y^2=X*(X^2+1350*X+23625) := by
  let p := x*y
  let s := x+y
  have hr : 7*p+1≠0 := denominator_ne h
  have hF : productNumerator p-15*(7*p+1)*s^2=0 := by
    simpa only [product_sum,mul_assoc] using h
  change curveY p s ^2=curveX p*(curveX p ^2+1350*curveX p+23625)
  simp only [curveX,curveY]
  unfold productNumerator at hF
  field_simp [hr]
  linear_combination (-10584000:ℚ)*hF

private theorem rat_square_fifteen (r : ℚ) (h : r^2=15) : False := by
  have nat_no : ¬ IsSquare (15:ℕ) := by
    rintro ⟨m,e⟩
    by_cases b : 4≤m
    · have k : 16≤m*m := Nat.mul_le_mul b b
      omega
    · have c : m≤3 := by omega
      have k : m*m≤9 := Nat.mul_le_mul c c
      omega
  exact ((Rat.isSquare_natCast_iff (n:=15)).not.mpr nat_no)
    ⟨r,by linear_combination -h⟩

/-- The only possible affine torsion point of the paper's rank-zero
curve cannot come from a pair of finite rational clocks. -/
theorem curve_zero_impossible {x y : ℚ} (h : kernelFour x y=0)
    (hx : curveX (x*y)=0) : False := by
  have hr := denominator_ne h
  unfold curveX at hx
  rw [div_eq_iff hr,zero_mul] at hx
  have p : x*y=-3/5 := by linear_combination (-1/525:ℚ)*hx
  have Y : curveY (x*y) (x+y)=0 := by
    have hP := kernel_to_curve h
    have hq : curveX (x*y)=0 := by
      unfold curveX
      rw [div_eq_iff hr,zero_mul]
      exact hx
    dsimp at hP
    rw [hq,zero_mul] at hP
    exact sq_eq_zero_iff.mp hP
  unfold curveY at Y
  rw [div_eq_iff hr,zero_mul] at Y
  have s : x+y=0 := by linear_combination (1/12600:ℚ)*Y
  apply rat_square_fifteen (5*x)
  linear_combination 25*x*s-25*p

theorem kernel_nonzero_of_curve (hE : ∀ X Y : ℚ, Y^2=X*(X^2+1350*X+23625) → X=0)
    (x y : ℚ) : kernelFour x y≠0 := by
  intro e
  exact curve_zero_impossible e (hE _ _ (kernel_to_curve e))

/-- Five active support sites, a nonzero isotropic component, and a paid
four-dimensional polynomial span force the component to lie in that span. -/
theorem five_support_cubic {K : Type*} [Field K] {P : Submodule K (Fin 5→K)}
    (p : finrank K P=4) {b v : Fin 5→K} (hb : ∀ i,b i≠0) (hv : v≠0)
    (horth : diag b v ∈ annih P) (hnum : row (diag b v) v=0) : v∈P := by
  let w := diag b v
  have wn : w≠0 := by
    intro hw
    apply hv
    funext i
    have hi : b i*v i=0 := by
      simpa only [w,diag_apply,Pi.zero_apply] using congrFun hw i
    exact (mul_eq_zero.mp hi).resolve_left (hb i)
  let U := K ∙ w
  have le : P≤annih U := by
    intro q hq
    apply mem_annih.mpr
    intro z hz
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [row_apply,dotProduct_smul,dotProduct_comm,←row_apply,
      mem_annih.mp horth _ hq,smul_zero]
  have dimU : finrank K U=1 := finrank_span_singleton wn
  have dimA := finrank_annih U
  rw [dimU,Fintype.card_fin] at dimA
  have eqP : P=annih U := Submodule.eq_of_le_of_finrank_le le (by omega)
  rw [eqP]
  apply mem_annih.mpr
  intro z hz
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [row_apply,dotProduct_smul,dotProduct_comm,←row_apply,hnum,smul_zero]

def makeMask : List ℕ → ℕ
  | [] => 0
  | i::l => (1 <<< i) ||| makeMask l

private theorem makeMask_hit {l : List ℕ} {i : ℕ} (h : i∈l) :
    (makeMask l).testBit i = true := by
  induction l with
  | nil => simp at h
  | cons j l ih =>
    rw [makeMask,Nat.testBit_or]
    rcases List.mem_cons.mp h with rfl | h'
    · simp [Nat.testBit_shiftLeft]
    · rw [ih h',Bool.or_true]

def squares (q : ℕ) : List ℕ := (List.range q).map fun t => t*t%q

def quarticResidue (q : ℕ) (a b c : ℤ) (t : ℕ) : ℕ :=
  ((a : ZMod q)+(b : ZMod q)*(t : ZMod q)^2+(c : ZMod q)*(t : ZMod q)^4).val

def chartChecks (q : ℕ) (a b c : ℤ) : Bool :=
  let m := makeMask (squares q)
  (List.range q).all fun i => !(m.testBit (quarticResidue q a b c i))

private theorem chart_no_square {q : ℕ} [NeZero q] {a b c : ℤ}
    (h : chartChecks q a b c=true) (r s : ZMod q) :
    s^2≠(a : ZMod q)+(b : ZMod q)*r^2+(c : ZMod q)*r^4 := by
  intro eqn
  have hit : (s.val*s.val%q) ∈ squares q :=
    List.mem_map.mpr ⟨s.val,List.mem_range.mpr s.val_lt,rfl⟩
  have k := makeMask_hit hit
  unfold chartChecks at h
  have d := List.all_eq_true.mp h r.val (List.mem_range.mpr r.val_lt)
  have g : s.val*s.val%q=quarticResidue q a b c r.val := by
    unfold quarticResidue
    rw [ZMod.natCast_zmod_val,←eqn,pow_two,ZMod.val_mul]
  rw [←g,k] at d
  contradiction

abbrev Receipt := ℕ × ℤ × ℤ × ℤ

def localReceipts : List Receipt :=
  [(27,-15,1350,-1575),(16,-5,1350,-4725),(256,-3,1350,-7875),
    (16,-1,1350,-23625),(16,3,1350,7875),(256,5,1350,4725),
    (16,15,1350,1575),(625,3,-2700,576000),(81,5,-2700,345600),
    (27,15,-2700,115200)]

def bothCharts : Receipt → Bool
  | (q,a,b,c) => chartChecks q a b c && chartChecks q c b a

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem local_receipts_checked : localReceipts.all bothCharts=true := by decide +kernel

private theorem homogenize {R : Type*} [CommRing R] {a b c m n v : R}
    (h : ∀ r s : R, s^2≠a+b*r^2+c*r^4) (hm : IsUnit m) :
    v^2≠a*m^4+b*m^2*n^2+c*n^4 := by
  intro e
  obtain ⟨u,rfl⟩ := hm
  let i : R := ↑u⁻¹
  have hu : (u : R)*i=1 := Units.mul_inv u
  apply h (n*i) (v*i^2)
  calc
    (v*i^2)^2=v^2*i^4 := by ring
    _=(a*(u:R)^4+b*(u:R)^2*n^2+c*n^4)*i^4 := by rw [e]
    _=a*((u:R)*i)^4+b*((u:R)*i)^2*(n*i)^2+c*(n*i)^4 := by ring
    _=a+b*(n*i)^2+c*(n*i)^4 := by rw [hu]; ring

/-- Each tabulated prime power excludes both unit charts of its homogeneous
quartic; no affine-only reduction or search height is used. -/
theorem local_quartic_obstruction {q : ℕ} [NeZero q] {a b c : ℤ}
    (h : (q,a,b,c)∈localReceipts) {m n v : ZMod q} (unit : IsUnit m ∨ IsUnit n) :
    v^2≠(a : ZMod q)*m^4+(b : ZMod q)*m^2*n^2+(c : ZMod q)*n^4 := by
  have hh := List.all_eq_true.mp local_receipts_checked _ h
  change (chartChecks q a b c && chartChecks q c b a)=true at hh
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hh
  rcases unit with unit | unit
  · exact homogenize (chart_no_square h₁) unit
  · intro e
    apply homogenize (m:=n) (n:=m) (v:=v) (chart_no_square h₂) unit
    linear_combination e

theorem affine_f19_mass : (11 : ZMod 19)*kernelFour 17 17=4 := by
  decide +kernel

def natCurveCount (p : ℕ) : ℕ :=
  1+((List.range p).map fun x =>
    ((List.range p).filter fun y =>
      y*y%p==x*(x*x+1350*x+23625)%p).length).sum

theorem good_reduction_counts : natCurveCount 11=6 ∧ natCurveCount 17=16 := by
  decide +kernel

end RKResearch.Certified.SDIRKSevenChristoffelScalar
