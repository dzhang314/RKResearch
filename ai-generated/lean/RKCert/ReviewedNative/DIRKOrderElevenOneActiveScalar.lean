module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Division-free scalar checks for the single active dirty clock
The order and causal-rank hypotheses are supplied in the associated paper.
In particular no diagonal or third shifted tap is inverted. -/
namespace RKResearch.Certified.Graded.OrderElevenOneActive

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [CharZero K]

/-- The single-cut equality at a live clean row rules out the same
cubic moment ratio that an early ghost would require. -/
theorem early_donor_conflict (u v V beta : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hV : V ≠ 0) (hVu : V-u ≠ 0) (hb : beta ≠ 0)
    (he : V*(V-u)*(V-v) = V*(V-u)*(V-u/2))
    (hm : beta*v^3*(2*u-v)=0) : False := by
  have h1 : V*(V-u)*(u/2-v)=0 := by linear_combination he
  have h2 : u/2-v=0 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hV hVu)
  have h3 : 2*u-v=0 := (mul_eq_zero.mp hm).resolve_left (mul_ne_zero hb (pow_ne_zero _ hv))
  have hu0 : u=0 := by linear_combination (2/3 : K)*h3-(2/3 : K)*h2
  exact hu hu0

noncomputable def M (u v w : K) : K :=
  4*w*u^2-13*w*u*v+4*w*v^2+u^2*v+u*v^2
noncomputable def L (u v w : K) : K := 3*w^2-5*w*(u+v)+10*u*v
noncomputable def J (u v w : K) : K := w*u^2-4*w*u*v+w*v^2+u^2*v+u*v^2
noncomputable def F (u v w : K) : K := w^3*(2*u-v)*L u v w

noncomputable def a2 (u v : K) : K := (u-2*v)^2*(2*u-v)
noncomputable def a1 (u v w : K) : K := w*(
    3*u^3*v^2-15*u^3*v*w+4*u^3*w^2+3*u^2*v^3+15*u^2*v^2*w+6*u^2*v*w^2-
    15*u*v^3*w+6*u*v^2*w^2-9*u*v*w^3+4*v^3*w^2)
noncomputable def a0 (u v w : K) : K := w^4*(2*u-v)*(
    6*u^2*v^2-3*u^2*v*w+u^2*w^2-3*u*v^2*w-u*v*w^2+v^2*w^2)

noncomputable def numerator (u v w q : K) : K :=
  a2 u v*q^2+a1 u v w*q+a0 u v w

/-- Clear the shifted DA slope without assuming `M≠0` or `q≠0`.
The exact resultant modulo `M*q-F` is the displayed square. -/
theorem undivided_affine_identity (u v w q : K) (hq : M u v w*q=F u v w) :
    (M u v w)^2*numerator u v w q =
      36*w^4*(u-w)^2*(2*u-v)*(v-w)^2*(J u v w)^2 := by
  calc
    _ = a2 u v*(M u v w*q)^2+a1 u v w*M u v w*(M u v w*q)+a0 u v w*(M u v w)^2 := by
      unfold numerator
      ring
    _ = _ := by
      rw [hq]
      unfold a2 a1 a0 M F L J
      ring

/-- The third shifted diagonal numerator is exactly divisible by the
same clock gate, still before dividing by `M`. -/
theorem undivided_diagonal_identity (u v w q : K) (hq : M u v w*q=F u v w) :
    M u v w*(3*w^4-4*(u+v)*w^3+6*u*v*w^2+(2*v-u)*q) =
      6*w^2*(u-w)*(v-w)*J u v w := by
  calc
    _ = M u v w*(3*w^4-4*(u+v)*w^3+6*u*v*w^2)+(2*v-u)*(M u v w*q) := by ring
    _ = _ := by rw [hq]; unfold M F L J; ring

noncomputable def kU (u : K) : K := -u^3/6
noncomputable def kV (u v : K) : K := v^3*(2*u-v)/(6*(u-2*v))
noncomputable def m1 (w : K) : K := w^2/2
noncomputable def m2 (w k : K) : K := w^3/3-k
noncomputable def m3 (u w k : K) : K := w^4/4-(3*u/2)*k
noncomputable def tap2 (i j w k : K) : K := (m2 w k-j*m1 w)/(i*(i-j))
noncomputable def tap3 (i j l u w k : K) : K :=
  (m3 u w k-(j+l)*m2 w k+j*l*m1 w)/(i*(i-j)*(i-l))
noncomputable def readV (u v : K) : K :=
  (u^3-3*u*v^2+v^3)/(2*(u-2*v)*(2*u-v))

/-- Calibration from the first two genuine compensated clean columns. -/
theorem readV_formula (u v : K)
    (hu : u≠0) (hv : v≠0) (huv : u-v≠0) (hvu : v-u≠0)
    (hu2v : u-2*v≠0) (h2uv : 2*u-v≠0) :
    (kU u*tap2 u v v (kV u v)+kV u v*tap2 v u v (kV u v))/kV u v = readV u v := by
  have hkv : kV u v ≠ 0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ hv) h2uv)
    (mul_ne_zero (by norm_num) hu2v)
  rw [div_eq_iff hkv]
  unfold kU kV tap2 m1 m2 readV
  generalize hp : u-2*v = p at *
  generalize hq : 2*u-v = q at *
  field_simp [hu,hv,huv,hvu,hu2v,h2uv]
  subst p
  subst q
  ring

/-- The undivided, shifted DA-affinity equation is exactly the
three-variable polynomial applied in `undivided_affine_identity`. -/
theorem cleared_three_read (u v w k : K)
    (hu : u≠0) (hv : v≠0) (hw : w≠0)
    (huv : u-v≠0) (hvu : v-u≠0) (huw : u-w≠0) (hwu : w-u≠0)
    (hvw : v-w≠0) (hwv : w-v≠0) (hu2v : u-2*v≠0) (h2uv : 2*u-v≠0) :
    72*w*(u-2*v)*(u-w)*(2*u-v)*(v-w)*
      (k*(u/2+(readV u v-u/2)*(w-u)/(v-u))-
        kU u*tap3 u v w u w k-kV u v*tap3 v u w u w k-k*tap3 w u v u w k) =
      numerator u v w (6*k) := by
  unfold readV kU kV tap3 m1 m2 m3 numerator a2 a1 a0
  generalize hp : u-2*v = p at *
  generalize hq : 2*u-v = q at *
  field_simp [hu,hv,hw,huv,hvu,huw,hwu,hvw,hwv,hu2v,h2uv]
  subst p
  subst q
  ring

end RKResearch.Certified.Graded.OrderElevenOneActive
