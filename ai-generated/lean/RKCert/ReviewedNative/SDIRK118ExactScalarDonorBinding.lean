module

public import RKCert.ReviewedNative.SDIRK118LiteralAssembly
public import RKCert.ReviewedNative.SDIRK118ReverseOperator
public import Mathlib.LinearAlgebra.Basis.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings

open RKResearch
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation (coordinate affine_ratio_of_bracket)
open RKResearch.Certified.PaidDefectBridge.ForwardChart
open RKResearch.Certified.PaidDefectBridge.ReverseChart (seedQuad lastNormRow)
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry matrixOf rows)
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- Use the standard monomial basis. The basis hypothesis in the following
lemmas is only its exact usual specification, not a chart coefficient. -/
def coefficientPrimitive (M : Module.Basis ℕ K (Polynomial K)) :
    Polynomial K →ₗ[K] Polynomial K :=
  M.constr K (fun n => ((n+1 : ℕ) : K)⁻¹ • (Polynomial.X^(n+1)))

def evalAt (M : Module.Basis ℕ K (Polynomial K)) (x : K) : Polynomial K →ₗ[K] K :=
  M.constr K (fun n => x^n)

theorem primitive_pow (M : Module.Basis ℕ K (Polynomial K))
    (hM : ∀ n, M n=Polynomial.X^n) (n : ℕ) :
    coefficientPrimitive M (Polynomial.X^n)=((n+1 : ℕ) : K)⁻¹ • (Polynomial.X^(n+1)) := by
  rw [←hM n]
  simp [coefficientPrimitive]

theorem eval_pow (M : Module.Basis ℕ K (Polynomial K))
    (hM : ∀ n, M n=Polynomial.X^n) (x : K) (n : ℕ) :
    evalAt M x (Polynomial.X^n)=x^n := by
  rw [←hM n]
  simp [evalAt]

def evalSites (M : Module.Basis ℕ K (Polynomial K)) (x : Fin 6 → K) :
    Polynomial K →ₗ[K] (Fin 6 → K) where
  toFun p i := evalAt M (x i) p
  map_add' p q := by
    funext i
    exact map_add (evalAt M (x i)) p q
  map_smul' a p := by
    funext i
    exact map_smul (evalAt M (x i)) a p

theorem evalSites_pow (M : Module.Basis ℕ K (Polynomial K))
    (hM : ∀ n, M n=Polynomial.X^n) (x : Fin 6 → K) (n : ℕ) :
    evalSites M x (Polynomial.X^n)=x^n := by
  funext i
  change evalAt M (x i) (Polynomial.X^n)=(x i)^n
  exact eval_pow M hM (x i) n

theorem evalSites_X (M : Module.Basis ℕ K (Polynomial K))
    (hM : ∀ n, M n = Polynomial.X ^ n) (x : Fin 6 → K) :
    evalSites M x Polynomial.X = x := by
  simpa only [pow_one] using evalSites_pow M hM x 1

def mean (M : Module.Basis ℕ K (Polynomial K)) : Polynomial K →ₗ[K] K :=
  (evalAt M 1).comp (coefficientPrimitive M)

theorem mean_pow (M : Module.Basis ℕ K (Polynomial K))
    (hM : ∀ n, M n=Polynomial.X^n) (n : ℕ) :
    mean M (Polynomial.X^n)=((n+1 : ℕ) : K)⁻¹ := by
  change evalAt M 1 (coefficientPrimitive M (Polynomial.X^n))=_
  rw [primitive_pow M hM n,map_smul,eval_pow M hM]
  simp

def card6 (y : Fin 6 → K) (i : Fin 6) : Polynomial K :=
  (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ •
    (∏ j ∈ Finset.univ.erase i, (Polynomial.X-Polynomial.C (y j)))

def scalarWeights (M : Module.Basis ℕ K (Polynomial K)) (y : Fin 6 → K) : Fin 6 → K :=
  fun i => mean M (card6 y i)

/-- A monic degree-six division reduces the two linear rules to the
degree-five rule and the two exact nodal moments. All rules are scalar. -/
theorem rule_eq_of_degree5_and_nodal (L J : Polynomial K →ₗ[K] K)
    (N P : Polynomial K) (h5 : ∀ R, PolyBound 5 R → L R=J R)
    (hn : L N=0) (hxn : L (Polynomial.X*N)=0)
    (jn : J N=0) (jxn : J (Polynomial.X*N)=0)
    (d : ∃ (R : Polynomial K) (a b : K), PolyBound 5 R ∧
      P=R+a • N+b • (Polynomial.X*N)) :
    L P=J P := by
  obtain ⟨R,a,b,hR,he⟩ := d
  rw [he]
  simp only [map_add,map_smul,h5 R hR,hn,hxn,jn,jxn,smul_zero,add_zero]

/-- The exact moment functional for the original forward early taps.
It acts on a polynomial represented by its quadratic coefficients. -/
def moments (F0 U V0 : K) : Quad K →ₗ[K] K where
  toFun q := q.1*F0+q.2.1*U+q.2.2*V0
  map_add' p q := by
    change (p.1+q.1)*F0+(p.2.1+q.2.1)*U+(p.2.2+q.2.2)*V0=
      (p.1*F0+p.2.1*U+p.2.2*V0)+(q.1*F0+q.2.1*U+q.2.2*V0)
    ring
  map_smul' a q := by
    change (a*q.1)*F0+(a*q.2.1)*U+(a*q.2.2)*V0=a*(q.1*F0+q.2.1*U+q.2.2*V0)
    ring

theorem moments_apply (F0 U V0 : K) (q : Quad K) :
    moments F0 U V0 q=q.1*F0+q.2.1*U+q.2.2*V0 := rfl

def forwardLast (u : V K) (F0 U V0 : K) : V K →ₗ[K] K :=
  (moments F0 U V0).comp (interp u)+coordinate 3

/-- These three cardinal values are the early taps, with self one; not an
unchecked linear solve or an alternative chart. -/
theorem forwardLast_literal (u v : V K) (F0 U V0 : K) :
    forwardLast u F0 U V0 v =
      v 0 * moments F0 U V0 (ell (u 0) (u 1) (u 2)) +
      v 1 * moments F0 U V0 (ell (u 1) (u 0) (u 2)) +
      v 2 * moments F0 U V0 (ell (u 2) (u 0) (u 1)) + v 3 := by
  change moments F0 U V0 (interp u v)+v 3=_
  simp only [interp_apply,map_add,map_smul,smul_eq_mul]

theorem forwardLast_sample (u : V K) (F0 U V0 : K) (q : Quad K)
    (h01 : u 0 ≠ u 1) (h02 : u 0 ≠ u 2) (h12 : u 1 ≠ u 2) :
    forwardLast u F0 U V0 (sample u q)=moments F0 U V0 q+ev (u 3) q := by
  change moments F0 U V0 (interp u (sample u q))+sample u q 3=_
  rw [interp_sample u h01 h02 h12,sample_apply]

def Bs (s : K) : K := (1-s)*(3-s)
def qSeed (s T : K) : K := T^2-(s+3)*T+s
def Ld (s η T : K) : K := (Bs s-1)*(T-1)-η*(T+1-2*s)
def gdAt (s η d : K) : K := ((η/2)*(d-s)*qSeed s d)/(Ld s η d)
def Ud (d gd : K) : K := gd-d+d^2/2
def Vd (d η gd : K) : K := (2/3)*(1+d+(d-1)/η)*gd-d^2+d^3/3

/-- The defect moment equation is forced by the exact scalar g_d formula. -/
theorem original_defect_moment (s η d gd : K)
    (hb : Bs s≠0) (he : η≠0)
    (hL : Ld s η d*gd=(η/2)*(d-s)*qSeed s d) :
    moments (d-1) (Ud d gd) (Vd d η gd) (seedQuad s (3/(2*Bs s))) =
      (d-1)*gd/η := by
  let W := moments (d-1) (Ud d gd) (Vd d η gd) (seedQuad s (3/(2*Bs s)))
  have eq :
      (η*Bs s)*(W-(d-1)*gd/η)=-(Ld s η d*gd-(η/2)*(d-s)*qSeed s d) := by
    dsimp [W]
    simp only [moments_apply,Ud,Vd,seedQuad,Ld,qSeed]
    field_simp [hb,he] <;> ring
  rw [hL,sub_self,neg_zero] at eq
  exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left (mul_ne_zero he hb))

/-- After defining the row by its three cardinal values, it satisfies the
same two remaining equations of the old Cramer system. -/
theorem forward_cleared_moment_system (s η d gd : K)
    (hb : Bs s≠0) (he : η≠0)
    (hL : Ld s η d*gd=(η/2)*(d-s)*qSeed s d) :
    let U := Ud d gd
    let V0 := Vd d η gd
    let W := moments (d-1) U V0 (seedQuad s (3/(2*Bs s)))
    (3/2)*V0-W-(1+d)*U = -d*(d-1) ∧
      (d-1)*U-η*W=-(d-1)*(d-d^2/2) := by
  dsimp
  rw [original_defect_moment s η d gd hb he hL]
  constructor <;> simp only [Ud,Vd] <;> field_simp [he] <;> ring

def linearFactor (x : K) : Polynomial K := Polynomial.X-Polynomial.C x
def atOne (M : Module.Basis ℕ K (Polynomial K)) (x : K) (P : Polynomial K) :
    Polynomial K := (evalAt M x P)⁻¹ • P

def avg (M : Module.Basis ℕ K (Polynomial K)) (z : K) (P : Polynomial K) : K :=
  evalAt M z (coefficientPrimitive M P)/z

def aAt (s : K) : K := (1+s)/2
def zAt (s : K) : K := aAt s+s
def hAt (s : K) : K := aAt s-1
def g1At (s : K) : K := 1/2+hAt s-(hAt s)^2/2
def etaAt (s : K) : K := 2*g1At s

def cubic (u v w : K) : Polynomial K := linearFactor u*linearFactor v*linearFactor w
def Jpoly (s t : K) : Polynomial K := cubic s t 1
def Zpoly (s t : K) : Polynomial K := linearFactor (aAt s)*Jpoly s t

def μ (M : Module.Basis ℕ K (Polynomial K)) (s t : K) (j : ℕ) : K :=
  avg M (zAt s) (Polynomial.X^j*Zpoly s t)

def momentDet (M : Module.Basis ℕ K (Polynomial K)) (s t : K) : K :=
  μ M s t 0*μ M s t 2-(μ M s t 1)^2

def beta1 (M : Module.Basis ℕ K (Polynomial K)) (s t : K) : K :=
  (μ M s t 1*μ M s t 2-μ M s t 0*μ M s t 3)/momentDet M s t

def beta0 (M : Module.Basis ℕ K (Polynomial K)) (s t : K) : K :=
  (μ M s t 1*μ M s t 3-(μ M s t 2)^2)/momentDet M s t

def quadraticAt (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : K :=
  c^2+beta1 M s t*c+beta0 M s t

def bStar (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : K :=
  -beta1 M s t-c

theorem quadratic_factors (M : Module.Basis ℕ K (Polynomial K)) (s t c : K)
    (hc : quadraticAt M s t c=0) (u : K) :
    quadraticAt M s t u=(u-bStar M s t c)*(u-c) := by
  unfold quadraticAt at hc ⊢
  unfold bStar
  have hb : beta0 M s t = -c^2-beta1 M s t*c := by
    linear_combination hc
  rw [hb]
  ring

def ellAvg (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) (j : ℕ) : K :=
  avg M (zAt s) (Polynomial.X^j*linearFactor (aAt s)*linearFactor c*
    (coefficientPrimitive M (Jpoly s t)-Jpoly s t))

def selectorQuadAt (M : Module.Basis ℕ K (Polynomial K)) (s t c T : K) : K :=
  (T-zAt s+c)*(ellAvg M s t c 0*(zAt s-T)-ellAvg M s t c 1)

/-- Evaluate the exact unscaled affine response, not a polynomial root
approximation. Its affine identity follows by expanding the displayed terms. -/
def affineAt (M : Module.Basis ℕ K (Polynomial K)) (s t c T : K) : K :=
  let r := s/3
  let a := aAt s
  let η := etaAt s
  let μs := η*Bs s-3*(Bs s-1-η)
  let j := selectorQuadAt M s t c
  let aff := ((T-a)*j 1/(1-r)-(T-1)*j a/(a-r))/(1-a)
  Ld s η T*j r/((1-r)*(a-r))-(μs/3)*aff

def dAt (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : K :=
  -(affineAt M s t c 0)/(affineAt M s t c 1-affineAt M s t c 0)

def normalizedRows (h v : K) (last : V K →ₗ[K] K) : V K →ₗ[K] V K :=
  rows ![coordinate 0,h • coordinate 0+coordinate 1,
    (2*h-v) • coordinate 0+v • coordinate 1+coordinate 2,last]

def uAt (s T : K) : V K := ![1,aAt s,s,T]
def gAt (s g3 : K) : V K := ![1/2,g1At s,0,g3]

def forwardNormalized (s d : K) : Matrix (Fin 4) (Fin 4) K :=
  let gd := gdAt s (etaAt s) d
  matrixOf (normalizedRows (hAt s) (2/(hAt s-2))
    (forwardLast (uAt s d) (d-1) (Ud d gd) (Vd d (etaAt s) gd)))

def reverseNormalized (s t : K) : Matrix (Fin 4) (Fin 4) K :=
  matrixOf (normalizedRows (hAt s) (2/(hAt s-2)) (lastNormRow (uAt s t) t))

/-- The original six reverse sites and their physical forward clocks. -/
def yAt (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : Fin 6 → K :=
  ![1/zAt s, aAt s/zAt s, s/zAt s, t/zAt s, bStar M s t c/zAt s, c/zAt s]

def xAt (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : Fin 6 → K :=
  1 - yAt M s t c

/-- Literal geometry from s, t and the larger scalar quadrature root.
Every entry is a field/polynomial operation; no numerical tableau or
rank computation is used. The d coordinate is deterministic. -/
def geometry (M : Module.Basis ℕ K (Polynomial K)) (s t c : K) : Geometry K :=
  let a := aAt s
  let z := zAt s
  let γ := z⁻¹
  let d := dAt M s t c
  let y := yAt M s t c
  let x := xAt M s t c
  let gd := gdAt s (etaAt s) d
  let ru := cubic (x 1) (x 4) (x 5)
  let A := tiltA a d (1/2) gd
  let B := tiltB a d (g1At s) gd
  let clean := A • evalAt M γ+B • evalAt M (γ*a)+evalAt M (γ*d)
  let h4 := atOne M (x 4) (linearFactor (x 1)*linearFactor (x 5))
  let h5 := atOne M (x 5) (linearFactor (x 1)*linearFactor (x 4))
  let straighten := fun H => H-(clean H/clean ru) • ru
  { G := γ • forwardNormalized s d
    R := γ • reverseNormalized s t
    W := scalarWeights M y
    γ := γ
    Ex := evalSites M x
    Ey := evalSites M y
    I := coefficientPrimitive M
    Projf := polyProject (γ • uAt s d) ((γ^2) • gAt s gd)
    Projr := polyProject (γ • uAt s t) ((γ^2) • gAt s 0)
    HF := ![straighten h4,straighten h5]
    KR := ![atOne M (y 0) (cubic (y 2) (y 3) (y 4)),
      atOne M (y 4) (cubic (y 2) (y 3) (y 0))] }

theorem affineAt_affine (M : Module.Basis ℕ K (Polynomial K)) (s t c x : K) :
    affineAt M s t c x=
      (affineAt M s t c 1-affineAt M s t c 0)*x+affineAt M s t c 0 := by
  simp only [affineAt,Ld]
  ring

/-- No root evaluator is involved in the calibrated fourth coordinate. -/
theorem affineAt_dAt (M : Module.Basis ℕ K (Polynomial K)) (s t c : K)
    (h : affineAt M s t c 1-affineAt M s t c 0 ≠ 0) :
    affineAt M s t c (dAt M s t c)=0 := by
  rw [affineAt_affine]
  unfold dAt
  field_simp [h] <;> ring

theorem two_nodal_moment_equations (M : Module.Basis ℕ K (Polynomial K)) (s t : K)
    (h : momentDet M s t≠0) :
    beta0 M s t*μ M s t 0+beta1 M s t*μ M s t 1+μ M s t 2=0 ∧
    beta0 M s t*μ M s t 1+beta1 M s t*μ M s t 2+μ M s t 3=0 := by
  unfold beta0 beta1
  constructor <;> field_simp [h] <;> unfold momentDet <;> ring

/-- All four actual moments of the new forward row, without solving M f=m
or making a four-dimensional rank call. -/
theorem forward_last_frame (u g : V K) (s η d gd : K)
    (h01 : u 0≠u 1) (h02 : u 0≠u 2) (h12 : u 1≠u 2)
    (ht : u 3=d) (hg : g 3=gd)
    (hJ : interp u g=seedQuad s (3/(2*Bs s)))
    (hb : Bs s≠0) (he : η≠0)
    (hL : Ld s η d*gd=(η/2)*(d-s)*qSeed s d) :
    let F := forwardLast u (d-1) (Ud d gd) (Vd d η gd)
    F 1=d ∧ F u=d^2/2+gd ∧
    F (u^2)=d^3/3+(2/3)*(F g+d*gd) ∧ F g=gd+(d-1)*gd/η := by
  dsimp
  let F := forwardLast u (d-1) (Ud d gd) (Vd d η gd)
  have Fg : F g=gd+(d-1)*gd/η := by
    change moments (d-1) (Ud d gd) (Vd d η gd) (interp u g)+g 3=_
    rw [hJ,hg,original_defect_moment s η d gd hb he hL]
    ring
  have z0 : sample u ((1,0,0) : Quad K)=1 := by
    funext i
    simp [sample_apply,ev_apply]
  have z1 : sample u ((0,1,0) : Quad K)=u := by
    funext i
    simp [sample_apply,ev_apply]
  have z2 : sample u ((0,0,1) : Quad K)=u^2 := by
    funext i
    simp [sample_apply,ev_apply,Pi.pow_apply]
  refine ⟨?_,?_,?_,Fg⟩
  · rw [←z0,forwardLast_sample u _ _ _ _ h01 h02 h12,ht]
    simp [moments_apply,ev_apply] <;> ring
  · change F u = _
    rw [congrArg F z1.symm]
    change forwardLast u (d-1) (Ud d gd) (Vd d η gd) (sample u ((0,1,0) : Quad K)) = _
    rw [forwardLast_sample u _ _ _ _ h01 h02 h12, ht]
    simp [moments_apply,ev_apply,Ud] <;> ring
  · change F (u^2)=_
    rw [←z2]
    change forwardLast u (d-1) (Ud d gd) (Vd d η gd) (sample u ((0,0,1) : Quad K))=_
    rw [forwardLast_sample u _ _ _ _ h01 h02 h12,ht,Fg]
    simp [moments_apply,ev_apply,Vd] <;> ring

/-- These are exact polynomial sign hypotheses, not approximations to d.
The previously checked signs refer to the unscaled affineAt expression. -/
theorem calibrated_real_bracket (M : Module.Basis ℕ ℝ (Polynomial ℝ)) (s t c : ℝ)
    (hl : affineAt M s t c (15/4)<0) (hu : 0<affineAt M s t c 4) :
    (15/4 : ℝ)<dAt M s t c ∧ dAt M s t c<4 ∧ affineAt M s t c (dAt M s t c)=0 := by
  rw [affineAt_affine M s t c (15/4)] at hl
  rw [affineAt_affine M s t c 4] at hu
  obtain ⟨ha,hlo,hhi,_⟩ := affine_ratio_of_bracket (by norm_num) hl hu
  exact ⟨hlo,hhi,affineAt_dAt M s t c (ne_of_gt ha)⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
