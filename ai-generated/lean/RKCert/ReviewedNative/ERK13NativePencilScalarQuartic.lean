module
public import RKCert.ReviewedNative.ERK13NativePencilQuarticPorts
public import RKCert.ReviewedNative.NativePencilFivePrimitive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! # Recover the certified complementary quartic from its actual three roots

The true factor R becomes a nonzero scalar multiple of the certified
quarticMask after tX substitution. Distinct roots are used only to divide the
cubic Q, never to assume that a general mesh splits or is squarefree. -/
namespace RKResearch.Certified.Graded.ERK13NativePencil
open ERK13NativeFirst RKResearch Polynomial NativeLobatto NativePencilPorts
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private theorem cubic_with_three_roots (Q : K[X]) (qd : Q.natDegree=3)
    (t u : K) (tn : t≠0) (un : u≠0) (tu : t≠u)
    (q0 : Q.eval 0=0) (qt : Q.eval t=0) (qu : Q.eval u=0) :
    ∃ c : K,c≠0 ∧ Q=X*((X-C t)*(X-C u)*C c) := by
  obtain ⟨Q₁,e₁⟩ := X_dvd_iff.mpr (show Q.coeff 0=0 by rw [coeff_zero_eq_eval_zero]; exact q0)
  rw [e₁,eval_mul,eval_X] at qt qu
  obtain ⟨Q₂,e₂⟩ := (dvd_iff_isRoot (a:=t)).mpr ((mul_eq_zero.mp qt).resolve_left tn)
  have ur := (mul_eq_zero.mp qu).resolve_left un
  rw [e₂,eval_mul,eval_sub,eval_X,eval_C] at ur
  obtain ⟨Q₃,e₃⟩ := (dvd_iff_isRoot (a:=u)).mpr ((mul_eq_zero.mp ur).resolve_left (sub_ne_zero.mpr tu.symm))
  have n₁ : Q₁≠0 := by intro h; rw [e₁,h,mul_zero,natDegree_zero] at qd; omega
  have n₂ : Q₂≠0 := by intro h; exact n₁ (by rw [e₂,h,mul_zero])
  have n₃ : Q₃≠0 := by intro h; exact n₂ (by rw [e₃,h,mul_zero])
  rw [e₁,natDegree_X_mul n₁,e₂,natDegree_mul (X_sub_C_ne_zero _) n₂,natDegree_X_sub_C,e₃,
    natDegree_mul (X_sub_C_ne_zero _) n₃,natDegree_X_sub_C] at qd
  have f := eq_C_of_natDegree_eq_zero (show Q₃.natDegree=0 by omega)
  refine ⟨Q₃.coeff 0,fun z=>n₃ (by rw [f,z,map_zero]),?_⟩
  rw [e₁,e₂,e₃]
  conv_lhs => rw [f]
  ring

private theorem eval_pencil (a b x : K) :
    (pencilB a b).eval x=a*radauQuotient x+b*lobattoValue x := by
  simp [pencilB,radauQuotient,lobattoValue]

private theorem eval_contrast (t z : K) :
    (pencilContrast t).eval z=lobattoValue t*radauQuotient (t*z)-radauQuotient t*lobattoValue (t*z) := by
  simp [pencilContrast,lobattoValue,radauQuotient]

private theorem scalar_moment (R : K[X]) (c t : K) (n : ℕ) :
    moment (C c*R) n t=c*moment R n t := by
  have eq : X^n*(C c*R)=c • (X^n*R) := by rw [smul_eq_C_mul]; ring
  simp only [moment,eq,map_smul,eval_smul,smul_eq_mul]

theorem certified_quartic_pencil_cut : QuarticPencilCut K := by
  intro a b s t u R Q an bn tn un tu _rd qd _r0 fac q0 qt qu i1 i2 mix
  let z := u/t
  have tz : t*z=u := by dsimp only [z]; field_simp [tn] <;> ring
  have zn : z≠0 := div_ne_zero un tn
  have z1 : z≠1 := by intro h; apply tu; simpa only [h,mul_one] using tz
  obtain ⟨c,cn,qshape⟩ := cubic_with_three_roots Q qd t u tn un tu q0 qt qu
  have root (x : K) (xn : x≠0) (qx : Q.eval x=0) :
      a*radauQuotient x+b*lobattoValue x=0 := by
    have h := congrArg (fun T : K[X]=>T.eval x) fac
    simp only [eval_mul,eval_X,eval_pencil,qx,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left xn
  have rt := root t tn qt
  have ru := root u un qu
  have pair : lobattoValue t*radauQuotient u-radauQuotient t*lobattoValue u=0 := by
    have h : a*(lobattoValue t*radauQuotient u-radauQuotient t*lobattoValue u)=0 := by
      linear_combination (lobattoValue t)*ru-(lobattoValue u)*rt
    exact (mul_eq_zero.mp h).resolve_left an
  let d := -radauQuotient t/b
  have da : d*a=lobattoValue t := by dsimp only [d]; field_simp [bn]; linear_combination -rt
  have db : d*b= -radauQuotient t := by dsimp only [d]; exact div_mul_cancel₀ _ bn
  have dn : d≠0 := by
    intro zero
    have fz : lobattoValue t=0 := by simpa only [zero,zero_mul] using da.symm
    have jz : radauQuotient t=0 := (mul_eq_zero.mp (by simpa only [fz,mul_zero,add_zero] using rt)).resolve_left an
    exact lobatto_radau_not_both_zero t ⟨fz,jz⟩
  have Bform : pencilB a b=R*((X-C t)*(X-C u)*C c) := by
    apply mul_left_cancel₀ (X_ne_zero : (X:K[X])≠0)
    rw [qshape] at fac
    linear_combination fac
  let V := C t*X
  have contrast : pencilContrast t=C d*(pencilB a b).comp V := by
    letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    rw [eval_contrast,eval_mul,eval_C,eval_comp,eval_pencil]
    simp only [V,eval_mul,eval_C,eval_X]
    calc
      _=(d*a)*radauQuotient (t*x)+(d*b)*lobattoValue (t*x) := by rw [da,db]; ring
      _=_ := by ring
  have xt : V-C t=C t*(X-1) := by dsimp [V]; ring
  have xu : V-C u=C t*(X-C z) := by rw [←tz,map_mul]; dsimp only [V]; ring
  have shape : pencilContrast t=(X-1)*(X-C z)*(C t)^2*(C (d*c)*R.comp V) := by
    rw [contrast,Bform]
    simp only [mul_comp,sub_comp,X_comp,C_comp,xt,xu,map_mul]
    ring
  have div := quartic_division_identity z t
  have atz : (pencilContrast t).eval z=0 := by rw [eval_contrast,tz]; exact pair
  have rem : t*NativePencilQuarticInteger.secondPort z t=0 := by
    have h := congrArg (fun T : K[X]=>T.eval z) div
    simp only [atz,eval_add,eval_mul,eval_sub,eval_X,eval_one,eval_C,eval_pow,sub_self,mul_zero,
      zero_mul,zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr z1)
  rw [rem,map_zero,mul_zero,add_zero] at div
  have nprod : (X-1)*(X-C z)*(C t)^2≠(0:K[X]) :=
    mul_ne_zero (mul_ne_zero (by simpa using (X_sub_C_ne_zero (1:K))) (X_sub_C_ne_zero _))
      (pow_ne_zero _ (C_ne_zero.mpr tn))
  have wf : quarticMask z t=C (d*c)*R.comp V := mul_left_cancel₀ nprod (div.symm.trans shape)
  have scale (n : ℕ) (x : K) :
      t^(n+1)*moment (quarticMask z t) n x=(d*c)*moment R n (t*x) := by
    rw [wf,scalar_moment]
    linear_combination (d*c)*moment_dilate R n t x
  have x1 := scale 1 1
  have x2 := scale 2 1
  have z2 := scale 2 z
  have zM := scale 1 z
  simp only [mul_one] at x1 x2
  rw [tz] at z2 zM
  change moment R 1 t=0 at i1
  change moment R 2 t=s*radauValue t at i2
  change moment R 2 u-t*moment R 1 u=s*radauValue u at mix
  have first : moment (quarticMask z t) 1 1=0 := (mul_eq_zero.mp (x1.trans (by rw [i1,mul_zero]))).resolve_left (pow_ne_zero _ tn)
  have scaled : t^3*(z*lobattoValue u*moment (quarticMask z t) 2 1-
      lobattoValue t*(moment (quarticMask z t) 2 z-moment (quarticMask z t) 1 z))=0 := by
    calc
      t^3*(z*lobattoValue u*moment (quarticMask z t) 2 1-
          lobattoValue t*(moment (quarticMask z t) 2 z-moment (quarticMask z t) 1 z)) =
        (d*c)*(z*lobattoValue u*moment R 2 t-lobattoValue t*(moment R 2 u-t*moment R 1 u)) := by
          linear_combination (z*lobattoValue u)*x2-(lobattoValue t)*z2+(t*lobattoValue t)*zM
      _=0 := by
        rw [i2,mix]
        simp only [radauValue]
        calc
          _ = -(d*c*s*u)*(lobattoValue t*radauQuotient u-radauQuotient t*lobattoValue u) := by rw [←tz]; ring
          _=0 := by rw [pair,mul_zero]
  have high := (mul_eq_zero.mp scaled).resolve_left (pow_ne_zero 3 tn)
  apply quartic_pencil_ports_incompatible z t z1 zn tn (by rwa [tz]) (by simpa only [moment,pow_one] using first)
  simpa only [moment,pow_one,tz] using high

end
end RKResearch.Certified.Graded.ERK13NativePencil
