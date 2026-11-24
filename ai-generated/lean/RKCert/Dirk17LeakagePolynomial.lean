module
public import RKCert.Dirk17EarlyScalars
public import RKCert.Dirk17ThreePortTable
@[expose] public section
namespace RKCert.RadauEight.EarlyPort
open Polynomial RKCert.Paired RKCert.Endpoint RKCert.FixedFactor

def left7Coeffs : Fin 8→ℤ := ![64,-2016,20160,-92400,221760,-288288,192192,-51480]

def scaledLeft7 {R:Type*} [CommRing R] (x:R):R :=
  ∑ i:Fin 8,((left7Coeffs i:ℤ):R)*(24310:R)^(7-i.val)*x^i.val

private noncomputable def leftTest : MvPolynomial (Fin 1) ℤ := scaledLeft7 (MvPolynomial.X 0)

private theorem eval_leftTest {R:Type*} [CommRing R] (a:Fin 1→R):
    zEval leftTest a=scaledLeft7 (a 0):=by
  let f:=MvPolynomial.eval₂Hom (Int.castRingHom R) a
  change f (scaledLeft7 (MvPolynomial.X 0))=_
  simp only [scaledLeft7,map_sum,map_mul,map_intCast,map_ofNat,map_pow]
  simp only [f,MvPolynomial.eval₂Hom_X']

theorem scaledLeft7_nonzero_on_grid :
    gridp.tail.all (fun x=>decide (scaledLeft7 x≠0))=true:=by decide +kernel

variable {K:Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem scaledLeft7_agrees (u:K):scaledLeft7 ((24310:K)*u)=(24310:K)^7*(radauLeft7:K[X]).eval u:=by
  classical
  unfold scaledLeft7 radauLeft7
  rw [ofFn_eq_sum_monomial,eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  have h:(radauLeft7_coeff (K:=K)) i=((left7Coeffs i:ℤ):K):=by fin_cases i <;> norm_num [radauLeft7_coeff,left7Coeffs]
  rw [eval_monomial,h,mul_pow]
  have add:7-i.val+i.val=7:=Nat.sub_add_cancel (by have:=i.isLt;omega)
  calc _ = ((left7Coeffs i:ℤ):K)*(24310:K)^(7-i.val+i.val)*u^i.val := by rw [pow_add];ring
       _ = _ := by rw [add];ring

/-- No nonzero order-17 early Radau clock is a root of the sole scalar
grade-ten leakage polynomial, X times the order-15 left reproducer. -/
theorem leakage_nonzero_at_grid (u:K) (un:u≠0) (ur:(grid K).eval u=0):
    (EarlyFifteen.relation K).eval u≠0:=by
  have r:(scaledNonzero.map (Int.castRingHom K)).eval ((24310:K)*u)=0:=by
    have e:=scale_eqn u
    rw [ur,mul_zero,factor_scaled,Polynomial.map_mul,Polynomial.map_X,eval_mul,eval_X] at e
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) un)
  have nz:=split_prime_root_tuple 293177 scaledNonzero nonzero_monic gridp.tail split_nonzero
    (fun t ht=>by rw [split_nonzero];exact simple_product_of_nodup gridp.tail (by decide) ht)
    leftTest (fun _ _=>False) (fun a h _=>by
      rw [eval_leftTest]
      exact decide_eq_true_eq.mp (List.all_eq_true.mp scaledLeft7_nonzero_on_grid _ (h 0)))
    (fun _=>24310*u) (fun _=>r) (fun _ _ h=>h.elim)
  rw [eval_leftTest,scaledLeft7_agrees] at nz
  rw [EarlyFifteen.relation,eval_mul,eval_X]
  exact mul_ne_zero un (mul_ne_zero_iff.mp nz).2

end RKCert.RadauEight.EarlyPort

namespace RKCert.Paired.Seventeen.Early
open Polynomial RKCert.FixedFactor RKCert.RadauEight
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]

theorem leakage_shift_independent (a b t:K)
    (eq:X*(C a*EarlyFifteen.relation K)-C b*EarlyFifteen.relation K=C t*grid K):
    a=0 ∧ b=0:=by
  have left1:(EarlyFifteen.relation K).coeff 1=64:=by
    rw [EarlyFifteen.relation,coeff_X_mul]
    change (ofFn 8 (radauLeft7_coeff (K:=K))).coeff 0=_
    rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
    norm_num [radauLeft7_coeff]
  have left2:(EarlyFifteen.relation K).coeff 2=(-2016:K):=by
    rw [EarlyFifteen.relation,coeff_X_mul]
    change (ofFn 8 (radauLeft7_coeff (K:=K))).coeff 1=_
    rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
    norm_num [radauLeft7_coeff]
  have left3:(EarlyFifteen.relation K).coeff 3=(20160:K):=by
    rw [EarlyFifteen.relation,coeff_X_mul]
    change (ofFn 8 (radauLeft7_coeff (K:=K))).coeff 2=_
    rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
    norm_num [radauLeft7_coeff]
  have left0:(EarlyFifteen.relation K).coeff 0=0:=by simp [EarlyFifteen.relation]
  have right1:(grid K).coeff 1=9:=by norm_num [grid,coeff_map,coeff_horner,raw,readCoeff]
  have right2:(grid K).coeff 2=(-360:K):=by norm_num [grid,coeff_map,coeff_horner,raw,readCoeff]
  have right3:(grid K).coeff 3=(4620:K):=by norm_num [grid,coeff_map,coeff_horner,raw,readCoeff]
  have x1:a*0-b*64=t*9:=by
    have h:=congrArg (fun P:K[X]=>P.coeff 1) eq
    simpa only [coeff_sub,coeff_X_mul,coeff_C_mul,left0,left1,right1] using h
  have x2:a*64-b*(-2016)=t*(-360):=by
    have h:=congrArg (fun P:K[X]=>P.coeff 2) eq
    simpa only [coeff_sub,coeff_X_mul,coeff_C_mul,left1,left2,right2] using h
  have x3:a*(-2016)-b*20160=t*4620:=by
    have h:=congrArg (fun P:K[X]=>P.coeff 3) eq
    simpa only [coeff_sub,coeff_X_mul,coeff_C_mul,left2,left3,right3] using h
  constructor
  · linear_combination (-45/56:K)*x1-(5/112:K)*x2-(3/1568:K)*x3
  · linear_combination (-20/119:K)*x1-(27/3808:K)*x2-(3/13328:K)*x3
end
end RKCert.Paired.Seventeen.Early
