module

public import RKCert.ERKOrderNineFixedRadauCharZero

@[expose] public section

/-! # Exact scalar reconstruction from the late Radau columns -/
namespace RKCert.Paired

variable {K : Type*} [Field K] [CharZero K]

def radauLateD (u v : K) : K := 2*u-3*v+1

def radauLateDn (u v x : K) : K :=
  3*x^2+(2-4*u-4*v)*x+1-2*u-2*v+6*u*v

def radauLateL (u v x : K) : K :=
  4*u^2-5*u*v+2*v-1-3*(u-v)*x

def radauLateE (u v nu a beta gamma x : K) : K :=
  beta+gamma*x-(1+u+v)*a+(u+v+u*v)*nu

/-- The second, first, and third late columns give both necessary
weight equations. No affine coefficient is used as a denominator. -/
theorem fixedRadau_late_column_equations
    (u v r bu bv br su sv sr nu a beta gamma : K)
    (huv : u≠v) (hv : v≠1) (hsu : su≠0) (hsv : sv≠0) (hnu : nu≠0)
    (hV1 : bv*(1-v)^2=2*nu*sv)
    (hV2 : bv*(v+2)*(1-v)^2=3*a*sv)
    (hU2 : bu*(1-u)^2*radauLateD u v=6*(a-(1+v)*nu)*su)
    (hU3 : 12*radauLateE u v nu a beta gamma u*su=bu*(1-u)^2*radauLateDn u v u)
    (hV3 : 12*radauLateE u v nu a beta gamma v*sv=bv*(1-v)^2*radauLateDn u v v)
    (hR3 : 12*radauLateE u v nu a beta gamma r*sr=br*(1-r)^2*radauLateDn u v r) :
    radauLateD u v≠0 ∧
      bu*(1-u)^2*radauLateD u v=2*nu*(1-v)*su ∧
      br*(1-r)^2*radauLateD u v*radauLateDn u v r= -2*nu*(1-v)*radauLateL u v r*sr := by
  have hA : 3*a=2*nu*(v+2) := by
    apply mul_right_cancel₀ hsv
    linear_combination (v+2)*hV1-hV2
  have hU : bu*(1-u)^2*radauLateD u v=2*nu*(1-v)*su := by
    linear_combination hU2+2*su*hA
  have hD : radauLateD u v≠0 := by
    intro h; rw [h,mul_zero] at hU
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2:K)≠0) hnu)
      (sub_ne_zero.mpr (Ne.symm hv))) hsu hU.symm
  have hiu : radauLateDn u v u+radauLateL u v u=0 := by
    unfold radauLateDn radauLateL; ring
  have hiv : radauLateD u v*radauLateDn u v v+(1-v)*radauLateL u v v=0 := by
    unfold radauLateD radauLateDn radauLateL; ring
  let W (x : K) := 6*radauLateD u v*radauLateE u v nu a beta gamma x+
    nu*(1-v)*radauLateL u v x
  have hWu : W u=0 := by
    apply (mul_eq_zero.mp (?_ : W u*su=0)).resolve_right
    · exact hsu
    · dsimp [W]
      linear_combination (radauLateD u v/2)*hU3+(radauLateDn u v u/2)*hU+
        nu*(1-v)*su*hiu
  have hWv : W v=0 := by
    apply (mul_eq_zero.mp (?_ : W v*sv=0)).resolve_right
    · exact hsv
    · dsimp [W]
      linear_combination (radauLateD u v/2)*hV3+
        (radauLateD u v*radauLateDn u v v/2)*hV1+nu*sv*hiv
  let d := W 0
  let m := 6*radauLateD u v*gamma-3*nu*(1-v)*(u-v)
  have hW (x : K) : W x=d+m*x := by
    dsimp [W,d,m,radauLateE,radauLateL]
    ring
  rw [hW u] at hWu
  rw [hW v] at hWv
  have hm : m=0 := (mul_eq_zero.mp (show m*(u-v)=0 by linear_combination hWu-hWv)).resolve_right
    (sub_ne_zero.mpr huv)
  have hd : d=0 := by simpa [hm] using hWv
  have hFinal : W r=0 := by rw [hW,hm,hd,zero_mul,add_zero]
  refine ⟨hD,hU,?_⟩
  dsimp [W] at hFinal
  linear_combination -radauLateD u v*hR3+2*sr*hFinal

omit [CharZero K] in
/-- The output quadrature and the annihilating state row share the
same interpolation denominator at each on node. Cancel only their
nonzero common quadrature normalization, not an F/G coefficient. -/
theorem fixedRadau_FG_of_late_weights (u v r bu bv br su sv sr nu qU qV qR TZ SZ : K)
    (P : K → K) (hT : TZ≠0)
    (hV : bv*(1-v)^2=2*nu*sv)
    (hU : bu*(1-u)^2*radauLateD u v=2*nu*(1-v)*su)
    (hR : br*(1-r)^2*radauLateD u v*radauLateDn u v r= -2*nu*(1-v)*radauLateL u v r*sr)
    (hTU : bu*qU*fixedRadauT3 u=TZ)
    (hTV : bv*qV*fixedRadauT3 v=TZ)
    (hTR : br*qR*fixedRadauT3 r=TZ)
    (hSU : su*P u*qU=SZ) (hSV : sv*P v*qV=SZ) (hSR : sr*P r*qR=SZ) :
    fixedRadauF u v P=0 ∧ fixedRadauG r u v P=0 := by
  have eu : TZ*(1-u)^2*radauLateD u v*P u=2*nu*(1-v)*SZ*fixedRadauT3 u := by
    linear_combination P u*qU*fixedRadauT3 u*hU -
      (1-u)^2*radauLateD u v*P u*hTU+2*nu*(1-v)*fixedRadauT3 u*hSU
  have ev : TZ*(1-v)^2*P v=2*nu*SZ*fixedRadauT3 v := by
    linear_combination P v*qV*fixedRadauT3 v*hV-(1-v)^2*P v*hTV+2*nu*fixedRadauT3 v*hSV
  have er : TZ*(1-r)^2*radauLateD u v*radauLateDn u v r*P r =
      -2*nu*(1-v)*radauLateL u v r*SZ*fixedRadauT3 r := by
    linear_combination P r*qR*fixedRadauT3 r*hR-
      (1-r)^2*radauLateD u v*radauLateDn u v r*P r*hTR-
      2*nu*(1-v)*radauLateL u v r*fixedRadauT3 r*hSR
  constructor
  · apply (mul_eq_zero.mp (?_ : TZ*fixedRadauF u v P=0)).resolve_left
    · exact hT
    · unfold fixedRadauF radauLateD at *
      linear_combination fixedRadauT3 v*eu-(1-v)*fixedRadauT3 u*ev
  · apply (mul_eq_zero.mp (?_ : TZ*fixedRadauG r u v P=0)).resolve_left
    · exact hT
    · unfold fixedRadauG radauLateD radauLateDn radauLateL at *
      dsimp only
      linear_combination fixedRadauT3 v*er+(1-v)*fixedRadauT3 r*
        (4*u^2-5*u*v+2*v-1-3*(u-v)*r)*ev

end RKCert.Paired

