module

public import RKCert.ERKOrderNineFiveSixFG

@[expose] public section
namespace RKCert.Paired
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The compact degree-eight factor before substituting the Vieta root
sum. This exact integer polynomial is a witness, not an elimination
oracle; Lean checks the full factorization below. -/
def sixOnK8Coeff2 (r u v : K) : K :=
  ((504*u*v^3 - 945*u*v^2 + 540*u*v - 81*u - 504*v^3 + 945*v^2 - 549*v + 90)*r^2 +
      (-756*u^2*v^3 + 1512*u^2*v^2 - 972*u^2*v + 192*u^2 + 504*u*v^3 - 1107*u*v^2 + 816*u*v - 201*u + 252*v^3 - 393*v^2 + 150*v + 3)*r +
      (756*u^2*v^3 - 1512*u^2*v^2 + 984*u^2*v - 204*u^2 - 1008*u*v^3 + 2037*u*v^2 - 1350*u*v + 291*u + 252*v^3 - 537*v^2 + 381*v - 90))

def sixOnK8Coeff1 (r u v : K) : K :=
  ((-168*u^2*v^2 + 336*u^2*v - 168*u^2 - 504*u*v^3 + 1092*u*v^2 - 888*u*v + 276*u + 504*v^3 - 924*v^2 + 564*v - 120)*r^3 +
      (224*u^3*v^2 - 448*u^3*v + 224*u^3 + 224*u^2*v^3 - 588*u^2*v^2 + 576*u^2*v - 204*u^2 - 28*u*v^3 + 72*u*v^2 + 16*u*v - 52*u - 196*v^3 + 288*v^2 - 148*v + 40)*r^2 +
      (672*u^3*v^3 - 1456*u^3*v^2 + 1184*u^3*v - 368*u^3 - 952*u^2*v^3 + 2004*u^2*v^2 - 1608*u^2*v + 508*u^2 + 524*u*v^3 - 1008*u*v^2 + 684*u*v - 176*u - 260*v^3 + 484*v^2 - 272*v + 40)*r +
      (-672*u^3*v^3 + 1232*u^3*v^2 - 752*u^3*v + 160*u^3 + 728*u^2*v^3 - 1244*u^2*v^2 + 704*u^2*v - 148*u^2 + 28*u*v^3 - 184*u*v^2 + 200*u*v - 52*u - 68*v^3 + 176*v^2 - 148*v + 40))

def sixOnK8Coeff0 (r u v : K) : K :=
  ((756*u^2*v^3 - 1260*u^2*v^2 + 576*u^2*v - 36*u^2 - 756*u*v^3 + 1224*u*v^2 - 522*u*v + 18*u + 18*v^2 - 36*v + 18)*r^3 +
      (-1008*u^3*v^3 + 1680*u^3*v^2 - 768*u^3*v + 48*u^3 + 546*u^2*v^3 - 900*u^2*v^2 + 390*u^2*v - 12*u^2 + 510*u*v^3 - 834*u*v^2 + 378*u*v - 30*u - 24*v^3 + 42*v^2 - 12*v - 6)*r^2 +
      (1008*u^3*v^3 - 1632*u^3*v^2 + 696*u^3*v - 24*u^3 - 1362*u^2*v^3 + 2208*u^2*v^2 - 930*u^2*v + 24*u^2 + 318*u*v^3 - 516*u*v^2 + 204*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6)*r +
      (-24*u^3*v^2 + 48*u^3*v - 24*u^3 + 30*u^2*v^3 - 36*u^2*v^2 - 18*u^2*v + 24*u^2 - 42*u*v^3 + 90*u*v^2 - 54*u*v + 6*u + 12*v^3 - 30*v^2 + 24*v - 6))
/-- Exact integer compatibility expression before Vieta substitution. -/
def sixOnK8Raw (h r u v : K) : K :=
  sixOnK8Coeff2 r u v*h^2+sixOnK8Coeff1 r u v*h+sixOnK8Coeff0 r u v

def sixOnK8 (h u v l : K) : K := sixOnK8Raw h (2-l-h-u-v) u v

noncomputable def sixOnW (h r u v : K) : K :=
  sixOnF u v (fixedRadauP0 h)*sixOnG r u v (fixedRadauP1 h) -
    sixOnF u v (fixedRadauP1 h)*sixOnG r u v (fixedRadauP0 h)

noncomputable def sixOnK8Factor (h r u v : K) : K :=
  (3/14)*lobattoCubic.eval v*h*(u-v)*(v-r)*radauLateD u v*(u-r)

private noncomputable def sixOnDMinor (r u v : K) (i j : ℕ) : K :=
  sixOnF u v (fun x=>x^i)*sixOnG r u v (fun x=>x^j) -
    sixOnF u v (fun x=>x^j)*sixOnG r u v (fun x=>x^i)

private noncomputable def k8Common (r u v : K) : K :=
  (3/14)*lobattoCubic.eval v*(u-v)*(v-r)*radauLateD u v*(u-r)

set_option maxHeartbeats 1600000 in
private theorem k8_component2 (r u v : K) :
    9*sixOnDMinor r u v 0 1=k8Common r u v*sixOnK8Coeff2 r u v := by
  simp [sixOnDMinor,k8Common,sixOnK8Coeff2,sixOnF,sixOnG,lobattoCubic,radauLateD,radauLateDn,radauLateL]
  ring

set_option maxHeartbeats 1600000 in
private theorem k8_component1 (r u v : K) :
    -12*sixOnDMinor r u v 0 2=k8Common r u v*sixOnK8Coeff1 r u v := by
  simp [sixOnDMinor,k8Common,sixOnK8Coeff1,sixOnF,sixOnG,lobattoCubic,radauLateD,radauLateDn,radauLateL]
  ring

set_option maxHeartbeats 1600000 in
private theorem k8_component0 (r u v : K) :
    18*sixOnDMinor r u v 1 2=k8Common r u v*sixOnK8Coeff0 r u v := by
  simp [sixOnDMinor,k8Common,sixOnK8Coeff0,sixOnF,sixOnG,lobattoCubic,radauLateD,radauLateDn,radauLateL]
  ring

omit [CharZero K] in
private theorem sixOnW_expand (h r u v : K) :
    sixOnW h r u v =
      h^3*(9*sixOnDMinor r u v 0 1)+h^2*(-12*sixOnDMinor r u v 0 2)+
        h*(18*sixOnDMinor r u v 1 2) := by
  simp [sixOnW,sixOnDMinor,sixOnF,sixOnG,fixedRadauP0,fixedRadauP1]
  ring

theorem sixOnW_factor (h r u v : K) :
    sixOnW h r u v=sixOnK8Factor h r u v * sixOnK8Raw h r u v := by
  have e : sixOnK8Factor h r u v=k8Common r u v*h := by
    unfold sixOnK8Factor k8Common
    ring
  rw [sixOnW_expand,k8_component2,k8_component1,k8_component0,e,sixOnK8Raw]
  ring

omit [CharZero K] in
theorem sixOnW_zero_of_FG {h r u v t : K}
    (f : sixOnF u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0)
    (g : sixOnG r u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0) :
    sixOnW h r u v=0 := by
  have hf : sixOnF u v (fixedRadauP0 h)+t*sixOnF u v (fixedRadauP1 h)=0 := by
    unfold sixOnF at f ⊢
    linear_combination f
  have hg : sixOnG r u v (fixedRadauP0 h)+t*sixOnG r u v (fixedRadauP1 h)=0 := by
    unfold sixOnG at g ⊢
    linear_combination g
  unfold sixOnW
  linear_combination sixOnG r u v (fixedRadauP1 h)*hf-sixOnF u v (fixedRadauP1 h)*hg

theorem sixOnK8Raw_zero_of_FG {h r u v t : K}
    (hh : h≠0) (huv : u≠v) (hvr : v≠r) (hur : u≠r)
    (hd : radauLateD u v≠0) (hv : lobattoCubic.eval v≠0)
    (f : sixOnF u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0)
    (g : sixOnG r u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0) :
    sixOnK8Raw h r u v=0 := by
  have h := sixOnW_zero_of_FG f g
  rw [sixOnW_factor] at h
  apply (mul_eq_zero.mp h).resolve_left
  unfold sixOnK8Factor
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) hv) hh) (sub_ne_zero.mpr huv)) (sub_ne_zero.mpr hvr))
    hd) (sub_ne_zero.mpr hur)

end RKCert.Paired

