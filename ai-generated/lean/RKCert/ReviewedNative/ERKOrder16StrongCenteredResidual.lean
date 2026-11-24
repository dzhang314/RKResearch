module

public import RKCert.ReviewedNative.PositiveIntervalGrid19

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-free residuals for one or two chronological cuts -/
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial RKCert.ReviewedNative.PositiveRule19

noncomputable section
variable {K : Type*} [CommRing K]

def middleDelta (a z r s : K) : K := (1+z-a)*r*s+z*(a-r-s)

theorem middleDelta_mul_left (a z r s : K) :
    a*middleDelta a z r s = r*s*(1-a)*(a-z)+z*(a-r)*(a-s) := by
  unfold middleDelta
  ring

theorem middle_scaled_polynomial (a z r s : K) :
    C (middleDelta a z r s)*X-C (z-r*s)*(X*(C a-X))-
         C (r*s)*((1-X)*(X-C z))=C z*((X-C r)*(X-C s)) := by
  simp only [middleDelta,map_add,map_sub,map_mul,map_one]
  ring

theorem left_scaled_polynomial (a s : K) :
    C (a-s)*X-X*(C a-X)=X*(X-C s) := by
  simp only [map_sub]
  ring

theorem right_scaled_polynomial (z s : K) :
    C (s-z)*(1-X)-(1-X)*(X-C z)=(1-X)*(C s-X) := by
  simp only [map_sub]
  ring

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem middleDelta_pos {a z r s : K} (hz : 0<z) (zr : z<r)
    (rs : r<s) (sa : s<a) (a1 : a<1) : 0<middleDelta a z r s := by
  have hr := hz.trans zr
  have hs := hr.trans rs
  have ha := hs.trans sa
  have za := zr.trans (rs.trans sa)
  have ra := rs.trans sa
  have pos : 0<a*middleDelta a z r s := by
    rw [middleDelta_mul_left]
    exact add_pos (mul_pos (mul_pos (mul_pos hr hs) (sub_pos.mpr a1)) (sub_pos.mpr za))
      (mul_pos (mul_pos hz (sub_pos.mpr ra)) (sub_pos.mpr sa))
  exact lt_of_not_ge fun bad => pos.not_ge (mul_nonpos_of_nonneg_of_nonpos ha.le bad)

section Field
variable {F : Type*} [Field F] [CharZero F]

/-- An exact polynomial residual can replace the paid parts of a
moment before any sign analysis. Coefficients are not divided. -/
theorem scaled_moment_of_residual {S U V T q : F[X]} {d c e f l t : F}
    (p : C d*S-C c*U-C e*V=C f*T)
    (u : integral l t (U*q)=0) (v : integral l t (V*q)=0) :
    d*integral l t (S*q)=f*integral l t (T*q) := by
  have scale (a : F) (P : F[X]) : integral l t (C a*P)=a*integral l t P := by
    simpa only [smul_eq_C_mul,smul_eq_mul] using (integral l t).map_smul a P
  have regroup : C d*(S*q)-C c*(U*q)-C e*(V*q)=(C d*S-C c*U-C e*V)*q := by ring
  calc
    _ = integral l t (C d*(S*q)-C c*(U*q)-C e*(V*q)) := by
      simp only [map_sub,scale,u,v,mul_zero,sub_zero]
    _ = integral l t (C f*(T*q)) := by rw [regroup,p,mul_assoc]
    _ = _ := scale _ _

theorem middle_scaled_moment {a z r s l t : F} {q : F[X]}
    (u : integral l t ((X*(C a-X))*q)=0)
    (v : integral l t (((1-X)*(X-C z))*q)=0) :
    middleDelta a z r s*integral l t (X*q)=z*integral l t (((X-C r)*(X-C s))*q) :=
  scaled_moment_of_residual (middle_scaled_polynomial a z r s) u v

end Field
end
end RKCert.ReviewedNative.StrongCentered16
