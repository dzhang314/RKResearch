module
public import RKCert.SDIRK6Normal
@[expose] public section
namespace RKCert.Paired.SDIRK.P6
open RKCert.Paired RKCert.Paired.SDIRK

variable {K : Type*} [Field K] [CharZero K]

theorem zero_algebra {z u w r : K} (v:K) (h : Third z u w r) (hu:u≠0)
    (hr:r=0) (hw:w≠0) (hwu:w≠u) : zeroCubic z u v=0 := by
  subst r
  have hc:=h.clock
  have hp : w*(w-u)*(2-w-u)=0 := by unfold kap at hc;linear_combination hc
  have hw' : w=2-u := by
    have hh := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero hw (sub_ne_zero.mpr hwu))
    linear_combination -hh
  subst w
  have hu1 : u-1≠0 := by intro hz;apply hwu;linear_combination -2*hz
  have hu2 : u-2≠0 := by intro hz;apply hw;linear_combination -hz
  have H:=h.leg3
  have hprod : ((-2:K)*u*(u-2)*(u-1))*zeroCubic z u v=0 := by
    unfold leg kap at H;unfold zeroCubic;linear_combination H
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hu) hu2) hu1)

theorem nonzero_algebra {z u w r : K} (v:K) (h : Third z u w r) (hu:u≠0) (hr:r≠0) :
    w=2*u ∧ Op.D u*r=2*u*(3*u-2) ∧ front z u v=0 := by
  have hw : w=2*u := by
    have hh := (mul_eq_zero.mp h.comm).resolve_left (mul_ne_zero hr hu)
    linear_combination -hh
  subst w
  have hc:=h.clock
  have hb : u*(Op.D u*r-2*u*(3*u-2))=0 := by unfold Op.D;unfold kap at hc;linear_combination hc
  have hd := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hu)
  have hh:=h.leg3
  have ht : (-2*u^3)*front z u v=0 := by
    unfold leg kap at hh
    unfold front
    unfold Op.D at hd
    linear_combination (norm := ring_nf)
      (-2+u+4*u^2-u^3)*hh -
        (-2*u^2*(20-30*z+12*z^2-z^3)-
        ((20*(1+u)^3-30*z*(1+u)^2+12*z^2*(1+u)-z^3)-
         (1+2*u-u^2)*(20-30*z+12*z^2-z^3))*((1+2*u-u^2)-1))*hd
  exact ⟨rfl,hd,(mul_eq_zero.mp ht).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hu))⟩

def dz (z u t:K) : K := u*kap u*leg z 1+(leg z (1+u)-kap u*leg z 1)*(t-1)

omit [CharZero K] in
theorem terminal_algebra {z v:K} {B:Fin 6→Fin 6→K} (hf : Front B z)
    (h4:nodes B 4=z-1-v) (h5:nodes B 5=z-1) (hg:seed B 4=kap v*seed B 5) :
    kappa z (B 1 0) v=0 ∨ terminal z (B 1 0) v=0 := by
  let u:= B 1 0
  by_cases hk: kap u=0
  · left;change -(u^2)+2*u+1=0;unfold kap at hk;linear_combination hk
  right
  have hs (i) : u*kap u*leg z (nodes B i)=dz z u (nodes B i)*seed B i := by
    have h₁:=hf.clock i;have h₂:=hf.profile i
    change (nodes B i-1)*seed B i=kap u*(tapMap B 1 (seed B) i) at h₁
    change u*leg z (nodes B i)=u*leg z 1*seed B i+
      (leg z (1+u)-kap u*leg z 1)*tapMap B 1 (seed B) i at h₂
    unfold dz;linear_combination kap u*h₂-(leg z (1+u)-kap u*leg z 1)*h₁
  have e4:=hs 4;have e5:=hs 5
  rw [h4,hg] at e4;rw [h5] at e5
  have O : terminal z u v=leg z (z-1-v)*dz z u (z-1)-kap v*leg z (z-1)*dz z u (z-1-v) := by
    simp only [terminal,dz,leg,kap];ring
  have hh : u*kap u*terminal z u v=0 := by
    rw [O]
    linear_combination dz z u (z-1)*e4-kap v*dz z u (z-1-v)*e5
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hf.tap_ne hk)
end RKCert.Paired.SDIRK.P6

