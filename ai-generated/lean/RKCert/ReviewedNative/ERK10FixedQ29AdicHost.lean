module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPairInputs

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

structure HostInput (R : Type*) where
  r : R
  v : R
  z : R
  ηv : R
  ηz : R
deriving DecidableEq

namespace HostInput
variable {R S: Type*} [CommRing R] [CommRing S]

def pole (p : HostInput R) : R := (p.v^2*(3*p.r-2*p.v)-p.ηv*p.r^3)*(6:R)⁻¹ʳ
def numerator (p : HostInput R) : R := (-p.v^3*(3*p.v-4*p.r)-p.ηv*p.r^4)*(12:R)⁻¹ʳ
def t (p : HostInput R) : R := p.numerator*p.pole⁻¹ʳ
def s (p : HostInput R) : R := (2*p.r-p.t)*(3:R)⁻¹ʳ
def q (p : HostInput R) : R := p.r*p.s*p.t⁻¹ʳ
def α (p : HostInput R) : R := p.q^2*(3*p.s-2*p.q)*(p.s^3)⁻¹ʳ

def eval2 (p : HostInput R) (x : R) : R := x*(x-2*p.r*(3:R)⁻¹ʳ)
def int2 (p : HostInput R) (x : R) : R := (x^3-p.r*x^2)*(3:R)⁻¹ʳ
def eval3 (p : HostInput R) (x : R) : R := x*(x-p.r)*(x-p.t)
def int3 (p : HostInput R) (x : R) : R :=
  x^4*(4:R)⁻¹ʳ-(p.r+p.t)*x^3*(3:R)⁻¹ʳ+p.r*p.t*x^2*(2:R)⁻¹ʳ

def va (p : HostInput R) : R := p.int2 p.v*(p.eval2 p.r)⁻¹ʳ
def zb (p : HostInput R) : R := (p.int3 p.z-p.int3 p.r*p.ηz)*(p.eval3 p.v)⁻¹ʳ
def za (p : HostInput R) : R := (p.int2 p.z-p.zb*p.eval2 p.v)*(p.eval2 p.r)⁻¹ʳ

def momentDen (p : HostInput R) : R := p.s*p.q*(p.q-p.s)
def decodeDen (p : HostInput R) : R :=
  (p.q-p.α*p.s)*p.r^2 - (p.q^2-p.α*p.s^2)*p.r

def denominators (p : HostInput R) : Fin 14→R :=
  ![p.r,p.pole,p.t,p.s,p.q,p.q-p.s,p.r-p.s,p.r-p.q,p.eval3 p.s,p.eval2 p.r,
    p.eval3 p.v,p.int3 p.r,p.momentDen,p.decodeDen]

def taps (p : HostInput R) : Fin 3→R := ![p.va,p.za,p.zb]

def map (p : HostInput R) (ρ : R→+*S) : HostInput S :=
  ⟨ρ p.r,ρ p.v,ρ p.z,ρ p.ηv,ρ p.ηz⟩

theorem map_denominators (p : HostInput R) (ρ : R→+*S) [IsLocalHom ρ] :
    ρ ∘ p.denominators=(p.map ρ).denominators := by
  funext i
  fin_cases i <;> simp [denominators, map, pole, t, numerator, s, q, α, eval2, eval3, int3,
    momentDen, decodeDen, map_ringInverse, map_ofNat]

theorem map_taps (p : HostInput R) (ρ : R→+*S) [IsLocalHom ρ] :
    ρ ∘ p.taps=(p.map ρ).taps := by
  funext i
  fin_cases i <;> simp [taps,map,va,za,zb,pole,t,numerator,eval2,int2,eval3,int3,
    map_ringInverse,map_ofNat]

theorem int2_r (p : HostInput R) : p.int2 p.r=0 := by
  unfold int2; ring

theorem eval3_r (p : HostInput R) : p.eval3 p.r=0 := by
  unfold eval3; ring

theorem geometry (p : HostInput R) (h3 : IsUnit (3:R)) (ht : IsUnit p.t) :
    3*p.s=2*p.r-p.t ∧ p.t*p.q=p.r*p.s ∧ 2*p.q*p.r-3*p.q*p.s-p.r*p.s=0 := by
  have hs : 3*p.s=2*p.r-p.t := by
    unfold s; rw [mul_left_comm,Ring.mul_inverse_cancel _ h3,mul_one]
  have hq : p.t*p.q=p.r*p.s := by
    unfold q; rw [mul_left_comm,Ring.mul_inverse_cancel _ ht,mul_one]
  exact ⟨hs,hq,by linear_combination -p.q*hs+hq⟩

/-- The forward model contacts of the first three raw rows, with the
true nonlinear dirt parameter and all divisions paid. -/
theorem contact (p : HostInput R)
    (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (h4 : IsUnit (4:R))
    (h6 : IsUnit (6:R)) (h12 : IsUnit (12:R))
    (hD : IsUnit p.pole) (hF : IsUnit (p.eval2 p.r)) (hP : IsUnit (p.eval3 p.v)) :
    p.va*p.eval2 p.r=p.int2 p.v ∧
    p.int3 p.v=p.ηv*p.int3 p.r ∧
    p.za*p.eval2 p.r+p.zb*p.eval2 p.v=p.int2 p.z ∧
    p.zb*p.eval3 p.v=p.int3 p.z-p.int3 p.r*p.ηz := by
  have inv2 : (12:R)*(2:R)⁻¹ʳ=6 := by
    calc
      _ = 6*(2*(2:R)⁻¹ʳ) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h2,mul_one]
  have inv3 : (12:R)*(3:R)⁻¹ʳ=4 := by
    calc
      _ = 4*(3*(3:R)⁻¹ʳ) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h3,mul_one]
  have inv4 : (12:R)*(4:R)⁻¹ʳ=3 := by
    calc
      _ = 3*(4*(4:R)⁻¹ʳ) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h4,mul_one]
  have inv6 : (12:R)*(6:R)⁻¹ʳ=2 := by
    calc
      _ = 2*(6*(6:R)⁻¹ʳ) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h6,mul_one]
  have inv12 : (12:R)*(12:R)⁻¹ʳ=1 := Ring.mul_inverse_cancel _ h12
  have ht : p.pole*p.t=p.numerator := by
    unfold t; rw [mul_left_comm,Ring.mul_inverse_cancel _ hD,mul_one]
  refine ⟨?_,?_,?_,?_⟩
  · unfold va; rw [mul_assoc,mul_comm ((p.eval2 p.r)⁻¹ʳ),Ring.mul_inverse_cancel _ hF,mul_one]
  · apply h12.mul_left_cancel
    apply sub_eq_zero.mp
    calc
      _ = (12:R)*(p.pole*p.t-p.numerator) := by
        unfold int3 pole numerator
        linear_combination
          (p.v^4-p.ηv*p.r^4)*inv4 +
          (-(p.r+p.t)*p.v^3+p.ηv*(p.r+p.t)*p.r^3)*inv3 +
          (p.r*p.t*p.v^2-p.ηv*p.r*p.t*p.r^2)*inv2 -
          ((p.v^2*(3*p.r-2*p.v)-p.ηv*p.r^3)*p.t)*inv6 +
          (-p.v^3*(3*p.v-4*p.r)-p.ηv*p.r^4)*inv12
      _ = _ := by rw [ht,sub_self,mul_zero]
  · have H : p.za*p.eval2 p.r=p.int2 p.z-p.zb*p.eval2 p.v := by
      unfold za; rw [mul_assoc,mul_comm ((p.eval2 p.r)⁻¹ʳ),Ring.mul_inverse_cancel _ hF,mul_one]
    rw [H,sub_add_cancel]
  · unfold zb; rw [mul_assoc,mul_comm ((p.eval3 p.v)⁻¹ʳ),Ring.mul_inverse_cancel _ hP,mul_one]

end HostInput

variable {R : Type*} [CommRing R]
def actualHost (c a b : R) : HostInput R :=
  let x:=nodal c a b
  ⟨1-x host,1-x nodeH,1-x nodeG,etaNoncenter (closureU c) x nodeH,
    etaNoncenter (closureU c) x nodeG⟩

def hostMod : HostInput F := ⟨15,8,24,21,8⟩
def hostDenMod : Fin 14→F := ![15,5,16,24,8,13,20,7,17,17,13,18,2,27]
def hostTapMod : Fin 3→F := ![6,3,13]

theorem host_field_den : ∀ i, hostMod.denominators i=hostDenMod i := by
  simp only [hostMod,hostDenMod,HostInput.denominators,HostInput.pole,HostInput.t,
    HostInput.numerator,HostInput.s,HostInput.q,HostInput.α,HostInput.eval2,HostInput.eval3,
    HostInput.int3,HostInput.momentDen,HostInput.decodeDen,Ring.inverse_eq_inv]
  decide +kernel

theorem host_field_tap : ∀ i, hostMod.taps i=hostTapMod i := by
  simp only [hostMod,hostTapMod,HostInput.taps,HostInput.va,HostInput.za,HostInput.zb,
    HostInput.pole,HostInput.t,HostInput.numerator,HostInput.eval2,
    HostInput.int2,HostInput.eval3,HostInput.int3,Ring.inverse_eq_inv]
  decide +kernel

theorem host_den_nonzero : ∀ i, hostDenMod i≠0 := by decide +kernel

section Actual
variable (ρ : R →+* F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actual_host_mod : (actualHost c a b).map ρ=hostMod := by
  have h := nodes_reduce ρ c a b hc ha hb
  have hH : ρ (nodal c a b nodeH)=nodeResidues nodeH := congrFun h nodeH
  have hR : ρ (nodal c a b host)=nodeResidues host := congrFun h host
  have hG : ρ (nodal c a b nodeG)=nodeResidues nodeG := congrFun h nodeG
  have hmH : nodeH∈withoutCenter := by decide +kernel
  have hmG : nodeG∈withoutCenter := by decide +kernel
  simp only [actualHost,HostInput.map,map_sub,map_one,hH,hR,hG,
    actual_eta_residue ρ c a b hp hc ha hb hmH,actual_eta_residue ρ c a b hp hc ha hb hmG]
  decide +kernel

theorem actual_host_guards (i : Fin 14) : IsUnit ((actualHost c a b).denominators i) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  have H := congrFun ((actualHost c a b).map_denominators ρ) i
  change ρ ((actualHost c a b).denominators i)=_ at H
  rw [H,actual_host_mod ρ c a b hp hc ha hb,host_field_den]
  exact host_den_nonzero i

theorem actual_host_taps (i : Fin 3) : ρ ((actualHost c a b).taps i)=hostTapMod i := by
  have H := congrFun ((actualHost c a b).map_taps ρ) i
  change ρ ((actualHost c a b).taps i)=_ at H
  rw [H,actual_host_mod ρ c a b hp hc ha hb,host_field_tap]

theorem actual_host_contact :
    let p:=actualHost c a b
    p.va*p.eval2 p.r=p.int2 p.v ∧
    p.int3 p.v=p.ηv*p.int3 p.r ∧
    p.za*p.eval2 p.r+p.zb*p.eval2 p.v=p.int2 p.z ∧
    p.zb*p.eval3 p.v=p.int3 p.z-p.int3 p.r*p.ηz := by
  have h2 : IsUnit (2:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h3 : IsUnit (3:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h4 : IsUnit (4:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h6 : IsUnit (6:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h12 : IsUnit (12:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  apply HostInput.contact _ h2 h3 h4 h6 h12
  · exact actual_host_guards ρ c a b hp hc ha hb 1
  · exact actual_host_guards ρ c a b hp hc ha hb 9
  · exact actual_host_guards ρ c a b hp hc ha hb 10

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_host_mod
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_host_guards
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_host_taps
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_host_contact
