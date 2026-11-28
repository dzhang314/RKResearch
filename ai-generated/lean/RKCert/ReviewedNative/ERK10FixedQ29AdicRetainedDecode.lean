module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRetainedLow

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear
open scoped Ring BigOperators
noncomputable section
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

theorem actual_host_alpha_pay (p : HostInput R) (hs : IsUnit p.s) :
    p.α*p.s^3=p.q^2*(3*p.s-2*p.q) := by
  unfold HostInput.α
  rw [mul_assoc,mul_comm (Ring.inverse (p.s^3)) (p.s^3),
    Ring.mul_inverse_cancel _ (hs.pow 3),mul_one]

/-- Both exact old projected evaluations of the fixed-host polynomials. -/
theorem host_projected_geometry (p : HostInput R) (h3 : IsUnit (3:R))
    (hs : IsUnit p.s) (ht : IsUnit p.t) :
    p.eval2 p.q=p.α*p.eval2 p.s ∧ p.eval3 p.q=p.α*p.eval3 p.s := by
  have geo := p.geometry h3 ht
  have g0 : 3*p.s-2*p.r+p.t=0 := by linear_combination geo.1
  have g := geo.2.2
  have hA := actual_host_alpha_pay p hs
  have i3 := Ring.mul_inverse_cancel _ h3
  constructor
  · apply (h3.mul (hs.pow 3)).mul_left_cancel
    unfold HostInput.eval2
    linear_combination
      -2*p.q*p.s*(p.q-p.s)*g-(3*p.s^2-2*p.r*p.s)*hA-
        2*p.r*p.s^3*(p.q-p.α*p.s)*i3
  · apply (hs.pow 3).mul_left_cancel
    unfold HostInput.eval3
    linear_combination
      p.q*p.s*(p.q-p.s)*(2*p.q*p.r-2*p.q*p.s-p.r*p.s)*g0+
      p.q*p.s*(p.q-p.s)*(2*p.r-3*p.s)*g-
      (p.s*(p.s-p.r)*(p.s-p.t))*hA

/-- Uniqueness for the three actual retained decoder linear reads; no
field or nonzero-only cancellation is used. -/
theorem quad_eq_of_reads (p : HostInput R) (D : IsUnit p.decodeDen)
    (a b : Quad R) (h0 : a.eval 0=b.eval 0)
    (h1 : a.eval p.q-p.α*a.eval p.s=b.eval p.q-p.α*b.eval p.s)
    (h2 : a.eval p.r=b.eval p.r) : a=b := by
  let A := p.q-p.α*p.s
  let B := p.q^2-p.α*p.s^2
  have hv0 : a.c0=b.c0 := by simpa [Quad.eval] using h0
  have hv1 : A*(a.c1-b.c1)+B*(a.c2-b.c2)=0 := by
    unfold A B Quad.eval at *
    linear_combination h1-(1-p.α)*hv0
  have hv2 : p.r*(a.c1-b.c1)+p.r^2*(a.c2-b.c2)=0 := by
    unfold Quad.eval at h2
    linear_combination h2-hv0
  have hd1 : p.decodeDen*(a.c1-b.c1)=0 := by
    change (A*p.r^2-B*p.r)*(a.c1-b.c1)=0
    linear_combination p.r^2*hv1-B*hv2
  have hd2 : p.decodeDen*(a.c2-b.c2)=0 := by
    change (A*p.r^2-B*p.r)*(a.c2-b.c2)=0
    linear_combination A*hv2-p.r*hv1
  have hA : a.c1=b.c1 := sub_eq_zero.mp (D.mul_left_cancel (by rwa [mul_zero]))
  have hB : a.c2=b.c2 := sub_eq_zero.mp (D.mul_left_cancel (by rwa [mul_zero]))
  cases a
  cases b
  congr

def hostQuadratic (p : HostInput R) : Quad R :=
  let iF := Ring.inverse (p.eval2 p.r)
  ⟨0,(-2*p.r*Ring.inverse (3:R))*iF,iF⟩

theorem hostQuadratic_eval (p : HostInput R) (y : R) :
    (hostQuadratic p).eval y=p.eval2 y*Ring.inverse (p.eval2 p.r) := by
  unfold hostQuadratic Quad.eval HostInput.eval2
  ring

theorem hostQuadratic_prim (p : HostInput R) (y : R) (h2 : IsUnit (2:R)) :
    (hostQuadratic p).primitive y=p.int2 y*Ring.inverse (p.eval2 p.r) := by
  unfold hostQuadratic Quad.primitive HostInput.int2
  linear_combination
    -(p.r*Ring.inverse (3:R)*Ring.inverse (p.eval2 p.r)*y^2)*(Ring.mul_inverse_cancel _ h2)

def Quad.subScale (a b : Quad R) (k : R) : Quad R :=
  ⟨a.c0-k*b.c0,a.c1-k*b.c1,a.c2-k*b.c2⟩

theorem Quad.subScale_eval (a b : Quad R) (k y : R) :
    (a.subScale b k).eval y=a.eval y-k*b.eval y := by
  unfold Quad.subScale Quad.eval;ring

theorem Quad.subScale_prim (a b : Quad R) (k y : R) :
    (a.subScale b k).primitive y=a.primitive y-k*b.primitive y := by
  unfold Quad.subScale Quad.primitive;ring

def cubicPart (n : ℕ) (σ : R) : R := if n=3 then σ else 0

def modelRemainder (p : HostInput R) (σ : R) : ℕ→Quad R
  | 0 => ⟨σ,0,0⟩
  | 1 => ⟨0,σ,0⟩
  | 2 => ⟨0,0,σ⟩
  | _+3 => ⟨0,-σ*p.r*p.t,σ*(p.r+p.t)⟩

theorem modelRemainder_eval (p : HostInput R) (σ : R) (n : ℕ) (h : n≤3) (y : R) :
    (modelRemainder p σ n).eval y=σ*y^n-cubicPart n σ*p.eval3 y := by
  interval_cases n <;>
    simp [modelRemainder,Quad.eval,cubicPart,HostInput.eval3] <;> ring

theorem modelRemainder_prim (p : HostInput R) (σ : R) (n : ℕ) (h : n≤3) (y : R) :
    (modelRemainder p σ n).primitive y =
      (σ*Ring.inverse (((n+1:ℕ):R)))*y^(n+1)-cubicPart n σ*p.int3 y := by
  interval_cases n <;>
    norm_num [modelRemainder,Quad.primitive,cubicPart,HostInput.int3,Ring.inverse_one] <;> ring

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actual_retained_as_quad (t : RKCert.Tree) (ht : t.order≤4) :
    let p:=actualHost c a b
    p.retainedPoly (retainedTreeProfile c a b t) =
      (modelRemainder p (treeScale t) (t.order-1)).subScale
        (hostQuadratic p) (treeModel t p.r) := by
  let p:=actualHost c a b
  let v:=retainedTreeProfile c a b t
  let σ : R := treeScale t
  let n:=t.order-1
  let γ:=cubicPart n σ
  let C:=hostQuadratic p
  let M:=modelRemainder p σ n
  let Q:=M.subScale C (treeModel t p.r)
  have h2 := small_order_paid ρ 2 (by decide) (by decide)
  have h3 := small_order_paid ρ 3 (by decide) (by decide)
  have h8 := small_order_paid ρ 8 (by decide) (by decide)
  have he : IsUnit (Ring.inverse (8:R)) :=
    IsUnit.of_mul_eq_one 8 (by
      rw [mul_comm]
      exact Ring.mul_inverse_cancel _ (show IsUnit (8:R) from h8))
  have hs : IsUnit p.s := actual_host_guards ρ c a b hp hc ha hb 3
  have hT : IsUnit p.t := actual_host_guards ρ c a b hp hc ha hb 2
  have hF : IsUnit (p.eval2 p.r) := actual_host_guards ρ c a b hp hc ha hb 9
  have hD : IsUnit p.decodeDen := actual_host_guards ρ c a b hp hc ha hb 13
  have hn : n≤3 := by unfold n;omega
  obtain ⟨E2,E3⟩ := host_projected_geometry p h3 hs hT
  have hModel : ∀ y : R,Q.eval y=treeModel t y-γ*p.eval3 y-
      treeModel t p.r*(p.eval2 y*Ring.inverse (p.eval2 p.r)) := by
    intro y
    change (M.subScale C (treeModel t p.r)).eval y=_
    rw [Quad.subScale_eval,show M.eval y=_ from modelRemainder_eval p σ n hn y,
        show C.eval y=_ from hostQuadratic_eval p y]
    rfl
  obtain ⟨h0,h1,hr⟩ := p.retained_reads hD v
  change p.retainedPoly v=Q
  apply quad_eq_of_reads p hD
  · rw [h0,hModel]
    change retainedTreeProfile c a b t 0=_
    rw [retained_origin_model]
    simp [HostInput.eval3,HostInput.eval2]
  · rw [h1,hModel,hModel]
    change retainedProj p v=_
    rw [show retainedProj p v=_ from retained_projected_low c a b t ht he h2 h3 hs]
    linear_combination γ*E3+(treeModel t p.r*Ring.inverse (p.eval2 p.r))*E2
  · rw [hr,hModel,Ring.mul_inverse_cancel _ hF]
    simp [HostInput.eval3]

theorem actual_retained_eval_prim (t : RKCert.Tree) (ht : t.order≤4) (y : R) :
    let p:=actualHost c a b
    let q:=p.retainedPoly (retainedTreeProfile c a b t)
    let γ:=cubicPart (t.order-1) (treeScale t:R)
    let δ:=treeModel t p.r*Ring.inverse (p.eval2 p.r)
    q.eval y=treeModel t y-γ*p.eval3 y-δ*p.eval2 y ∧
    q.primitive y=treePrim t y-γ*p.int3 y-δ*p.int2 y := by
  let p:=actualHost c a b
  let q:=p.retainedPoly (retainedTreeProfile c a b t)
  let γ:=cubicPart (t.order-1) (treeScale t:R)
  let δ:=treeModel t p.r*Ring.inverse (p.eval2 p.r)
  change q.eval y=treeModel t y-γ*p.eval3 y-δ*p.eval2 y ∧
    q.primitive y=treePrim t y-γ*p.int3 y-δ*p.int2 y
  have hq : q=_ := actual_retained_as_quad ρ c a b hp hc ha hb t ht
  have h2 := small_order_paid ρ 2 (by decide) (by decide)
  have hpos := t.order_pos
  have hn : t.order-1≤3 := by omega
  constructor
  · rw [hq,Quad.subScale_eval,modelRemainder_eval _ _ _ hn,hostQuadratic_eval]
    unfold γ δ p treeModel
    ring
  · rw [hq,Quad.subScale_prim,modelRemainder_prim _ _ _ hn,hostQuadratic_prim _ _ h2]
    rw [show t.order-1+1=t.order from by omega]
    unfold γ δ p treePrim
    ring

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.host_projected_geometry
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.quad_eq_of_reads
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_retained_as_quad
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_retained_eval_prim
