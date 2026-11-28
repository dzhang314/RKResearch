module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRetainedDecode

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped Ring BigOperators
noncomputable section
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

/-- The two global forward host residuals; their restriction to the first
three raw physical rows is already supplied by the actual ports. -/
structure ForwardHostLaws (c a b : R) : Prop where
  quadratic : ∀ i : Site, let p:=actualHost c a b
    rawTransact (actualK c a b) (fun j=>p.eval2 (rawClock c a b j)) i=
      p.int2 (rawClock c a b i)
  cubic : ∀ i : Site, let p:=actualHost c a b
    rawTransact (actualK c a b) (fun j=>p.eval3 (rawClock c a b j)) i-
      p.int3 (rawClock c a b i) = -p.int3 p.r*rawEta c a b i

theorem rawTransact_affine_gap (K : Site→Site→R) (x y z : Site→R)
    (a b : R) (i : Site) :
    rawTransact K (fun j=>x j-a*y j-b*z j) i =
      rawTransact K x i-a*rawTransact K y i-b*rawTransact K z i := by
  unfold rawTransact
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

/-- Exact physical low-edge evaluation after the projected old decoder
and the two global host laws. The sign is the true raw matrix sign. -/
theorem actual_first_edges_formula (H : ForwardHostLaws c a b)
    (t : RKCert.Tree) (ht : t.order≤4) (he : rawTreeErr c a b t=0) :
    rawTreeEdge c a b t=
      fun i=>-(cubicPart (t.order-1) (treeScale t:R))*
        (actualHost c a b).int3 (actualHost c a b).r*rawEta c a b i := by
  let p:=actualHost c a b
  let q:=p.retainedPoly (retainedTreeProfile c a b t)
  let γ:=cubicPart (t.order-1) (treeScale t:R)
  let δ:=treeModel t p.r*Ring.inverse (p.eval2 p.r)
  let x := rawClock c a b
  let K:=actualK c a b
  have hV : rawTreeProfile c a b t=fun j=>treeModel t (x j) := sub_eq_zero.mp he
  have evalEq (y : R) : q.eval y=treeModel t y-γ*p.eval3 y-δ*p.eval2 y :=
    (actual_retained_eval_prim ρ c a b hp hc ha hb t ht y).1
  have primEq (y : R) : q.primitive y=treePrim t y-γ*p.int3 y-δ*p.int2 y :=
    (actual_retained_eval_prim ρ c a b hp hc ha hb t ht y).2
  funext i
  have hE := rawTreeEdge_block c a b t i
  change rawTreeEdge c a b t i=q.primitive (x i)-
    rawTransact K (fun j=>q.eval (x j)) i+
    rawTransact K (rawTreeProfile c a b t) i-rawTreePrimitive c a b t i at hE
  rw [hE,primEq,hV]
  simp only [rawTreePrimitive]
  have hRead :
      rawTransact K (fun j=>q.eval (x j)) i =
        rawTransact K (fun j=>treeModel t (x j)) i -
        γ*rawTransact K (fun j=>p.eval3 (x j)) i -
        δ*rawTransact K (fun j=>p.eval2 (x j)) i := by
    simp only [evalEq]
    exact rawTransact_affine_gap K _ _ _ γ δ i
  rw [hRead]
  change _ = -γ*p.int3 p.r*rawEta c a b i
  have U : rawTransact K (fun j=>p.eval2 (x j)) i=p.int2 (x i) := H.quadratic i
  have V : rawTransact K (fun j=>p.eval3 (x j)) i-p.int3 (x i)=
      -p.int3 p.r*rawEta c a b i := H.cubic i
  change treePrim t (x i)-γ*p.int3 (x i)-δ*p.int2 (x i)-
    (rawTransact K (fun j=>treeModel t (x j)) i-
      γ*rawTransact K (fun j=>p.eval3 (x j)) i-δ*rawTransact K (fun j=>p.eval2 (x j)) i)+
      rawTransact K (fun j=>treeModel t (x j)) i-treePrim t (x i)=_
  linear_combination γ*V+δ*U

theorem actual_low_edge_of_host_laws (H : ForwardHostLaws c a b)
    (t : RKCert.Tree) (ht : t.order≤3) (he : rawTreeErr c a b t=0) :
    rawTreeEdge c a b t=0 := by
  rw [actual_first_edges_formula ρ c a b hp hc ha hb H t (by omega) he]
  have h0 : t.order-1≠3 := by omega
  funext i
  simp [cubicPart,h0]

theorem actual_fourth_edge_of_host_laws (H : ForwardHostLaws c a b)
    (t : RKCert.Tree) (ht : t.order=4) (he : rawTreeErr c a b t=0) :
    rawLine c a b (rawTreeEdge c a b t) := by
  refine ⟨-(cubicPart (t.order-1) (treeScale t:R))*
     (actualHost c a b).int3 (actualHost c a b).r,?_⟩
  exact actual_first_edges_formula ρ c a b hp hc ha hb H t (by omega) he

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_first_edges_formula
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_low_edge_of_host_laws
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_fourth_edge_of_host_laws
