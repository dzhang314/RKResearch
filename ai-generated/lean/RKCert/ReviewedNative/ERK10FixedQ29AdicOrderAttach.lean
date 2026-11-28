module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderAnn
public import RKCert.ReviewedNative.ERK10FixedQ29AdicAttachCore
public import RKCert.Tree

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

/-- The unnormalized scalar stage monomial, defined by the actual
constructor recursion. The primitive of a child divides by its order. -/
def treeScale : RKCert.Tree→R
  | .leaf => 1
  | .attach u v => (treeScale u*Ring.inverse (u.order:R))*treeScale v

def treeModel (t : RKCert.Tree) (x : R) : R := treeScale t*x^(t.order-1)
def treePrim (t : RKCert.Tree) (x : R) : R :=
  (treeScale t*Ring.inverse (t.order:R))*x^t.order

theorem treeModel_attach (u v : RKCert.Tree) (x : R) :
    treeModel (.attach u v) x=treePrim u x*treeModel v x := by
  have hv := v.order_pos
  have he : u.order+v.order-1=u.order+(v.order-1) := by omega
  simp only [treeModel,treePrim,treeScale,RKCert.Tree.order]
  rw [he,pow_add]
  ring

def rawTreeProfile (c a b : R) (t : RKCert.Tree) (i : Site) : R :=
  RKCert.stageWeight (tableau15 c a b (actualK c a b)) t (rawSlot i)

def retainedTreeProfile (c a b : R) (t : RKCert.Tree) (j : Old) : R :=
  RKCert.stageWeight (tableau15 c a b (actualK c a b)) t (oldSlot j)

def rawTreeNominal (c a b : R) (t : RKCert.Tree) (i : Site) : R :=
  treeModel t (rawClock c a b i)

def rawTreePrimitive (c a b : R) (t : RKCert.Tree) (i : Site) : R :=
  treePrim t (rawClock c a b i)

def rawTreeErr (c a b : R) (t : RKCert.Tree) : Site→R :=
  rawTreeProfile c a b t-rawTreeNominal c a b t

def rawTreeEdge (c a b : R) (t : RKCert.Tree) (i : Site) : R :=
  (∑ j : Fin 15,tableau15 c a b (actualK c a b) (rawSlot i) j*
    RKCert.stageWeight (tableau15 c a b (actualK c a b)) t j) -
      rawTreePrimitive c a b t i

theorem rawTreeEdge_block (c a b : R) (t : RKCert.Tree) (i : Site) :
    let q:=(actualHost c a b).retainedPoly (retainedTreeProfile c a b t)
    rawTreeEdge c a b t i =
      q.primitive (rawClock c a b i) -
      rawTransact (actualK c a b) (fun k=>q.eval (rawClock c a b k)) i +
      rawTransact (actualK c a b) (rawTreeProfile c a b t) i -
      rawTreePrimitive c a b t i := by
  unfold rawTreeEdge
  rw [tableau15_raw_action]
  rfl

theorem rawTreeErr_leaf (c a b : R) : rawTreeErr c a b .leaf=0 := by
  funext i
  simp [rawTreeErr,rawTreeNominal,rawTreeProfile,RKCert.stageWeight,
    treeModel,treeScale,RKCert.Tree.order]

/-- Actual binary attach expansion, including the product of the two
real defect vectors. No short-word or nominal-only hypothesis is used. -/
theorem rawTreeErr_attach (c a b : R) (u v : RKCert.Tree) :
    rawTreeErr c a b (.attach u v) =
      rawTreePrimitive c a b u*rawTreeErr c a b v+
      rawTreeNominal c a b v*rawTreeEdge c a b u+
      rawTreeEdge c a b u*rawTreeErr c a b v := by
  funext i
  simp only [rawTreeErr,rawTreeProfile,rawTreeNominal,rawTreePrimitive,rawTreeEdge,
    Pi.sub_apply,Pi.add_apply,Pi.mul_apply,RKCert.stageWeight,treeModel_attach]
  ring

theorem rawAnn_treeModel_mul (c a b : R) (t : RKCert.Tree) (j : ℕ)
    (v : Site→R) (h : rawAnn c a b (j+(t.order-1)) v) :
    rawAnn c a b j (rawTreeNominal c a b t*v) := by
  have H := rawAnn_scale c a b (treeScale t)
    (rawAnn_markPow c a b j (t.order-1) v h)
  have he : rawTreeNominal c a b t*v =
      fun i=>treeScale t*((rawClock c a b i)^(t.order-1)*v i) := by
    funext i
    simp only [Pi.mul_apply,rawTreeNominal,treeModel,mul_assoc]
  rw [he]
  exact H

theorem rawAnn_treePrim_mul (c a b : R) (t : RKCert.Tree) (j : ℕ)
    (v : Site→R) (h : rawAnn c a b (j+t.order) v) :
    rawAnn c a b j (rawTreePrimitive c a b t*v) := by
  have H := rawAnn_scale c a b (treeScale t*Ring.inverse (t.order:R))
    (rawAnn_markPow c a b j t.order v h)
  have he : rawTreePrimitive c a b t*v =
      fun i=>(treeScale t*Ring.inverse (t.order:R))*((rawClock c a b i)^t.order*v i) := by
    funext i
    simp only [Pi.mul_apply,rawTreePrimitive,treePrim,mul_assoc]
  rw [he]
  exact H

/-- These are the remaining linear/early physical fields only, not a
statement of order or abstract nonlinear closure. The actual recurrence,
mark shifts, and all three nonlinear cases are proved elsewhere. -/
structure OrderAttachReceipts (c a b : R) : Prop where
  err_low : ∀ t : RKCert.Tree, t.order ≤ 4 → rawTreeErr c a b t=0
  edge_low : ∀ t : RKCert.Tree, t.order ≤ 3 → rawTreeEdge c a b t=0
  err_five : ∀ t : RKCert.Tree, t.order=5 → rawLine c a b (rawTreeErr c a b t)
  edge_four : ∀ t : RKCert.Tree, t.order=4 → rawLine c a b (rawTreeEdge c a b t)
  edge_step : ∀ t : RKCert.Tree, 5 ≤ t.order → t.order ≤ 9 →
    rawAnn c a b (10-t.order) (rawTreeErr c a b t) →
    rawAnn c a b (9-t.order) (rawTreeEdge c a b t)

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

def actualTreeKit (h : OrderAttachReceipts c a b) :
    RKResearch.Certified.ERK10AttachCore.Kit RKCert.Tree (Site→R) where
  size := RKCert.Tree.order
  attach := fun t u v=>t=RKCert.Tree.attach u v
  positive := RKCert.Tree.order_pos
  decompose := by
    intro t ht
    cases t with
    | leaf => simp [RKCert.Tree.order] at ht
    | attach u v => exact ⟨u,v,rfl⟩
  attach_size := by intro t u v h;subst t;rfl
  zero := 0
  add := (·+·)
  mul := (·*·)
  zero_mul := zero_mul
  mul_zero := mul_zero
  err := rawTreeErr c a b
  edge := rawTreeEdge c a b
  nominal := rawTreeNominal c a b
  primitive := rawTreePrimitive c a b
  recurrence := by intro t u v h;subst t;exact rawTreeErr_attach c a b u v
  ann := rawAnn c a b
  line := rawLine c a b
  ann_zero := rawAnn_zero c a b
  ann_add := fun _ _ _ => rawAnn_add c a b
  nominal_shift := fun t j v _ => rawAnn_treeModel_mul c a b t j v
  primitive_shift := fun t j v _ => rawAnn_treePrim_mul c a b t j v
  err_low := h.err_low
  edge_low := h.edge_low
  err_five := h.err_five
  edge_four := h.edge_four
  line_ann := fun _ => actual_lineAnn5 ρ c a b hp hc ha hb hRoot hOther
  edge_step := h.edge_step
  line_product := fun _ _ => actual_line_product ρ c a b hp hc ha hb hRoot hOther
  line_ann_product := fun _ _ => actual_line_ann_product ρ c a b hp hc ha hb hRoot hOther
  ann_line_product := fun _ _ => actual_ann_line_product ρ c a b hp hc ha hb hRoot hOther

theorem actual_attach_grade (h : OrderAttachReceipts c a b) (t : RKCert.Tree)
    (lo : 5≤t.order) (hi : t.order≤10) :
    rawAnn c a b (10-t.order) (rawTreeErr c a b t) :=
  (actualTreeKit ρ c a b hp hc ha hb hRoot hOther h).grade t lo hi

theorem actual_error_output_zero (h : OrderAttachReceipts c a b)
    (t : RKCert.Tree) (ht : t.order≤10) :
    ∑ i : Site,rawW c a b i*rawTreeErr c a b t i=0 := by
  by_cases hv : t.order≤4
  · rw [h.err_low t hv]
    simp
  have HH := (actual_attach_grade ρ c a b hp hc ha hb hRoot hOther h t (by omega) ht).1
    0 (Nat.zero_le _)
  simpa only [rawMoment,pow_zero,mul_one] using HH

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.rawTreeEdge_block
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.rawTreeErr_attach
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_attach_grade
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_error_output_zero
