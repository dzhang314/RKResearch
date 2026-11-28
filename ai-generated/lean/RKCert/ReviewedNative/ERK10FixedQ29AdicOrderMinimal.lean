module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderOutput

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear
open scoped Ring BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem rawLine_zero (c a b : R) : rawLine c a b 0 :=
  ⟨0,by funext i;simp⟩

theorem rawTreeNominal_leaf (c a b : R) : rawTreeNominal c a b .leaf=1 := by
  funext i
  simp [rawTreeNominal,treeModel,treeScale,RKCert.Tree.order]

/-- These are the three genuinely remaining physical linear/early
interfaces. The first two are only consulted after the child's raw
profile has already been proved equal to its model. -/
structure MinimalEdgeReceipts (c a b : R) : Prop where
  low : ∀ t : RKCert.Tree, t.order ≤ 3 → rawTreeErr c a b t=0 →
    rawTreeEdge c a b t=0
  fourth : ∀ t : RKCert.Tree, t.order=4 → rawTreeErr c a b t=0 →
    rawLine c a b (rawTreeEdge c a b t)
  high : ∀ t : RKCert.Tree, 5 ≤ t.order → t.order ≤ 9 →
    rawAnn c a b (10-t.order) (rawTreeErr c a b t) →
    rawAnn c a b (9-t.order) (rawTreeEdge c a b t)

theorem MinimalEdgeReceipts.err_low {c a b : R} (H : MinimalEdgeReceipts c a b)
    (t : RKCert.Tree) (ht : t.order≤4) : rawTreeErr c a b t=0 := by
  induction t with
  | leaf => exact rawTreeErr_leaf c a b
  | attach u v ihU ihV =>
    change u.order+v.order≤4 at ht
    have hu := u.order_pos
    have hv := v.order_pos
    have E := H.low u (by omega) (ihU (by omega))
    rw [rawTreeErr_attach,E,ihV (by omega)]
    simp

theorem MinimalEdgeReceipts.base_low {c a b : R} (H : MinimalEdgeReceipts c a b)
    (t : RKCert.Tree) (ht : t.order≤3) : rawTreeEdge c a b t=0 :=
  H.low t ht (H.err_low t (by omega))

theorem MinimalEdgeReceipts.base_fourth {c a b : R} (H : MinimalEdgeReceipts c a b)
    (t : RKCert.Tree) (ht : t.order=4) : rawLine c a b (rawTreeEdge c a b t) :=
  H.fourth t ht (H.err_low t (by omega))

theorem MinimalEdgeReceipts.err_five {c a b : R} (H : MinimalEdgeReceipts c a b)
    (t : RKCert.Tree) (ht : t.order=5) : rawLine c a b (rawTreeErr c a b t) := by
  cases t with
  | leaf => simp [RKCert.Tree.order] at ht
  | attach u v =>
    change u.order+v.order=5 at ht
    have hu := u.order_pos
    have hv := v.order_pos
    by_cases hU : u.order≤3
    · rw [rawTreeErr_attach,H.base_low u hU,H.err_low v (by omega)]
      simpa using rawLine_zero c a b
    have h4 : u.order=4 := by omega
    have h1 : v.order=1 := by omega
    have hvLeaf : v=RKCert.Tree.leaf := by
      cases v with
      | leaf => rfl
      | attach l r =>
        have hl := l.order_pos
        have hr := r.order_pos
        change l.order+r.order=1 at h1
        omega
    subst v
    rw [rawTreeErr_attach,rawTreeErr_leaf,rawTreeNominal_leaf]
    simpa using H.base_fourth u h4

def MinimalEdgeReceipts.toAttach {c a b : R} (H : MinimalEdgeReceipts c a b) :
    OrderAttachReceipts c a b where
  err_low := H.err_low
  edge_low := H.base_low
  err_five := H.err_five
  edge_four := H.base_fourth
  edge_step := H.high

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actual_hasOrder10_of_three_edges (H : MinimalEdgeReceipts c a b) :
    RKResearch.HasOrder 10 (tableau15 c a b (actualK c a b)) (tableauWeights c a b) :=
  actual_hasOrder10_of_receipts ρ c a b hp hc ha hb hRoot hOther H.toAttach

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.MinimalEdgeReceipts.toAttach
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_hasOrder10_of_three_edges
