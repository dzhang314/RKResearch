module

import RKCert.ReviewedNative.AbstractContextModel

/-! Typed clients of the abstract model on the reviewed literal rooted trees.
Neither a quotient construction nor a split stage representation is assumed. -/
open RKResearch RKResearch.ContextCompletion
open RKResearch.CanonicalUniqueness (TreeWord)
open scoped FiniteRootedTree

section

variable {K V : Type*} [Field K] [CommRing V] [Algebra K V]
variable (M : Model K V)

example (t : FiniteRootedTree) :
    M.column (.leaf ◂ t) = M.act (M.column t) :=
  M.column_unary t

example (t u : FiniteRootedTree) :
    M.column (t # u) = M.column t * M.column u :=
  M.column_rootedSum t u

example (t u : FiniteRootedTree) :
    M.context (.through (.multiply u .empty)) (M.column t) =
      M.column (u # (.leaf ◂ t)) :=
  M.context_insert (.through (.multiply u .empty)) t

example {p : ℕ} (paidOrder : M.HasOrder p) (C : TreeWord) (t : FiniteRootedTree)
    (paid : ((C.insert t).order : ℕ) ≤ p) :
    M.readout (M.column (C.insert t)) = ((C.insert t).factorial : K)⁻¹ :=
  Model.HasOrder.paid_cell paidOrder C t paid

example [Module.Finite K V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (contexts : ι → TreeWord) (trees : κ → FiniteRootedTree) :
    (show Matrix ι κ K from fun i j =>
      M.readout (M.column ((contexts i).insert (trees j)))).rank ≤ Module.finrank K V :=
  M.block_rank_le contexts trees

end

#check @RKResearch.ContextCompletion.Model
#check @RKResearch.ContextCompletion.Model.column_unary
#check @RKResearch.ContextCompletion.Model.column_rootedSum
#check @RKResearch.ContextCompletion.Model.context_insert
#check @RKResearch.ContextCompletion.Model.block
#check @RKResearch.ContextCompletion.Model.HasOrder
#check @RKResearch.ContextCompletion.Model.HasOrder.paid_cell
#check @RKResearch.ContextCompletion.Model.block_rank_le

#print axioms RKResearch.ContextCompletion.Model.column_unary
#print axioms RKResearch.ContextCompletion.Model.column_rootedSum
#print axioms RKResearch.ContextCompletion.Model.context_insert
#print axioms RKResearch.ContextCompletion.Model.HasOrder.paid_cell
#print axioms RKResearch.ContextCompletion.Model.block_rank_le
