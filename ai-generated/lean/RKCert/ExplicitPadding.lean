module
public import RKCert.Tree
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
/-! # Zero-weight inactive suffix padding preserves every rooted-tree order -/
namespace RKCert.ExplicitPadding
variable {R:Type*} [CommSemiring R] {s m p:ℕ}

def matrix (A:Fin s→Fin s→R) (m:ℕ) : Fin (s+m)→Fin (s+m)→R :=
  Fin.addCases (fun i=>Fin.addCases (A i) (fun _=>0)) (fun _ _=>0)

def weights (b:Fin s→R) (m:ℕ) : Fin (s+m)→R :=
  Fin.addCases b (fun _=>0)

theorem strictLower {A:Fin s→Fin s→R} (ha:StrictLower A) :
    StrictLower (matrix A m) := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    intro j
    induction j using Fin.addCases with
    | left j =>
      intro le
      simpa only [matrix,Fin.addCases_left] using ha i j le
    | right j => intro _;simp only [matrix,Fin.addCases_left,Fin.addCases_right]
  | right i => intro j _;simp only [matrix,Fin.addCases_right]

theorem stageWeight_prefix (A:Fin s→Fin s→R) (t:Tree) (i:Fin s) :
    stageWeight (matrix A m) t (i.castAdd m)=stageWeight A t i := by
  induction t generalizing i with
  | leaf => rfl
  | attach c r ihc ihr =>
    simp only [stageWeight,Fin.sum_univ_add,matrix,Fin.addCases_left,Fin.addCases_right,
      ihc,ihr,zero_mul,Finset.sum_const_zero,add_zero]

theorem preserve_weight (A:Fin s→Fin s→R) (b:Fin s→R) (t:Tree) :
    weight (matrix A m) (weights b m) t=weight A b t := by
  simp only [weight,Fin.sum_univ_add,weights,Fin.addCases_left,Fin.addCases_right,
    stageWeight_prefix,zero_mul,Finset.sum_const_zero,add_zero]

theorem preserve_order {A:Fin s→Fin s→R} {b:Fin s→R} (ho:HasTreeOrderAtLeast A b p) :
    HasTreeOrderAtLeast (matrix A m) (weights b m) p := by
  intro t ht
  rw [preserve_weight]
  exact ho t ht

end RKCert.ExplicitPadding
