import Lean

/-! Structural closure of the weighted orthogonal flag used by the
ERK11 reversal. These are general Lean-core lemmas with abstract pairings. -/
namespace RKResearch.ERK11ReversalGate
open Lean.Grind
variable {K V : Type} [Field K]

def dualFlag (E : Nat → V → Prop) (terminal : V → K)
    (pair : V → V → K) (j : Nat) (v : V) : Prop :=
  terminal v=0 ∧ ∀ w, E (10-j) w → pair v w=0

/-- Unary closure of a last-coordinate-zero dual flag. -/
theorem adjointAdvance (E : Nat → V → Prop) (terminal : V → K)
    (pair : V → V → K) (A adj : V → V)
    (advanced : ∀ k w, E k w → E (k+1) (A w))
    (duality : ∀ x y, pair (adj x) y=pair x (A y))
    (last : ∀ x, terminal (adj x)=0)
    (j : Nat) (budget : j<10) (x : V) (hx : dualFlag E terminal pair j x) :
    dualFlag E terminal pair (j+1) (adj x) := by
  refine ⟨last x,?_⟩
  intro w hw
  rw [duality]
  apply hx.2
  have h := advanced (10-(j+1)) w hw
  have index : 10-(j+1)+1=10-j := by omega
  exact index ▸ h

/-- The product closure needed for a reverse defect when the other
factor is an actual forward rooted vector of the stated grade. -/
theorem mixedProduct (E : Nat → V → Prop) (terminal : V → K)
    (pair : V → V → K) (mul : V → V → V)
    (root : ∀ i k f w, E i f → E k w → E (i+k) (mul f w))
    (assoc : ∀ f x w, pair (mul f x) w=pair x (mul f w))
    (last : ∀ f x, terminal x=0 → terminal (mul f x)=0)
    (i j : Nat) (budget : i+j≤10) (f x : V)
    (hf : E i f) (hx : dualFlag E terminal pair j x) :
    dualFlag E terminal pair (i+j) (mul f x) := by
  refine ⟨last f x hx.1,?_⟩
  intro w hw
  rw [assoc]
  apply hx.2
  have h := root i (10-(i+j)) f w hf hw
  have index : i+(10-(i+j))=10-j := by omega
  exact index ▸ h

/-- The additional line over the pure midpoint is nondegenerate;
an isotropic vector has zero component in that line. -/
theorem spareIsotropic (a q : K) (nq : q ≠ 0) (iso : a*a*q=0) : a=0 := by
  have w := (Field.of_mul_eq_zero iso).resolve_right nq
  exact (Field.of_mul_eq_zero w).elim id id

/-- At the fourth raw row the first two paid primitive moments
forbid a second carrier of the first carrier's defect value. -/
theorem fourthCarrier (N a B : K) (nN : N ≠ 0)
    (h1 : a+N*B=0) (h2 : 3*(a+N*N*B)=(3-2*N)*a) :
    a=0 ∧ B=0 := by
  have r : N*a=0 := by
    have h := congrArg (fun x => 3*N*x) h1
    grind
  have az := (Field.of_mul_eq_zero r).resolve_left nN
  have s : N*B=0 := by grind
  exact ⟨az,(Field.of_mul_eq_zero s).resolve_left nN⟩

/-- Exact payment for the polynomial integration-by-parts read in
the finite order-eleven horizon. -/
private def fact : Nat → Nat
  | 0 => 1
  | k+1 => (k+1) * fact k

private def beta (i k : Nat) : Rat :=
  ((fact i : Nat) : Rat) * ((fact k : Nat) : Rat) /
    ((fact (i+k+1) : Nat) : Rat)

theorem primitiveMoments :
    ((List.range 11).all fun i =>
      (List.range (10-i)).all fun k =>
        beta (i+1) k / (((i+1) : Nat) : Rat) =
          beta i (k+1) / (((k+1) : Nat) : Rat)) = true := by
  decide +kernel

end RKResearch.ERK11ReversalGate
#print axioms RKResearch.ERK11ReversalGate.adjointAdvance
#print axioms RKResearch.ERK11ReversalGate.mixedProduct
#print axioms RKResearch.ERK11ReversalGate.spareIsotropic
#print axioms RKResearch.ERK11ReversalGate.fourthCarrier
#print axioms RKResearch.ERK11ReversalGate.primitiveMoments
