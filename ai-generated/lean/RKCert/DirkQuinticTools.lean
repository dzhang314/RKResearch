module
public import RKCert.RootTupleSpecialization
public import Mathlib.Tactic.Ring
@[expose] public section
namespace RKCert.DirkQuintic
open RKCert.FixedFactor
/-- Cleared normalized moments of the cubic nodal factor. The five rows
k=1,...,5 only use divisors of 2520. -/
def momentForm {R:Type*} [CommRing R] (k:ℕ) (a b c u:R) :R :=
  -(a*b*c)*(2520/(k+1):ℕ)+(a*b+a*c+b*c)*u*(2520/(k+2):ℕ)-
    (a+b+c)*u^2*(2520/(k+3):ℕ)+u^3*(2520/(k+4):ℕ)

def hankel {R:Type*} [CommRing R] (a b c d e:R) :R :=
  a*c*e-a*d^2-b^2*e+2*b*c*d-c^3

def obstruction {R:Type*} [CommRing R] (a b c u:R):R:=
  hankel (momentForm 1 a b c u) (momentForm 2 a b c u) (momentForm 3 a b c u)
    (momentForm 4 a b c u) (momentForm 5 a b c u)

noncomputable def test:MvPolynomial (Fin 4) ℤ :=
  obstruction (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)

theorem eval_test {R:Type*} [CommRing R] (v:Fin 4→R) : zEval test v=obstruction (v 0) (v 1) (v 2) (v 3) := by
  let f:=MvPolynomial.eval₂Hom (Int.castRingHom R) v
  have h (k:ℕ) (a b c u:MvPolynomial (Fin 4) ℤ) : f (momentForm k a b c u)=momentForm k (f a) (f b) (f c) (f u) := by
    simp only [momentForm,map_sub,map_add,map_mul,map_neg,map_pow,map_natCast]
  change f (obstruction _ _ _ _)=_
  simp only [obstruction,hankel,map_add,map_sub,map_mul,map_pow,map_ofNat,h]
  simp [f]

theorem obstruction_scale {R:Type*} [CommRing R] (t a b c u:R):
    obstruction (t*a) (t*b) (t*c) (t*u)=t^9*obstruction a b c u := by
  have norm (k:ℕ):momentForm k (t*a) (t*b) (t*c) (t*u)=t^3*momentForm k a b c u :=by
    unfold momentForm;ring
  simp only [obstruction,norm,hankel]
  ring

/-- A ring-valued comparison of a four-row tuple against the complete
symmetric signed moment determinant, excluding only genuine collisions. -/
def checkPair {p:ℕ} [Fact p.Prime] (L:List (ZMod p)) (a b:ZMod p):Bool :=
  L.all fun c=>L.all fun u=>decide (a=b ∨ a=c ∨ a=u ∨ b=c ∨ b=u ∨ c=u ∨ obstruction a b c u≠0)

theorem checked_eval {p:ℕ} [Fact p.Prime] (L:List (ZMod p))
    (checked:L.all (fun a=>L.all (fun b=>checkPair L a b))=true)
    (v:Fin 4→ZMod p) (mem:∀i,v i∈L) (inj:∀i j:Fin 4,i≠j → v i≠v j) :
    zEval test v≠0 := by
  rw [eval_test]
  have h:=List.all_eq_true.mp (List.all_eq_true.mp checked (v 0) (mem 0)) (v 1) (mem 1)
  unfold checkPair at h
  have e:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h (v 2) (mem 2)) (v 3) (mem 3))
  rcases e with e|e|e|e|e|e|e
  · exact (inj 0 1 (by decide) e).elim
  · exact (inj 0 2 (by decide) e).elim
  · exact (inj 0 3 (by decide) e).elim
  · exact (inj 1 2 (by decide) e).elim
  · exact (inj 1 3 (by decide) e).elim
  · exact (inj 2 3 (by decide) e).elim
  · exact e
end RKCert.DirkQuintic
