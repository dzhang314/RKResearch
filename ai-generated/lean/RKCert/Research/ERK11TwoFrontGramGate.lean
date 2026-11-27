import Lean

/-! Paid arithmetic for the complementary order-five first-provider
obstruction in the two-ended four-carrier branch. -/
namespace RKResearch.ERK11TwoFrontGramGate
open Lean.Grind
variable {K : Type} [Field K]

def G (x : K) : K := 6*x*x-15*x+10
def J (x : K) : K := 8*x*x-22*x+17

def H (x z : K) : K :=
  24*x*x*x-(30*z+45)*x*x+(60*z+20)*x-30*z

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

/-- Both paid actual grade-four aliases vanish at the same
ordinary order-five provider. Its clock is eliminated without
dividing by the clock-dependent coefficient. -/
theorem ordinaryProvider (x z : K) (n2 : (2:K) ≠ 0) (n5 : (5:K) ≠ 0)
    (a : G x=0) (h : H x z=0) : G z=0 ∧ x=z := by
  have f : 2*H x z-(8*x+5-10*z)*G x =
      5*((7-6*z)*x+8*z-10) := by unfold H G; grind
  have y : (5:K)*((7-6*z)*x+8*z-10)=0 := by
    rw [h,a] at f
    grind
  have l : (7-6*z)*x=10-8*z := by
    have w := (Field.of_mul_eq_zero y).resolve_left n5
    grind
  have n4 : (4:K) ≠ 0 := by
    have nn := nzMul n2 n2
    have e : (2:K)*2=4 := by grind
    rw [e] at nn
    exact nn
  have c : ((7-6*z)*(7-6*z))*G x =
      6*((7-6*z)*x)*((7-6*z)*x)-15*((7-6*z)*x)*(7-6*z)+10*(7-6*z)*(7-6*z) := by
    unfold G
    grind
  rw [a,Semiring.mul_zero,l] at c
  have d : (4:K)*G z=0 := by unfold G; grind
  have gz := (Field.of_mul_eq_zero d).resolve_left n4
  have live : 7-6*z ≠ 0 := by
    intro zz
    have ll : 10-8*z=0 := by grind
    exact n2 (by grind)
  have q : (7-6*z)*(x-z)=0 := by
    calc
      _ = (7-6*z)*x-(7-6*z)*z := by
        clear a h f y l n4 c d gz live n2 n5
        grind
      _ = (10-8*z)-(7-6*z)*z := by rw [l]
      _ = G z := by
        clear a h f y l n4 c d gz live n2 n5
        unfold G
        grind
      _ = 0 := gz
  exact ⟨gz,AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero q).resolve_left live)⟩

/-- Transferring the normalized sixth clock to the opposite
physical direction produces a coprime polynomial. -/
theorem complementary (z w : K) (n2 : (2:K) ≠ 0)
    (geometry : (4*(z-1))*w=4*z-3) (hw : G w=0) : J z=0 := by
  have h :
      (4*(z-1))*(4*(z-1))*G w =
      6*((4*(z-1))*w)*((4*(z-1))*w) -
      15*((4*(z-1))*w)*(4*(z-1)) + 10*(4*(z-1))*(4*(z-1)) := by
    unfold G
    grind
  rw [hw,Semiring.mul_zero,geometry] at h
  have e : (2:K)*J z=0 := by unfold J; grind
  exact (Field.of_mul_eq_zero e).resolve_left n2

/-- The two sixth-clock constraints are mutually incompatible in
the paid fields, not only in the reals. -/
theorem coprimeFronts (z : K) (n16 : (16:K) ≠ 0)
    (g : G z=0) (h : J z=0) : False := by
  have p : (22-24*z)*G z+(18*z-12)*J z=16 := by
    unfold G J
    grind
  rw [g,h,Semiring.mul_zero,Semiring.mul_zero,AddCommMonoid.zero_add] at p
  exact n16 p.symm

end RKResearch.ERK11TwoFrontGramGate
#print axioms RKResearch.ERK11TwoFrontGramGate.ordinaryProvider
#print axioms RKResearch.ERK11TwoFrontGramGate.complementary
#print axioms RKResearch.ERK11TwoFrontGramGate.coprimeFronts
