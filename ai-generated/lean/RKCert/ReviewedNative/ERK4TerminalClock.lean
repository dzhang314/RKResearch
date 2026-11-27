module

public import RKResearch.ERK
public import RKResearch.OrderConditions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The last clock of a four-stage explicit order-four tableau is one.
The scalar algebra works with repeated clocks and zero divisors. -/

namespace RKResearch.Certified.ERK4TerminalClock
open RKResearch FiniteRootedTree
open scoped Matrix

theorem scalar {R : Type*} [CommRing R] (a b c s w f z : R)
    (ht : 6*(a*s+b*w)=1)
    (hq : 12*(a^2*s+b^2*w)=1)
    (hc : 8*(c*(a*s+b*w)+(b-c)*a*f*z)=1)
    (htall : 24*w*f*a=1)
    (hm : 12*z*b*(b-a)*(b-c)=3-4*(a+c)+6*a*c) :
    c=1 := by
  have h1 : 12*b*(b-a)*w=1-2*a := by linear_combination hq-2*a*ht
  have h2 : 24*(b-c)*a*f*z=3-4*c := by linear_combination 3*hc-4*c*ht
  have h3 : (12*b*(b-a)*w)*(24*(b-c)*a*f*z)=12*z*b*(b-a)*(b-c) := by
    calc
      _ = (24*w*f*a)*(12*z*b*(b-a)*(b-c)) := by ring
      _ = _ := by rw [htall,one_mul]
  rw [h1,h2,hm] at h3
  have hzero : (2*a)*(1-c)=0 := by linear_combination -h3
  have hu : IsUnit (2*a) := IsUnit.of_mul_eq_one (12*w*f) (by linear_combination htall)
  apply hu.mul_left_cancel
  linear_combination -hzero

/-- Literal four-stage reviewed order supplies every scalar premise. -/
theorem terminal_one {R : Type*} [CommRing R]
    {A : Matrix (Fin 4) (Fin 4) R} {w : Fin 4→R}
    (hA : ERK A) (ho : HasOrder 4 A w) :
    (A *ᵥ (1:Fin 4→R)) 3=1 := by
  let X := A *ᵥ (1:Fin 4→R)
  let a := X 1
  let b := X 2
  let c := X 3
  let s := w 2*A 2 1+w 3*A 3 1
  let t := w 3*A 3 2
  let f := A 2 1
  have ha (i j : Fin 4) (h : i≤j) : A i j=0 := hA h
  have rd0 (v : Fin 4→R) : (A *ᵥ v) 0=0 := by
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,ha 0 0 (by decide),
      ha 0 1 (by decide),ha 0 2 (by decide),ha 0 3 (by decide)]
  have rd1 (v : Fin 4→R) : (A *ᵥ v) 1=A 1 0*v 0 := by
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,ha 1 1 (by decide),
      ha 1 2 (by decide),ha 1 3 (by decide)]
  have rd2 (v : Fin 4→R) : (A *ᵥ v) 2=A 2 0*v 0+A 2 1*v 1 := by
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,ha 2 2 (by decide),ha 2 3 (by decide)]
  have rd3 (v : Fin 4→R) : (A *ᵥ v) 3=A 3 0*v 0+A 3 1*v 1+A 3 2*v 2 := by
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,ha 3 3 (by decide),add_assoc]
  have hX0 : X 0=0 := rd0 _
  have sumW (v : Fin 4→R) : (w ⬝ᵥ v)=w 0*v 0+w 1*v 1+w 2*v 2+w 3*v 3 := by
    simp [dotProduct,Fin.sum_univ_four,add_assoc]
  have hT : w ⬝ᵥ (A *ᵥ X)=a*s+b*t := by
    simp only [sumW,rd0,rd1,rd2,rd3,hX0]
    dsimp [a,b,s,t]
    ring
  have hQ : w ⬝ᵥ (A *ᵥ X^2)=a^2*s+b^2*t := by
    simp only [sumW,rd0,rd1,rd2,rd3,Pi.pow_apply,hX0,zero_pow (by decide : 2≠0)]
    dsimp [a,b,s,t]
    ring
  have hC : w ⬝ᵥ (X*(A *ᵥ X))=c*(a*s+b*t)+(b-c)*a*f*w 2 := by
    simp only [sumW,Pi.mul_apply,rd0,rd1,rd2,rd3,hX0]
    dsimp [a,b,c,s,t,f]
    ring
  have hTall : w ⬝ᵥ (A *ᵥ (A *ᵥ X))=t*f*a := by
    simp only [sumW,rd0,rd1,rd2,rd3,hX0]
    dsimp [a,t,f]
    ring
  let t2 := FiniteRootedTree.butcherProduct leaf leaf
  let t3 := FiniteRootedTree.butcherProduct leaf t2
  let t4 := FiniteRootedTree.butcherProduct leaf t3
  let tq := FiniteRootedTree.butcherProduct leaf (bushyTree 3)
  let tc := FiniteRootedTree.butcherProduct (bushyTree 2) t2
  have T := ho t3 (by decide)
  have Q := ho tq (by decide)
  have C := ho tc (by decide)
  have Tall := ho t4 (by decide)
  rw [show (t3.factorial:ℕ)=6 by decide +kernel,Nat.cast_ofNat] at T
  rw [show (tq.factorial:ℕ)=12 by decide +kernel,Nat.cast_ofNat] at Q
  rw [show (tc.factorial:ℕ)=8 by decide +kernel,Nat.cast_ofNat] at C
  rw [show (t4.factorial:ℕ)=24 by decide +kernel,Nat.cast_ofNat] at Tall
  simp only [t3,t2,Φ,one_mul] at T
  simp only [tq,Φ,Φ_bushyTree,one_mul] at Q
  simp only [tc,t2,Φ,Φ_bushyTree,one_mul] at C
  simp only [t4,t3,t2,Φ,one_mul] at Tall
  change (6:R)*(w ⬝ᵥ (A *ᵥ X))=1 at T
  change (12:R)*(w ⬝ᵥ (A *ᵥ X^2))=1 at Q
  rw [show ((2:ℕ+):ℕ)-1=1 from rfl,pow_one] at C
  change (8:R)*(w ⬝ᵥ (X*(A *ᵥ X)))=1 at C
  change (24:R)*(w ⬝ᵥ (A *ᵥ (A *ᵥ X)))=1 at Tall
  rw [hT] at T
  rw [hQ] at Q
  rw [hC] at C
  rw [hTall] at Tall
  have B1 := ho (bushyTree 2) (by decide)
  have B2 := ho (bushyTree 3) (by decide)
  have B3 := ho (bushyTree 4) (by decide)
  simp only [factorial_bushyTree,Φ_bushyTree] at B1 B2 B3
  change (2:R)*(w ⬝ᵥ X^1)=1 at B1
  change (3:R)*(w ⬝ᵥ X^2)=1 at B2
  change (4:R)*(w ⬝ᵥ X^3)=1 at B3
  simp only [sumW,Pi.pow_apply,pow_one,hX0,zero_pow (by decide : 2≠0),
    zero_pow (by decide : 3≠0)] at B1 B2 B3
  have mom : 12*w 2*b*(b-a)*(b-c)=3-4*(a+c)+6*a*c := by
    dsimp [a,b,c]
    linear_combination 3*B3-4*(X 1+X 3)*B2+6*X 1*X 3*B1
  exact scalar a b c s t f (w 2) T Q C (by linear_combination Tall) mom

end RKResearch.Certified.ERK4TerminalClock

#print axioms RKResearch.Certified.ERK4TerminalClock.scalar

#print axioms RKResearch.Certified.ERK4TerminalClock.terminal_one
