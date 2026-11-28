module

public import RKCert.ReviewedNative.DIRK12MidpointReverseSeed
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact normalized geometry equations and the three-root cofactor
comparison used for the barycentric reverse amplitudes. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Shape

variable {K : Type*} [Field K] [CharZero K]

def qa (a b c : K) : K := 9*b^2-4*a*c
def qb (a b c : K) : K := 3*b^2-a*c
def qc (a b c : K) : K := 3*b^2-2*a*c
def D (r : K) : K := r^2-4*r+1
def Q (r : K) : K := r^2-r+1

theorem geometry (a b c d r u : K)
    (a0 : a≠0) (d0 : d≠0) (r0 : r≠0) (qa0 : qa a b c≠0)
    (hs : d*(1+r)*qa a b c=6*(b*c))
    (hp : d^2*r*qa a b c*qb a b c=3*(b*c)^2)
    (hu : u*qc a b c=b*c) :
    u*D r= -d*r*(1+r) ∧
      3*(r-1)^2*b=2*r*(1+r)*d*a ∧
      (r-1)^2*Q r*c=r^2*(1+r)^2*d^2*a := by
  have hs2 := congrArg (fun z : K => z^2) hs
  have zz : d^2*(qa a b c*(qa a b c*(1+r)^2-12*r*qb a b c))=0 := by
    linear_combination hs2-12*hp
  have hshape : qa a b c*(1+r)^2=12*r*qb a b c :=
    sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp zz).resolve_left (pow_ne_zero _ d0))).resolve_left qa0)
  have hC : 6*r*qc a b c= -(qa a b c)*D r := by
    have q : qc a b c=qa a b c-2*qb a b c := by unfold qa qb qc; ring
    rw [q,D]
    linear_combination hshape
  have hA : qa a b c*Q r=9*r*b^2 := by
    simp only [Q,qa,qb] at hshape ⊢
    linear_combination hshape
  have hL : 4*r*(a*c)=qa a b c*(r-1)^2 := by
    simp only [Q,qa] at hA ⊢
    linear_combination -hA
  have hq : 4*Q r*a*c=9*(r-1)^2*b^2 := by
    have z : r*(4*Q r*a*c-9*(r-1)^2*b^2)=0 := by
      linear_combination Q r*hL+(r-1)^2*hA
    exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left r0)
  have hs1 : 3*(r-1)^2*b=2*r*(1+r)*d*a := by
    have z : qa a b c*(3*(r-1)^2*b-2*r*(1+r)*d*a)=0 := by
      linear_combination -3*b*hL-2*r*a*hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left qa0)
  refine ⟨?_,hs1,?_⟩
  · have zz : qa a b c*(u*D r+ d*r*(1+r))=0 := by
      linear_combination u*hC-6*r*hu+r*hs
    linear_combination (mul_eq_zero.mp zz).resolve_left qa0
  · have hs1sq := congrArg (fun z : K => z^2) hs1
    have z : (4*a)*((r-1)^2*Q r*c-r^2*(1+r)^2*d^2*a)=0 := by
      linear_combination (r-1)^2*hq+hs1sq
    exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (mul_ne_zero (by norm_num) a0))

def tu (r : K) : K := -r*(r+1)/D r
def nOne (r : K) : K := 2*r*(1+r)/(3*(r-1)^2)
def nTwo (r : K) : K := r^2*(1+r)^2/((r-1)^2*Q r)

def normD (r t n1 n2 : K) : K := n2-(r+t)*n1+r*t
def normV (_r t n1 n2 : K) : K := n2-(1+t)*n1+t
def normU (r _t n1 n2 : K) : K := n2-(1+r)*n1+r

def uAmp (r : K) : K :=
  -r^3*(r+1)^2*(2*r-1)*(5*r^2-14*r+5)/(36*(r-1)*(D r)^4)

theorem cofactor_pair (r : K) (r0 : r≠0) (r1 : r≠1) (r2 : r≠2)
    (dr : D r≠0) (qr : Q r≠0) :
    -(Seed.k r)*Seed.sigma*normD r (tu r) (nOne r) (nTwo r)=
      (Seed.sigma*Seed.p r)*normV r (tu r) (nOne r) (nTwo r)/r := by
  have f1 := sub_ne_zero.mpr r1
  have f2 := sub_ne_zero.mpr r2
  unfold Seed.k Seed.lambda Seed.sigma Seed.p normD normV tu nOne nTwo
  field_simp [r0,f1,f2,dr,qr]
  unfold D Q
  ring

theorem cofactor_u (r : K) (r0 : r≠0) (r1 : r≠1)
    (dr : D r≠0) (qr : Q r≠0) (t0 : tu r≠0) :
    uAmp r*normU r (tu r) (nOne r) (nTwo r)/tu r=
      (Seed.sigma*Seed.p r)*normV r (tu r) (nOne r) (nTwo r)/r := by
  have f1 := sub_ne_zero.mpr r1
  have rP : r+1≠0 := by
    intro e
    apply t0
    simp [tu,e]
  unfold Seed.sigma Seed.p normU normV uAmp nOne nTwo tu
  field_simp [r0,f1,dr,qr,rP]
  unfold D Q
  ring

theorem primitive_u (r : K) (r1 : r≠1) (dr : D r≠0) :
    (tu r)^4/4-(tu r)^3*(1+r)/3+r*(tu r)^2/2+
      Seed.lambda r*uAmp r=0 := by
  have f1 := sub_ne_zero.mpr r1
  unfold Seed.lambda uAmp tu
  field_simp [f1,dr]
  unfold D
  ring

end RKResearch.Certified.DIRK12MidpointReverse.Shape

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Shape.geometry
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Shape.cofactor_pair
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Shape.cofactor_u
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Shape.primitive_u
