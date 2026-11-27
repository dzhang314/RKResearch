import Lean

/-! Exact pooled-moment gates for the sole invisible ghost's
many-clock outgoing column and balanced reverse defect. -/
namespace RKResearch.ERK10InvisibleReversePooledGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem uniformOpposedPair (a b u v : K)
    (a0 : a ≠ 0) (u0 : u ≠ 0)
    (m1 : a*u+b*v=0) (m2 : a*u^2+b*v^2=0) :
    u=v ∧ a+b=0 := by
  have h : a*u*(u-v)=0 := by
    calc
      _=(a*u^2+b*v^2)-v*(a*u+b*v) := by clear m1 m2; grind
      _=0 := by rw [m1,m2]; grind
  have e : u=v := by grind
  exact ⟨e, by grind⟩

theorem isolatedThird (a b c u v w : K)
    (m1 : a*u+b*v+c*w=0) (m2 : a*u^2+b*v^2+c*w^2=0)
    (m3 : a*u^3+b*v^3+c*w^3=0) :
    a*u*(u-v)*(u-w)=0 := by
  calc
    _=(a*u^3+b*v^3+c*w^3)-(v+w)*(a*u^2+b*v^2+c*w^2)
          +v*w*(a*u+b*v+c*w) := by clear m1 m2 m3; grind
    _=0 := by rw [m1,m2,m3]; grind

theorem uniformTriple (a b c u v w : K)
    (a0 : a ≠ 0) (b0 : b ≠ 0) (c0 : c ≠ 0)
    (u0 : u ≠ 0) (v0 : v ≠ 0) (w0 : w ≠ 0)
    (m1 : a*u+b*v+c*w=0) (m2 : a*u^2+b*v^2+c*w^2=0)
    (m3 : a*u^3+b*v^3+c*w^3=0) :
    u=v ∧ v=w ∧ a+b+c=0 := by
  have hu := isolatedThird a b c u v w m1 m2 m3
  have hv := isolatedThird b c a v w u (by grind) (by grind) (by grind)
  have hw := isolatedThird c a b w u v (by grind) (by grind) (by grind)
  have eu : u=v ∨ u=w := by grind
  have ev : v=w ∨ v=u := by grind
  have ew : w=u ∨ w=v := by grind
  have uv : u=v := by grind
  have vw : v=w := by grind
  exact ⟨uv,vw,by grind⟩

theorem threeMasses (x y z a b c : K)
    (yz : y ≠ z) (m0 : a+b+c=0) (m1 : x*a+y*b+z*c=0)
    (a0 : a=0) : b=0 ∧ c=0 := by
  have c_eq : c = -b := by grind
  have h : b*(y-z)=0 := by
    calc
      _=(x*a+y*b+z*c)-z*(a+b+c)-(x-z)*a := by clear m0 m1 a0 c_eq; grind
      _=0 := by rw [m0,m1,a0]; grind
  exact ⟨by grind,by grind⟩

theorem fourMasses (x y z w a b c d : K)
    (zw : z ≠ w) (yz : y ≠ z) (yw : y ≠ w)
    (m0 : a+b+c+d=0) (m1 : x*a+y*b+z*c+w*d=0)
    (m2 : x^2*a+y^2*b+z^2*c+w^2*d=0) (a0 : a=0) :
    b=0 ∧ c=0 ∧ d=0 := by
  have h : b*(y-z)*(y-w)=0 := by
    calc
      _=(x^2*a+y^2*b+z^2*c+w^2*d)-(z+w)*(x*a+y*b+z*c+w*d)
           +z*w*(a+b+c+d)-(x-z)*(x-w)*a := by
              clear m0 m1 m2 a0
              grind
      _=0 := by rw [m0,m1,m2,a0]; grind
  have b0 : b=0 := by grind
  have cc : c+d=0 := by grind
  have ww : z*c+w*d=0 := by grind
  have o := threeMasses y z w b c d zw (by grind) (by grind) b0
  exact ⟨b0,o⟩

theorem liveCount (q : Nat) (q4 : 4≤q)
    (budget : 6≤13-(2*q-1)) : q=4 := by omega

theorem exactPairCensus (s a b c : Nat) (s2 : 2≤s)
    (a3 : 3≤a) (b3 : 3≤b) (c3 : 3≤c)
    (budget : s+a+b+c ≤11) : s=2 ∧ a=3 ∧ b=3 ∧ c=3 := by omega

theorem allTwoWhenOnlyOnePool (s a b c : Nat) (s2 : 2≤s)
    (a2 : 2≤a) (b2 : 2≤b) (c2 : 2≤c)
    (budget : 6 ≤ 13-(s+a+b+c)+1) : s=2 ∧ a=2 ∧ b=2 ∧ c=2 := by omega

def lobatto (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1

theorem noLobattoDoubling (x : K) (a : lobatto x=0)
    (b : lobatto (2*x)=0) : False := by
  have eq :
      (182784*x^3-102144*x^2+11200*x-176)*lobatto x
       +(-11424*x^3+17808*x^2-7084*x+235)*lobatto (2*x)=59 := by
    unfold lobatto
    clear a b
    grind
  rw [a,b] at eq
  grind

end RKResearch.ERK10InvisibleReversePooledGate

#print axioms RKResearch.ERK10InvisibleReversePooledGate.uniformOpposedPair
#print axioms RKResearch.ERK10InvisibleReversePooledGate.isolatedThird
#print axioms RKResearch.ERK10InvisibleReversePooledGate.uniformTriple
#print axioms RKResearch.ERK10InvisibleReversePooledGate.threeMasses
#print axioms RKResearch.ERK10InvisibleReversePooledGate.fourMasses
#print axioms RKResearch.ERK10InvisibleReversePooledGate.liveCount
#print axioms RKResearch.ERK10InvisibleReversePooledGate.exactPairCensus
#print axioms RKResearch.ERK10InvisibleReversePooledGate.allTwoWhenOnlyOnePool

#print axioms RKResearch.ERK10InvisibleReversePooledGate.noLobattoDoubling
