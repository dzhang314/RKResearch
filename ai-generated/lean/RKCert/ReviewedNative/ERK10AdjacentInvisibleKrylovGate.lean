import Lean

/-! Ring arithmetic and exact two-level clock filtration for the
adjacent two-invisible-ghost cyclic rank-two room. -/
namespace RKResearch.ERK10AdjacentInvisibleKrylovGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem ghostTap (theta eta d k a : K) (dj : d=theta*a-eta^2/2)
    (kq : 2*k*d=theta^2) (hit : theta^2+k*eta^2 ≠ 0) : a≠0 := by
  intro a0
  have d0 : d=-eta^2/2 := by grind
  rw [d0] at kq
  grind

theorem addedMoment (a b c m4 m5 m6 : K) (m4z : m4=0) (m5z : m5=0)
    (cz : c ≠ 0) (newTest : a*m4+b*m5+c*m6=0) : m6=0 := by grind

variable {n : Nat}
def clock (c x : Fin n → K) : Fin n → K := fun i => c i*x i
def span2 (q p x : Fin n → K) : Prop :=
  ∃ a b : K, ∀ i, x i=a*q i+b*p i
def span3 (q p cp x : Fin n → K) : Prop :=
  ∃ a b d : K, ∀ i, x i=a*q i+b*p i+d*cp i

theorem firstFilter (c q p x : Fin n → K)
    (qZero : ∀ i, c i*q i=0)
    (no : ¬span3 q p (clock c p) (clock c (clock c p)))
    (old : span3 q p (clock c p) x)
    (raised : span3 q p (clock c p) (clock c x)) : span2 q p x := by
  obtain ⟨a,b,d,h⟩ := old
  obtain ⟨aa,bb,dd,hh⟩ := raised
  by_cases dz : d=0
  · refine ⟨a,b,?_⟩
    intro i
    have hi := h i
    rw [dz] at hi
    grind
  · exfalso
    apply no
    refine ⟨aa/d,bb/d,(dd-b)/d,?_⟩
    intro i
    have hi := h i
    have hj := hh i
    have z := qZero i
    simp only [clock] at hi hj ⊢
    have row : d*(c i*(c i*p i))=
          aa*q i+bb*p i+(dd-b)*(c i*p i) := by
      calc
        _=c i*(a*q i+b*p i+d*(c i*p i))-a*(c i*q i)-b*(c i*p i) := by
          clear hi hj z
          grind
        _=_ := by rw [← hi,hj,z]; grind
    grind

theorem secondFilter (c q p x : Fin n → K)
    (qZero : ∀ i, c i*q i=0) (no : ¬span2 q p (clock c p))
    (old : span2 q p x) (raised : span2 q p (clock c x)) :
    ∃ a : K, ∀ i, x i=a*q i := by
  obtain ⟨a,b,h⟩ := old
  obtain ⟨aa,bb,hh⟩ := raised
  by_cases bz : b=0
  · refine ⟨a,?_⟩
    intro i
    have hi := h i
    rw [bz] at hi
    grind
  · exfalso
    apply no
    refine ⟨aa/b,bb/b,?_⟩
    intro i
    have hi := h i
    have hj := hh i
    have z := qZero i
    simp only [clock] at hj ⊢
    have row : b*(c i*p i)=aa*q i+bb*p i := by
      calc
        _=c i*(a*q i+b*p i)-a*(c i*q i) := by clear hi hj z; grind
        _=_ := by rw [← hi,hj,z]; grind
    grind

theorem sameReverseAmplitude (a b u v : K)
    (al : a ≠ 0) (first : a+b=0) (second : a*u+b*v=0) :
    u=v := by grind

theorem carrierFourthNoRead (t a b : K) (live : t ≠ 0)
    (quad : a+t*b=0) (cube : 2*t*a+3*t^2*b=0) :
    a=0 ∧ b=0 := by
  have bz : t^2*b=0 := by grind
  grind

end RKResearch.ERK10AdjacentInvisibleKrylovGate
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.ghostTap
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.addedMoment
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.firstFilter
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.secondFilter
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.sameReverseAmplitude
#print axioms RKResearch.ERK10AdjacentInvisibleKrylovGate.carrierFourthNoRead
