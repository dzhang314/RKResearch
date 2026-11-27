import Lean

/-! Exact scalar gates for the all-early-output-live ERK11 endpoint reduction.
The accompanying proof supplies the actual rooted, rank, and support transfers. -/
namespace RKResearch.ERK11LiveTailGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem mulNz {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

/-- Positive moments of the two grade-six generators and the first
unary lift have determinant equal to the inverse first clock, after
scaling the third column by twelve. -/
theorem independentThirdRead (v a b c : K) (nv : v ≠ 0)
    (e1 : a+b*v+6*c=0) (e2 : a+2*b+4*c=0)
    (e3 : a+3*b+3*c=0) : a=0 ∧ b=0 ∧ c=0 := by
  have q : b=c := by grind
  have r : v*b=0 := by grind
  have z := (Field.of_mul_eq_zero r).resolve_left nv
  exact ⟨by grind,z,by grind⟩

/-- Two nonzero quadratic carrier values at the same clock must
agree if both paid pure products are seen by the same tail atom. -/
theorem sameCarrierValue (a b x y : K) (na : a ≠ 0) (nx : x ≠ 0)
    (e1 : a*x+b*y=0) (e2 : a*x*x+b*y*y=0) : x=y := by
  have z : (a*x)*(x-y)=0 := by
    have w := congrArg (fun h => h*y) e1
    grind
  exact AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero z).resolve_left (mulNz na nx))

/-- In the half-clock branch the three off-carrier loads are zero
together on the two forward annihilating rows. -/
theorem halfClockLoads (a b c u v w : K) (nu : u ≠ 0)
    (nvw : v-w ≠ 0)
    (pair : b+c=0) (head : u*a+v*b+w*c=0) :
    (a=0 ↔ b=0) ∧ (b=0 ↔ c=0) := by
  have q : u*a+(v-w)*b=0 := by grind
  constructor
  · constructor
    · intro ea
      have z : (v-w)*b=0 := by grind
      exact (Field.of_mul_eq_zero z).resolve_left nvw
    · intro eb
      have z : u*a=0 := by grind
      exact (Field.of_mul_eq_zero z).resolve_left nu
  · constructor <;> intro e <;> grind

/-- Three distinct weighted scalar sites cannot carry a nonzero
annihilator of the three consecutive low powers. -/
theorem threeCharges (x y z a b c : K)
    (hxy : x-y ≠ 0) (hxz : x-z ≠ 0) (hyz : y-z ≠ 0)
    (e0 : a+b+c=0) (e1 : a*x+b*y+c*z=0)
    (e2 : a*x*x+b*y*y+c*z*z=0) : a=0 ∧ b=0 ∧ c=0 := by
  have r : a*(x-y)*(x-z)=0 := by
    have s := congrArg (fun q => (y+z)*q) e1
    have t := congrArg (fun q => (y*z)*q) e0
    grind
  have az := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero r).resolve_right hxz)).resolve_right hxy
  have q : b*(y-z)=0 := by
    have w := congrArg (fun q => q*z) e0
    grind
  have bz := (Field.of_mul_eq_zero q).resolve_right hyz
  exact ⟨az,bz,by grind⟩

private theorem quadraticExpansion (t z L a f : K)
    (na : (6:K) ≠ 0)
    (first : 2*t*(t-1)*a=L)
    (rest : 12*t*(t-1)*(t-1)*(f-a)=
        -6*L*(z-1)*(1-2*t*(t-1)+2*(z-t)*(2-t))) :
    2*t*(t-1)*(t-1)*f=L*(2*(t-2)*z*z+3*z-t) := by
  have h : 6*(2*t*(t-1)*(t-1)*f-L*(2*(t-2)*z*z+3*z-t))=0 := by
    have k := congrArg (fun q => (6*(t-1))*q) first
    grind
  exact AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero h).resolve_left na)

/-- The same quadratic fits the physical defect at each of the
four distinct supporting tail clocks, without dividing by a node. -/
theorem propagatedQuadratic (t v d L z a f k2 k3 : K)
    (n6 : (6:K) ≠ 0) (tv : t*v=1) (hd : (d+6)*(t-1)=1)
    (hk2 : k2= -6*L*(4+d-v)) (hk3 : k3=12*L*(6+d-2*v))
    (first : 2*t*(t-1)*a=L)
    (transport : 12*(t-1)*(f-a)=(z-1)*(k2-(z-t)*k3)) :
    2*t*(t-1)*(t-1)*f=L*(2*(t-2)*z*z+3*z-t) := by
  have m2 : (t*(t-1))*(4+d-v)=1-2*t*(t-1) := by
    have g := congrArg (fun q => t*q) hd
    have h := congrArg (fun q => (t-1)*q) tv
    grind
  have m3 : (t*(t-1))*(6+d-2*v)=2-t := by
    have g := congrArg (fun q => t*q) hd
    have h := congrArg (fun q => (2*(t-1))*q) tv
    grind
  have k2v : (t*(t-1))*k2=-6*L*(1-2*t*(t-1)) := by
    calc
      _ = (-6*L)*((t*(t-1))*(4+d-v)) := by rw [hk2]; grind
      _ = _ := by rw [m2]
  have k3v : (t*(t-1))*k3=12*L*(2-t) := by
    calc
      _ = (12*L)*((t*(t-1))*(6+d-2*v)) := by rw [hk3]; grind
      _ = _ := by rw [m3]
  apply quadraticExpansion t z L a f n6 first
  calc
    _ = (t*(t-1))*(12*(t-1)*(f-a)) := by grind
    _ = (t*(t-1))*((z-1)*(k2-(z-t)*k3)) := by rw [transport]
    _ = (z-1)*((t*(t-1))*k2-(z-t)*((t*(t-1))*k3)) := by grind
    _ = _ := by rw [k2v,k3v]; grind

end RKResearch.ERK11LiveTailGate
#print axioms RKResearch.ERK11LiveTailGate.independentThirdRead
#print axioms RKResearch.ERK11LiveTailGate.sameCarrierValue
#print axioms RKResearch.ERK11LiveTailGate.halfClockLoads
#print axioms RKResearch.ERK11LiveTailGate.threeCharges
#print axioms RKResearch.ERK11LiveTailGate.propagatedQuadratic
