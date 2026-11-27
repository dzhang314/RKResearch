import Lean

/-! Scalar certificates for the actual two-generator endpoint-tail reduction.
Physical chronology, rooted lifts, and the paid field transfer are in the note. -/
namespace RKResearch.ERK11TwoGeneratorTailGate
open Lean.Grind
variable {K : Type} [Field K]

theorem paidModes (t a d B e x : K) (n2 : (2:K) ≠ 0)
    (h2 : 2*(2*a+d)=2*(t*x+B)+e)
    (h3 : 3*(3*a+d)=3*(t*(2*a+d)+B)+e)
    (h4 : 4*(4*a+d)=4*(t*(3*a+d)+B)+e) :
    e=12*a*(t-1) ∧ t*(x-d)=a := by
  have he : e=12*a*(t-1) := by grind
  have h : 2*(t*(x-d)-a)=0 := by grind
  exact ⟨he,AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero h).resolve_left n2)⟩

theorem normalizedMode (t d e f x : K) (n2 : (2:K) ≠ 0)
    (h2 : 2*(2+d)=2*t*x+e)
    (he : e=12*(t-1)) (hx : t*(x-d)=1)
    (hf : 24*x=24*(1+d)+f) :
    d*(t-1)+6*t-7=0 ∧ t*f=24*(1-t) := by
  have u : 2*(d*(t-1)+6*t-7)=0 := by grind
  exact ⟨(Field.of_mul_eq_zero u).resolve_left n2,by grind⟩

private theorem headCombination (t v d e s L g : K) :
    6*(L*((4-s)*(d+6)+4*v)) =
      t*(L*(24*g+288-144*v+6*s*(-8-d+3*v))) -
      L*((24*t*g+24*e-e*s)-24*(d+v)) +
      L*(24-s)*(e-12*(t-1)) +
      (6*L*s)*(d*(t-1)+6*t-7) +
      (144*L-18*L*s)*(t*v-1) := by grind

private theorem pureSubstitute (v d s L g k2 k3 k5 : K)
    (a : k2= -6*L*(4+d-v)) (b : k3=12*L*(6+d-2*v))
    (p0 : 24*L*g+24*k2+12*k3+k5=0)
    (last : k5+s*(k2+k3)=0) :
    L*(24*g+288-144*v+6*s*(-8-d+3*v))=0 := by
  calc
    _ = 24*L*g+24*(-6*L*(4+d-v))+12*(12*L*(6+d-2*v)) -
      s*((-6*L*(4+d-v))+(12*L*(6+d-2*v))) := by
        clear a b p0 last
        grind
    _ = 24*L*g+24*k2+12*k3-s*(k2+k3) := by rw [←a,←b]
    _ = 0 := by grind

theorem quadraticHead (t v d e s L g k2 k3 k5 : K)
    (n6 : (6:K) ≠ 0)
    (tv : t*v=1) (dd : d*(t-1)+6*t-7=0) (ee : e=12*(t-1))
    (g0 : 24*t*g+24*e-e*s=24*(d+v))
    (pure0 : 24*L*g+24*k2+12*k3+k5=0)
    (pure1 : 6*L*(d+v)+3*k2+k3=0)
    (pure2 : 12*L*(2+d)+4*k2+k3=0)
    (last : k5+s*(k2+k3)=0) :
    L*(t*s-8*t+4)=0 := by
  have k2' : k2= -6*L*(4+d-v) := by grind
  have k3' : k3= 12*L*(6+d-2*v) := by grind
  have base := pureSubstitute v d s L g k2 k3 k5 k2' k3' pure0 last
  have b2 : (6:K)*(L*((4-s)*(d+6)+4*v))=0 := by
    rw [headCombination,base,g0,ee,dd,tv]
    grind
  have b3 := (Field.of_mul_eq_zero b2).resolve_left n6
  have b4 : L*(8-s-4*v)=0 := by
    have s1 : (d+6)*(t-1)=1 := by grind
    calc
      _ = L*((4-s)*1+4*(1-v)) := by grind
      _ = L*((4-s)*((d+6)*(t-1))+4*(v*t-v)) := by
        have tt : v*t=1 := by grind
        rw [s1,tt]
      _ = (t-1)*(L*((4-s)*(d+6)+4*v)) := by grind
      _ = 0 := by rw [b3,Semiring.mul_zero]
  have b5 := congrArg (fun q => t*q) b4
  have b6 := congrArg (fun q => 4*L*q) tv
  grind

theorem tailCurve (t p q s J L : K) (n2 : (2:K) ≠ 0)
    (head : L*(t*s-8*t+4)=0)
    (third : p*s+(2-4*p)*J+4*(p-1)=0)
    (fourth : q*J=4*q-1) :
    L*(2*p*q*(t+1)-2*t*(p+q)+t)=0 := by
  have vv : q*p*s-12*p*q+4*p+4*q-2=0 := by
    have h := congrArg (fun x => q*x) third
    have k := congrArg (fun x => (2-4*p)*x) fourth
    grind
  have zz : 2*(L*(2*p*q*(t+1)-2*t*(p+q)+t))=0 := by
    have h := congrArg (fun x => (L*t)*x) vv
    have k := congrArg (fun x => (p*q)*x) head
    grind
  exact (Field.of_mul_eq_zero zz).resolve_left n2

theorem tiedDefect (t v d L k2 a : K)
    (n6 : (6:K) ≠ 0) (nt : t-1 ≠ 0)
    (tv : t*v=1) (dd : d*(t-1)+6*t-7=0)
    (k : k2= -6*L*(4+d-v))
    (clock : (12*(t-1))*a=(12*(t-1))*L+(1-t)*k2) :
    2*t*(t-1)*a=L := by
  have ab : (t-1)*(12*a-12*L+k2)=0 := by grind
  have abc := (Field.of_mul_eq_zero ab).resolve_left nt
  have eq : 12*a=6*L*(6+d-v) := by grind
  have r1 : (6+d)*(t-1)=1 := by grind
  have r2 : (t*(t-1))*(6+d-v)=1 := by
    have z := congrArg (fun h => t*h) r1
    have p := congrArg (fun h => (t-1)*h) tv
    grind
  have n : 6*(2*t*(t-1)*a-L)=0 := by
    have z := congrArg (fun h => (t*(t-1))*h) eq
    have p := congrArg (fun h => (6*L)*h) r2
    grind
  exact AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero n).resolve_left n6)

theorem tiedResonance (p k a2 a3 : K) (n12 : (12:K) ≠ 0)
    (h2 : a2 = -6*k) (h3 : a3=12*k)
    (diag : -a2+(p-1)*a3=0) :
    (2*p-1)*k=0 := by
  have n : 6*((2*p-1)*k)=0 := by grind
  have n6 : (6:K) ≠ 0 := by
    intro w
    apply n12
    grind
  exact (Field.of_mul_eq_zero n).resolve_left n6

end RKResearch.ERK11TwoGeneratorTailGate
#print axioms RKResearch.ERK11TwoGeneratorTailGate.paidModes
#print axioms RKResearch.ERK11TwoGeneratorTailGate.normalizedMode
#print axioms RKResearch.ERK11TwoGeneratorTailGate.quadraticHead
#print axioms RKResearch.ERK11TwoGeneratorTailGate.tailCurve
#print axioms RKResearch.ERK11TwoGeneratorTailGate.tiedDefect
#print axioms RKResearch.ERK11TwoGeneratorTailGate.tiedResonance
