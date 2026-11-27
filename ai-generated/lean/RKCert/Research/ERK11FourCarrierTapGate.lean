import Lean

/-! Literal six-slot path and low scalar gates for the half-clock
four-carrier ERK11 branch. Rooted grading and full supports are supplied
by the companion note. -/
namespace RKResearch.ERK11FourCarrierTapGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

/-- A truly strict principal six-block, using zero-based indices. -/
def step (a : Nat → Nat → K) (x : Nat → K) (i : Nat) : K :=
  match i with
  | 0 => 0
  | 1 => a 1 0 * x 0
  | 2 => a 2 0 * x 0 + a 2 1 * x 1
  | 3 => a 3 0 * x 0 + a 3 1 * x 1 + a 3 2 * x 2
  | 4 => a 4 0 * x 0 + a 4 1 * x 1 + a 4 2 * x 2 + a 4 3 * x 3
  | _ => a 5 0 * x 0 + a 5 1 * x 1 + a 5 2 * x 2 + a 5 3 * x 3 + a 5 4 * x 4

def chain (a : Nat → Nat → K) : Nat → Nat → K
  | 0 => fun _ => 1
  | n+1 => step a (chain a n)

/-- The degree-five chain at the sixth stage has just one
physical contributing path, independent of every off-path edge. -/
theorem uniqueFivePath (a : Nat → Nat → K) :
    chain a 5 5 = a 5 4 * (a 4 3 * (a 3 2 * (a 2 1 * a 1 0))) := by
  simp [chain, step, Semiring.mul_zero, Semiring.mul_one,
    Semiring.add_zero, AddCommMonoid.zero_add]

/-- Two clean sites at one fixed clock have paid model terms that
cancel. The only variation is then a common nonzero multiple of
their third-grade f-state difference. -/
theorem plateauNonzero (r4 r6 alpha T c5 : K)
    (nT : T ≠ 0) (diff : r6-r4 ≠ 0)
    (first : T+c5*r4=0) (next : alpha=T+c5*r6) :
    alpha ≠ 0 := by
  have nc : c5 ≠ 0 := by
    intro z
    apply nT
    grind
  have e : alpha=c5*(r6-r4) := by grind
  rw [e]
  exact nzMul nc diff

/-- Two actual fifth-carrier donor contrasts leave only the
half-clock front construction (the other root has unpaid D=0). -/
theorem fifthCarrier (N T : K) (nN : N ≠ 0) (n3 : (3:K) ≠ 0)
    (gap : 3*N-2*T ≠ 0)
    (g : N*T+3*N-2*T*T=0)
    (h : 5*N*T-3*N-4*T*T+3*T=0) :
    2*N=1 ∧ T=1 := by
  have r : 3*(T*(N+1)-3*N)=0 := by grind
  have rv := AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero r).resolve_left n3)
  have expand :
      ((N+1)*(N+1))*(N*T+3*N-2*T*T) =
        (N*(N+1))*(T*(N+1))+3*N*(N+1)*(N+1)-2*(T*(N+1))*(T*(N+1)) := by grind
  rw [g,Semiring.mul_zero,rv] at expand
  have mulg : (3*N)*((2*N-1)*(N-1))=0 := by grind
  have roots := (Field.of_mul_eq_zero mulg).resolve_left (nzMul n3 nN)
  have n1 : (N-1) ≠ 0 := by
    intro z
    have q := AddCommGroup.sub_eq_zero_iff.mp z
    apply gap
    grind
  have half := AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero roots).resolve_right n1)
  have s : 3*(T-1)=0 := by
    have k := congrArg (fun x => (2:K)*x) rv
    grind
  exact ⟨half,AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero s).resolve_left n3)⟩

/-- A repeated-clock carrier in slot six cannot read the second
preceding clean state at that clock. All equations are actual
low-degree derivative rows in the normalized front. -/
theorem sixthCarrier (N a x u v f4 f5 : K)
    (nN : N ≠ 0) (na : a ≠ 0) (n2 : (2:K) ≠ 0)
    (n3 : (3:K) ≠ 0) (diff : f5-f4 ≠ 0)
    (cube : (N-2*N*N)*a=0)
    (one : a+N*x+2*N*(u+v)=0)
    (two : 3*(a+N*N*x+4*N*N*(u+v))=(3-2*N)*a)
    (fval : 2*f4=-1)
    (fread : x+8*u*f4+8*v*f5= - (4*a)) :
    2*N=1 ∧ v=0 := by
  have nr : N*(1-2*N)*a=0 := by grind
  have rz := (Field.of_mul_eq_zero nr).resolve_right na
  have hh := (Field.of_mul_eq_zero rz).resolve_left nN
  have N0 : 2*N=1 := by grind
  have x0 : 3*x= -8*a := by
    have j := congrArg (fun t => 4*t) two
    have k := congrArg (fun t => 6*t) one
    grind
  have tv : 3*(u+v)=a := by
    have j := congrArg (fun t => 6*t) one
    grind
  have vv : 24*v*(f5-f4)=0 := by
    have h := congrArg (fun t => 3*t) fread
    have j := congrArg (fun t => (4*(3*(u+v)))*t) fval
    grind
  have n24 : (24:K) ≠ 0 := by
    have aa := nzMul (nzMul (nzMul n2 n2) n2) n3
    have k : (((2:K)*2)*2)*3=24 := by grind
    rw [k] at aa
    exact aa
  have qz := (Field.of_mul_eq_zero vv).resolve_right diff
  exact ⟨N0,(Field.of_mul_eq_zero qz).resolve_left n24⟩

/-- The new sixth clean stage is forced off all three preceding
clean clock labels when its incoming last edge is live. -/
theorem sixthClean (z f a edge : K)
    (n2 : (2:K) ≠ 0) (ne : edge*a ≠ 0)
    (cube : (z-1)*(f-z*z*(1-z))=0)
    (transport : 2*(edge*a)=(1-z)*(2*f-z*z)) :
    z ≠ 0 ∧ z ≠ 1 ∧ 2*z ≠ 1 ∧ f=z*z*(1-z) := by
  have nz1 : z-1 ≠ 0 := by
    intro h
    have hh := AddCommGroup.sub_eq_zero_iff.mp h
    have w : 2*(edge*a)=0 := by grind
    exact nzMul n2 ne w
  have ff := AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero cube).resolve_left nz1)
  have c : 2*(edge*a)=z*z*(1-z)*(1-2*z) := by grind
  have nz0 : z ≠ 0 := by
    intro h
    exact nzMul n2 ne (by rw [h] at c; grind)
  have nz2 : 2*z ≠ 1 := by
    intro h
    exact nzMul n2 ne (by grind)
  exact ⟨nz0,(fun h => nz1 (AddCommGroup.sub_eq_zero_iff.mpr h)),nz2,ff⟩

end RKResearch.ERK11FourCarrierTapGate
#print axioms RKResearch.ERK11FourCarrierTapGate.uniqueFivePath
#print axioms RKResearch.ERK11FourCarrierTapGate.plateauNonzero
#print axioms RKResearch.ERK11FourCarrierTapGate.fifthCarrier
#print axioms RKResearch.ERK11FourCarrierTapGate.sixthCarrier
#print axioms RKResearch.ERK11FourCarrierTapGate.sixthClean
