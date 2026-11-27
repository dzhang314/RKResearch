module

@[expose] public section

/-! Core finite arithmetic for the symmetric rank-one DIRK10 obstruction.
This certifies the final bounded enumerations, not an unrestricted lower
bound or the separate tableau-to-arithmetic reduction. -/

namespace RKResearch.Certified.DIRK10SymmetricThreePortArithmetic

set_option maxRecDepth 40000
set_option maxHeartbeats 0

def removeFactor (p : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => if n%p=0 then removeFactor p k (n/p) else n

def smooth (x : Int) : Bool :=
  let n := x.natAbs
  decide (0<n) &&
    decide (removeFactor 7 32 (removeFactor 5 32
      (removeFactor 3 32 (removeFactor 2 32 n))) = 1)

def candidatesC : List (Nat × Nat) :=
  (List.range' 1 6).flatMap fun (m : Nat) =>
    (List.range' 1 10).filterMap fun (n : Nat) =>
      let u : Int := 3*(m:Int)^2-(n:Int)^2
      let v : Int := 2*(m:Int)^2-(n:Int)^2
      let w : Int := 9*(m:Int)^2-5*(n:Int)^2
      if (decide (Nat.gcd m n=1) && smooth (n:Int) && smooth u && smooth v && smooth w) then
        some (m,n) else none

theorem candidatesC_eq : candidatesC = [(1,1),(1,3),(2,3)] := by decide +kernel

def forms : List (Int × Int) := [(1,0),(1,1),(1,-1),(1,2),(1,-2),(3,2),(3,-2)]

def determinant (u v : Int × Int) : Nat :=
  (u.1*v.2-u.2*v.1).natAbs

theorem determinantCap :
    (forms.all fun u => forms.all fun v =>
      decide (u=v ∨ (0<determinant u v ∧ 120 % determinant u v=0))) = true := by
  decide +kernel

def candidatesA : List (Nat × Nat × Int) :=
  ((List.range' 1 720).filter fun (n : Nat) => smooth (n:Int)).flatMap fun (n : Nat) =>
    ((List.range' 1 480).filter fun (m : Nat) => smooth (m:Int)).filterMap fun (m : Nat) =>
      if (decide (Nat.gcd m n=1) &&
        forms.all (fun (u,v) => smooth (u*(m:Int)+v*(n:Int)))) then
        some (m,n,145*(m:Int)^2-159*(n:Int)^2) else none

theorem candidatesA_eq :
    candidatesA = [(4,1,2161),(6,1,5061),(1,2,-491),(1,3,-1286),
      (4,3,889),(2,5,-3395),(2,7,-7211)] := by decide +kernel

theorem allTerminalNonsmooth :
    (candidatesA.all fun (_,_,w) => !smooth w) = true := by
  rw [candidatesA_eq]
  decide +kernel

theorem pinEleven :
    ((List.range 11).all fun x =>
      decide ((21*x*x*5 + 11*100 - 9*(x*x+5)+5)%11=0 ↔ x*x%11=5)) = true := by
  decide +kernel

#print axioms candidatesC_eq
#print axioms determinantCap
#print axioms allTerminalNonsmooth
#print axioms pinEleven

end RKResearch.Certified.DIRK10SymmetricThreePortArithmetic
