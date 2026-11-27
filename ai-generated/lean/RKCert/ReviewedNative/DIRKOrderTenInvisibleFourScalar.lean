module

public import Init

@[expose] public section

/-! # Mod-227 clock-only certificate for four invisible dirty rows

The roots, matrix rows, and division guards in this module are finite.
The tableau-to-matrix reduction and characteristic-zero good reduction
are proved in the companion mathematical note. No tableau coefficient
is reduced modulo 227. -/
namespace RKResearch.Certified.Graded.InvisibleFourScalar

abbrev p : Nat := 227

def add (a b : Nat) : Nat := (a+b)%p
def sub (a b : Nat) : Nat := (a%p+p-b%p)%p
def mul (a b : Nat) : Nat := (a*b)%p
def power (a n : Nat) : Nat := a^n%p
def divide (a b : Nat) : Nat := mul a (power b (p-2))

/-- Determinants by signed Laplace expansion, with all entries reduced. -/
def det : Nat → (Nat → Nat → Nat) → Nat
  | 0, _ => 1
  | n+1, M => (List.range (n+1)).foldl (fun s j =>
      let minor := det n (fun i k => M (i+1) (if k<j then k else k+1))
      let x := mul (M 0 j) minor
      if j%2=0 then add s x else sub s x) 0

/-- Exact Cramer's rule, undefined on a zero determinant. The fourth
argument chooses a separate contrast column (rather than modifying
the first, common-core column). -/
def solve (clocks : List Nat) (target kappa lambda : Nat) (contrast : Bool := false) :
    Option (List Nat) :=
  let n := clocks.length
  let col := if contrast then n-1 else 0
  let M := fun i j =>
    let x := power (clocks[j]?.getD 0) (i+1)
    if j=col then sub x (if i=2 then kappa else if i=3 then lambda else 0) else x
  let D := det n M
  if D=0 then none else
    let inv := power D (p-2)
    some ((List.range n).map fun q =>
      let z := det n (fun i j => if j=q then divide (power target (i+2)) (i+2) else M i j)
      mul z inv)

def lerp (x y a b z : Nat) : Nat := add a (divide (mul (sub b a) (sub z x)) (sub y x))

def quartic (x : Nat) : Nat :=
  add (sub (add (sub (mul 42 (power x 4)) (mul 84 (power x 3)))
    (mul 56 (power x 2))) (mul 14 x)) 1

def interior : List Nat := [24,51,177,204]
def clockSet : List Nat := interior ++ [1]

theorem quartic_roots : (List.range p).filter (fun x => quartic x == 0) = interior := by decide

theorem paid_divisions : [2,3,4,5,6,7,8,9,10].all (fun x => mul x (divide 1 x) == 1) = true := by
  decide

/-- u is the reflected repeated core clock; v,w,z are the first three
other reflected clocks. An unsuccessful linear system or zero divisor
makes the test fail, rather than being omitted from the certificate. -/
def tupleGood (u v w z : Nat) : Bool :=
  match solve [u,v] v 0 0 with
  | some [tv,dv] =>
    if tv=0 ∨ dv=0 then false else
    let kappa := divide (sub (add (mul dv (power v 3)) (mul tv (power u 3)))
      (divide (power v 4) 4)) tv
    let Lv := divide (sub (add (mul dv (power v 4)) (mul tv (power u 4)))
      (divide (power v 5) 5)) tv
    match solve [u,v,w] w kappa 0 with
    | some [tw,vw,dw] =>
      if tw=0 ∨ dw=0 then false else
      let Lw := divide (sub (add (add (mul dw (power w 4)) (mul tw (power u 4))) (mul vw (power v 4)))
        (divide (power w 5) 5)) tw
      let Lz := lerp v w Lv Lw z
      let Lu := lerp v w Lv Lw u
      match solve [u,v,w,z] z kappa Lz, solve [u,v,w,u] u kappa Lu, solve [u,v,u] u kappa 0 with
      | some [_,_,_,dz], some [_,_,_,dq2], some [hq,vq,dq1] =>
        if dz=0 ∨ dq2=0 ∨ hq=0 ∨ dq1=0 then false else
        let Lu1 := divide (sub (add (mul (add hq dq1) (power u 4)) (mul vq (power v 4)))
          (divide (power u 5) 5)) hq
        let Lw1 := lerp u v Lu1 Lv w
        match solve [u,v,w,0] w kappa Lw1 true with
        | some [_,_,dw1,_] => dw1 != 0
        | _ => false
      | _,_,_ => false
    | _ => false
  | _ => false

def distinct (u v w z : Nat) : Bool :=
  u != v && u != w && u != z && v != w && v != z && w != z

def goodCore (u : Nat) : Bool :=
  clockSet.all fun v => clockSet.all fun w => clockSet.all fun z =>
    if distinct u v w z then tupleGood u v w z else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem all_distinct_clock_tuples : clockSet.all goodCore = true := by decide

end RKResearch.Certified.Graded.InvisibleFourScalar
