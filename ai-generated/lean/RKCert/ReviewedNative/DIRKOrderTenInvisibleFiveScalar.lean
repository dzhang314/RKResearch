module

public import Init

@[expose] public section

/-! # Exact forward and reverse fixed-clock tests for invisible five

All computations concern the two split reductions of the fixed
Lobatto polynomial. The companion note gives the actual tableau
reduction and number-field good reduction. No tableau values are
reduced modulo a prime.
-/
namespace RKResearch.Certified.Graded.InvisibleFiveScalar

def add (p a b : Nat) : Nat := (a+b)%p
def sub (p a b : Nat) : Nat := (a%p+p-b%p)%p
def mul (p a b : Nat) : Nat := (a*b)%p
def power (p a k : Nat) : Nat := a^k%p
def divide (p a b : Nat) : Nat := mul p a (power p b (p-2))

def det (p : Nat) : Nat → (Nat → Nat → Nat) → Nat
  | 0, _ => 1
  | n+1, M => (List.range (n+1)).foldl (fun s j =>
      let minor := det p n (fun i k => M (i+1) (if k<j then k else k+1))
      let x := mul p (M 0 j) minor
      if j%2=0 then add p s x else sub p s x) 0

def vals (p x k : Nat) : Nat := divide p (power p x (k+1)) (k+1)

def coeffs (p : Nat) : List Nat := [1,sub p 0 14,56,sub p 0 84,42]

def poly (p : Nat) (a : List Nat) (x : Nat) : Nat :=
  (List.range a.length).foldl (fun r j => add p r (mul p (a[j]?.getD 0) (power p x j))) 0

def integ (p : Nat) (a : List Nat) (x shift : Nat) : Nat :=
  (List.range a.length).foldl (fun r j => add p r (mul p (a[j]?.getD 0) (vals p x (j+shift)))) 0

def timesRoot (p : Nat) (a : List Nat) (r : Nat) : List Nat :=
  (List.range (a.length+1)).map fun j =>
    sub p (if j=0 then 0 else a[j-1]?.getD 0) (mul p r (a[j]?.getD 0))

def inside (p : Nat) : List Nat := (List.range p).filter (fun x => poly p (coeffs p) x == 0)

theorem roots227 : inside 227 = [24,51,177,204] := by decide
theorem roots59 : inside 59 = [14,23,37,46] := by decide

def anchored (p a b : Nat) : Nat :=
  det p 3 (fun i j =>
    if i=0 then vals p a (j+1)
    else if i=1 then vals p a (j+2)
    else sub p (vals p b (j+2)) (mul p a (vals p b (j+1))))

def firstInterior (p a b : Nat) : Nat :=
  let T := fun x => integ p (coeffs p) x 1
  det p 4 (fun i j =>
    if i=0 then power p a j
    else if i=1 then vals p a (j+1)
    else if i=2 then vals p b (j+1)
    else sub p (mul p (T b) (vals p a (j+2))) (mul p (T a) (vals p b (j+2))))

def withEnd (p : Nat) : List Nat := inside p ++ [1]

def anchorAll (p : Nat) : Bool :=
  (withEnd p).all fun a => (withEnd p).all fun b => if a=b then true else anchored p a b != 0

def noLeakZero (p : Nat) : Bool :=
  (withEnd p).all fun a => integ p (coeffs p) a 1 != 0

theorem forward227 :
    anchorAll 227 = true ∧ noLeakZero 227 = true ∧
    ((withEnd 227).all fun a => (withEnd 227).all fun b =>
      if a=b then true else firstInterior 227 a b != 0) = true := by decide

def factor (p a : Nat) : List Nat :=
  ((inside p).filter (fun x => x != a)).foldl (timesRoot p) [1]

theorem forward59 :
    anchorAll 59 = true ∧ noLeakZero 59 = true ∧
    ((inside 59).all fun a => ((inside 59).filter (fun x => x != a)).all
      fun z => integ 59 (factor 59 a) z 1 != 0) = true := by decide

/-- Cramer's rule for the moment powers 1,...,n on a clock list. -/
def solve (p : Nat) (clock rhs : List Nat) : Option (List Nat) :=
  let n := clock.length
  let M := fun i j => power p (clock[j]?.getD 0) (i+1)
  let D := det p n M
  if D=0 then none else
    let inv := power p D (p-2)
    some ((List.range n).map fun q =>
      mul p (det p n (fun i j => if j=q then rhs[i]?.getD 0 else M i j)) inv)

def affine (p u v a b x : Nat) : Nat :=
  add p a (divide p (mul p (sub p b a) (sub p x u)) (sub p v u))

def reverseTest (p u v w z : Nat) : Bool :=
  match solve p [u,v,w,z] ([1,2,3,4].map (vals p z)) with
  | some [a,b,c,_] =>
    if a=0 ∨ b=0 ∨ c=0 then false else
    let hu := divide p (power p u 3) 6
    let hv := divide p
      (sub p 0 (mul p (mul p a hu) (sub p w u))) (mul p b (sub p w v))
    let hw := divide p
      (mul p (mul p a hu) (sub p v u)) (mul p c (sub p w v))
    if hu=0 ∨ hv=0 ∨ hw=0 then false else
    match solve p [u,v] [vals p v 1,add p (vals p v 2) hv] with
    | some [t,d] =>
      let gu := divide p (mul p 3 u) 2
      let gv := divide p
        (sub p (add p (mul p t (power p u 3)) (mul p d (power p v 3))) (vals p v 3)) hv
      let Lu := divide p u 2
      let Lv := divide p (add p (mul p t hu) (mul p d hv)) hv
      let row3 := [vals p w 1,add p (vals p w 2) hw,
        add p (vals p w 3) (mul p (affine p u v gu gv w) hw)]
      match solve p [u,v,w] row3 with
      | some [tu,tv,dd] =>
        sub p (add p (add p (mul p tu hu) (mul p tv hv)) (mul p dd hw))
          (mul p (affine p u v Lu Lv w) hw) != 0
      | _ => false
    | _ => false
  | _ => false

def distinct (u v w z : Nat) : Bool :=
  u != v && u != w && u != z && v != w && v != z && w != z

def reverseAll (p : Nat) : Bool :=
  (inside p).all fun u => (inside p).all fun v => (inside p).all fun w =>
    (inside p).all fun z => if distinct u v w z then reverseTest p u v w z else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reverse59 : reverseAll 59 = true := by decide

end RKResearch.Certified.Graded.InvisibleFiveScalar
