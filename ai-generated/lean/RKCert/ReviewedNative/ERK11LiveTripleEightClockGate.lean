
/-!
Letter-checked coefficients and finite-field unit witnesses for the ERK11
nonzero-mass eight-clock reduction. Modular reductions concern finite
free polynomial algebras at rational parameters, not tableau entries.
-/
namespace RKResearch.ERK11LiveTripleEightClockGate
open Lean.Grind
set_option maxRecDepth 40000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

section Field
variable {K : Type} [Field K] [IsCharP K 0]

theorem halfJacobiBezout (x : K) :
    (-1428*x^3+4452*x^2-3542*x+235)*(42*x^4-84*x^3+56*x^2-14*x+1) +
      (2856*x^3-3192*x^2+700*x-22)*(21*x^4-84*x^3+112*x^2-56*x+8)=59 := by
  grind

theorem leftCramer (m0 m1 m2 m3 u v : K)
    (h0 : m0*v+m1*u+m2=0) (h1 : m1*v+m2*u+m3=0) :
    (m0*m2-m1^2)*u=m1*m2-m0*m3 ∧
    (m0*m2-m1^2)*v=m1*m3-m2^2 := by
  constructor <;> grind

theorem derivativeContactScale (a z x U V L R : K)
    (hL : L = a*(a/2)*z*U)
    (hR : R = -a*(a/2)*(a-z)*(U+a*V)) :
    (a-x)*(a-z)*L - x*z*R = a^2*(a/2)*z*(a-z)*(U+x*V) := by grind

theorem primitiveCalibration (a : K) :
    a^3*(6*a^2-15*a*a+10*a^2)/30=a^5/30 := by grind
end Field

structure Alg (α : Type) where
  z : α
  o : α
  c : Int → α
  a : α → α → α
  n : α → α
  m : α → α → α
  eq : α → α → Bool

def F : Alg Int :=
  ⟨0, 1, fun x => x % 101, fun x y => (x+y) % 101,
   fun x => (-x) % 101, fun x y => (x*y) % 101, (· == ·)⟩

def Q : Alg Rat :=
  ⟨0, 1, fun x => x, (·+·), Neg.neg, (·*·), (· == ·)⟩

def sub {α : Type} (R : Alg α) (x y : α) := R.a x (R.n y)

def mulx {α : Type} (R : Alg α) (g xs : List α) : List α :=
  let ld := xs.getLast?.getD R.z
  List.zipWith (fun x h => sub R x (R.m ld h)) (R.z :: xs) g

def liftC {α : Type} (R : Alg α) (g : List α) (x : α) : List α :=
  x :: List.replicate (g.length-1) R.z

def root {α : Type} (R : Alg α) (g : List α) : List α :=
  [R.z,R.o] ++ List.replicate (g.length-2) R.z

def ext {α : Type} (R : Alg α) (g : List α) : Alg (List α) :=
  ⟨List.replicate g.length R.z, liftC R g R.o, fun n => liftC R g (R.c n),
   List.zipWith R.a, List.map R.n,
   fun xs ys => xs.foldr (fun c out =>
       List.zipWith R.a (ys.map (R.m c)) (mulx R g out)) (List.replicate g.length R.z),
   fun xs ys => xs.length == ys.length && (List.zipWith R.eq xs ys).all id⟩

def get {α : Type} (R : Alg α) (xs : List α) (i : Nat) : α :=
  xs[i]?.getD R.z

def sumA {α : Type} (R : Alg α) (xs : List α) : α := xs.foldl R.a R.z
def productA {α : Type} (R : Alg α) (xs : List α) : α := xs.foldl R.m R.o

def eval {α : Type} (R : Alg α) (p : List Int) (x : α) : α :=
  p.foldr (fun w v => R.a (R.c w) (R.m x v)) R.z

def coeffs {α : Type} (R : Alg α) (xs : List α) : List α :=
  xs.foldl (fun cs x => List.zipWith (fun u v => sub R u (R.m x v))
    (R.z :: cs) (cs ++ [R.z])) [R.o]

def invM : List Int := [17,59,96,64,89,92,94,55,45,88]

def moments {α : Type} (R : Alg α) (w : Nat → α) (cs : List α) (n : Nat) : List α :=
  (List.range n).map (fun j => sumA R (cs.zipIdx.map (fun (c,i) => R.m c (w (i+j)))))

def mm {α : Type} (R : Alg α) (ns : List α) (n : Nat) : List α :=
  moments R (fun j => R.c (get F invM j)) (coeffs R ns) n

def mq (ns : List Rat) (lead : Rat) : List Rat :=
  moments Q (fun j => 1 / (Rat.ofInt (Int.ofNat (j+2))*Rat.ofInt (Int.ofNat (j+3))))
     ((coeffs Q ns).map (lead*·)) 5

def det3 {α : Type} (R : Alg α) (ms : List α) : α :=
  let a := get R ms 0
  let b := get R ms 1
  let c := get R ms 2
  let d := get R ms 3
  let e := get R ms 4
  sumA R [productA R [a,c,e], productA R [R.c 2,b,c,d],
    R.n (productA R [a,d,d]), R.n (productA R [b,b,e]), R.n (productA R [c,c,c])]

def conv (xs ys : List Int) : List Int :=
  (List.range (xs.length + ys.length - 1)).map (fun i =>
    sumA F ((List.range (i+1)).map (fun k => F.m (get F xs k) (get F ys (i-k)))))

def tPoly : List Int := [1,-32,216,-480,330]
def uPoly : List (List Int) :=
  [[1,-32,216,-480,330], [-32,992,-6480,13920,-9240],
   [216,-6480,41040,-85680,55440], [-480,13920,-85680,174720,-110880],
   [330,-9240,55440,-110880,69300]]
def invG : List (List Int) :=
  [[3,-32,108,-144,66], [-32,388,-1404,1956,-924],
   [108,-1404,5316,-7644,3696], [-144,1956,-7644,11256,-5544],
   [66,-924,3696,-5544,2772]]

def ints : Alg Int := ⟨0,1,id,(·+·),Neg.neg,(·*·),(· == ·)⟩
def derL (a : Int) (i : Nat) := (Int.ofNat (i+1))*a^i
def derR (b : Int) (j : Nat) := (1-b)^j - b*(Int.ofNat j)*(1-b)^(j-1)
def gramEval (l r : Nat → Int) : Int :=
  sumA ints ((List.range 5).map (fun i =>
    sumA ints ((List.range 5).map (fun j => l i*(get ints (invG[i]?.getD []) j)*r j))))

def matCheck : Bool := (List.range 5).all (fun i => (List.range 5).all (fun j =>
  (sumA Q ((List.range 5).map (fun k =>
      Rat.ofInt (210*get ints (invG[i]?.getD []) k) /
        Rat.ofInt (Int.ofNat ((j+k+2)*(j+k+3)))))) ==
    (if i==j then (1:Rat) else 0)))

def contactCheck : Bool :=
  gramEval (fun i => if i==0 then 1 else 0) (fun _ => 1) == 1 &&
  (List.range 5).all (fun a =>
    gramEval (derL a) (fun _ => 1) == eval ints tPoly a &&
    gramEval (fun i => if i==0 then 1 else 0) (derR a) == eval ints tPoly a &&
    (List.range 5).all (fun b =>
      gramEval (derL a) (derR b) ==
        (uPoly.foldr (fun p v => eval ints p b + Int.ofNat a * v) 0)))

def two : List Nat → List (List Nat)
  | [] => []
  | x::xs => xs.map (fun y => [x,y]) ++ two xs

def assignments (ll rr : List Nat) : List (List Nat × List Nat) :=
  (two ll).flatMap (fun l =>
    (two rr).filterMap (fun r => if l.contains 2 && r.contains 0 then none else some (l,r)))

def contact {α : Type} (R : Alg α) (cs : List α) (ll rr : List Nat) : α :=
  let a := get R cs 0
  let b := sub R R.o (get R cs 2)
  let x := get R cs (ll[0]?.getD 0)
  let z := get R cs (ll[1]?.getD 0)
  let u := sub R R.o (get R cs (rr[0]?.getD 0))
  let v := sub R R.o (get R cs (rr[1]?.getD 0))
  let l0 := R.m (sub R a x) (sub R a z)
  let l1 := R.n (R.m x z)
  let r0 := R.m (sub R b u) (sub R b v)
  let r1 := R.n (R.m u v)
  let kab := uPoly.foldr (fun p w => R.a (eval R p b) (R.m a w)) R.z
  sumA R [R.m l0 r0, productA R [l1,r0,eval R tPoly a],
           productA R [l0,r1,eval R tPoly b], productA R [l1,r1,kab]]

def vC : List Int := [16, -216, 1206, -3375, 4932, -3564, 990]

def vL : List Int := [20, -210, 910, -1995, 2303, -1323, 294]

def bezC : List Int := [44, 59, 40, 92, 26, 48]

def bezL : List Int := [81, 16, 40, 34, 37, 28]

def g0 : List Int := [1, 65, 66]

def w0 : List (List Nat × List Nat × List (List Int)) :=
  [([2, 4], [4, 5], [[13, 33, 3], [6, 34, 39]]),
   ([2, 4], [4, 6], [[60, 15, 70], [95, 67, 62]]),
   ([2, 4], [5, 6], [[91, 8, 40], [0, 0, 0]]),
   ([2, 5], [4, 5], [[59, 10, 98], [37, 83, 62]]),
   ([2, 5], [4, 6], [[16, 87, 61], [95, 61, 0]]),
   ([2, 5], [5, 6], [[16, 20, 31], [41, 46, 39]]),
   ([2, 6], [4, 5], [[8, 6, 0], [6, 40, 0]]),
   ([2, 6], [4, 6], [[2, 40, 15], [64, 18, 39]]),
   ([2, 6], [5, 6], [[76, 84, 86], [60, 55, 62]]),
   ([4, 5], [0, 4], [[30, 39, 34], [46, 36, 58]]),
   ([4, 5], [0, 5], [[100, 24, 67], [17, 12, 43]]),
   ([4, 5], [0, 6], [[12, 16, 0], [16, 100, 0]]),
   ([4, 5], [4, 5], [[55, 3, 0], [3, 29, 0]]),
   ([4, 5], [4, 6], [[4, 7, 67], [10, 23, 17]]),
   ([4, 5], [5, 6], [[9, 32, 34], [29, 46, 84]]),
   ([4, 6], [0, 4], [[82, 74, 99], [55, 65, 43]]),
   ([4, 6], [0, 5], [[67, 66, 1], [85, 1, 0]]),
   ([4, 6], [0, 6], [[31, 91, 55], [84, 89, 58]]),
   ([4, 6], [4, 5], [[68, 89, 44], [91, 78, 84]]),
   ([4, 6], [4, 6], [[59, 5, 72], [98, 72, 0]]),
   ([4, 6], [5, 6], [[98, 3, 89], [72, 55, 17]]),
   ([5, 6], [0, 4], [[2, 19, 100], [0, 0, 0]]),
   ([5, 6], [0, 5], [[53, 86, 2], [4, 57, 58]]),
   ([5, 6], [0, 6], [[49, 90, 46], [97, 44, 43]]),
   ([5, 6], [4, 5], [[19, 15, 57], [13, 45, 17]]),
   ([5, 6], [4, 6], [[87, 56, 12], [88, 56, 84]]),
   ([5, 6], [5, 6], [[25, 93, 29], [0, 0, 0]])]

def g1 : List Int := [60, 70, 33]

def w1 : List (List Nat × List Nat × List (List Int)) :=
  [([2, 4], [4, 5], [[72, 21, 89], [41, 15, 48]]),
   ([2, 4], [4, 6], [[84, 17, 74], [60, 86, 53]]),
   ([2, 4], [5, 6], [[49, 75, 78], [0, 0, 0]]),
   ([2, 5], [4, 5], [[55, 33, 12], [13, 59, 53]]),
   ([2, 5], [4, 6], [[43, 52, 23], [26, 23, 0]]),
   ([2, 5], [5, 6], [[3, 42, 27], [100, 81, 48]]),
   ([2, 6], [4, 5], [[94, 75, 0], [75, 78, 0]]),
   ([2, 6], [4, 6], [[79, 66, 54], [88, 42, 48]]),
   ([2, 6], [5, 6], [[88, 23, 47], [1, 20, 53]]),
   ([4, 5], [4, 5], [[26, 25, 0], [25, 70, 0]]),
   ([4, 5], [4, 6], [[90, 10, 44], [95, 53, 3]]),
   ([4, 5], [5, 6], [[18, 57, 57], [73, 11, 98]]),
   ([4, 6], [4, 5], [[64, 93, 92], [6, 48, 98]]),
   ([4, 6], [4, 6], [[9, 13, 31], [76, 31, 0]]),
   ([4, 6], [5, 6], [[55, 17, 46], [28, 90, 3]]),
   ([5, 6], [4, 5], [[9, 0, 9], [87, 55, 3]]),
   ([5, 6], [4, 6], [[45, 25, 55], [14, 46, 98]]),
   ([5, 6], [5, 6], [[61, 63, 70], [0, 0, 0]])]

def g2 : List Int := [69, 97, 81]

def w2 : List (List Nat × List Nat × List (List Int)) :=
  [([4, 5], [0, 4], [[87, 89, 44], [34, 56, 78]]),
   ([4, 5], [0, 5], [[90, 5, 57], [60, 57, 23]]),
   ([4, 5], [0, 6], [[15, 84, 0], [84, 75, 0]]),
   ([4, 5], [4, 5], [[60, 51, 0], [51, 78, 0]]),
   ([4, 5], [4, 6], [[44, 72, 43], [1, 0, 57]]),
   ([4, 5], [5, 6], [[8, 53, 58], [23, 87, 44]]),
   ([4, 6], [0, 4], [[89, 55, 89], [67, 45, 23]]),
   ([4, 6], [0, 5], [[79, 86, 26], [17, 26, 0]]),
   ([4, 6], [0, 6], [[49, 84, 0], [41, 44, 78]]),
   ([4, 6], [4, 5], [[58, 45, 43], [100, 0, 44]]),
   ([4, 6], [4, 6], [[70, 45, 23], [50, 23, 0]]),
   ([4, 6], [5, 6], [[70, 79, 72], [78, 14, 57]]),
   ([5, 6], [0, 4], [[82, 32, 75], [0, 0, 0]]),
   ([5, 6], [0, 5], [[12, 29, 12], [17, 12, 78]]),
   ([5, 6], [0, 6], [[78, 41, 0], [84, 89, 23]]),
   ([5, 6], [4, 5], [[34, 51, 58], [97, 29, 57]]),
   ([5, 6], [4, 6], [[49, 3, 29], [4, 72, 44]]),
   ([5, 6], [5, 6], [[61, 5, 78], [0, 0, 0]])]

def a2D : List Int := [31, 95, 92, 32, 46, 76, 11]

def invDelta : List Int := [48, 65, 85, 92, 18, 12]

def w3 : List (List Nat × List Nat × List (List Int)) :=
  [([2, 3], [1, 4], [[59, 23, 23, 55, 1, 52], [15, 26, 9, 81, 81, 47]]),
   ([2, 3], [1, 5], [[74, 68, 18, 71, 68, 52], [86, 75, 92, 20, 20, 54]]),
   ([2, 3], [4, 5], [[17, 65, 7, 11, 7, 63], [0, 0, 0, 0, 0, 0]]),
   ([2, 4], [1, 4], [[1, 33, 63, 17, 79, 50], [63, 17, 76, 25, 32, 62]]),
   ([2, 4], [1, 5], [[23, 64, 66, 100, 84, 40], [59, 64, 80, 28, 19, 88]]),
   ([2, 4], [4, 5], [[15, 29, 25, 74, 9, 24], [93, 19, 91, 55, 9, 51]]),
   ([2, 5], [1, 4], [[1, 38, 34, 100, 46, 47], [42, 37, 21, 73, 82, 13]]),
   ([2, 5], [1, 5], [[73, 92, 35, 9, 62, 26], [38, 84, 25, 76, 69, 39]]),
   ([2, 5], [4, 5], [[94, 1, 68, 31, 37, 93], [8, 82, 10, 46, 92, 50]]),
   ([3, 4], [0, 1], [[58, 9, 16, 98, 13, 1], [95, 41, 48, 49, 37, 89]]),
   ([3, 4], [0, 4], [[2, 58, 87, 63, 83, 92], [79, 12, 41, 6, 50, 66]]),
   ([3, 4], [0, 5], [[29, 12, 12, 51, 24, 88], [100, 26, 41, 85, 2, 82]]),
   ([3, 4], [1, 4], [[29, 92, 68, 95, 92, 89], [4, 39, 28, 20, 53, 73]]),
   ([3, 4], [1, 5], [[32, 36, 47, 1, 89, 19], [84, 8, 16, 12, 10, 63]]),
   ([3, 4], [4, 5], [[80, 35, 63, 75, 46, 14], [81, 32, 84, 12, 86, 0]]),
   ([3, 5], [0, 1], [[34, 1, 66, 46, 36, 66], [6, 60, 53, 52, 64, 12]]),
   ([3, 5], [0, 4], [[34, 63, 12, 47, 50, 14], [1, 75, 60, 16, 99, 19]]),
   ([3, 5], [0, 5], [[37, 57, 28, 95, 57, 68], [22, 89, 60, 95, 51, 35]]),
   ([3, 5], [1, 4], [[77, 96, 35, 68, 16, 20], [17, 93, 85, 89, 91, 38]]),
   ([3, 5], [1, 5], [[8, 42, 36, 70, 98, 63], [97, 62, 73, 81, 48, 28]]),
   ([3, 5], [4, 5], [[52, 67, 48, 84, 80, 6], [20, 69, 17, 89, 15, 0]]),
   ([4, 5], [0, 1], [[24, 56, 97, 23, 39, 37], [0, 0, 0, 0, 0, 0]]),
   ([4, 5], [0, 4], [[93, 3, 52, 31, 88, 44], [45, 32, 6, 75, 85, 37]]),
   ([4, 5], [0, 5], [[47, 99, 14, 56, 85, 32], [56, 69, 95, 26, 16, 64]]),
   ([4, 5], [1, 4], [[6, 19, 35, 78, 82, 48], [43, 76, 70, 9, 55, 90]]),
   ([4, 5], [1, 5], [[12, 39, 3, 8, 0, 60], [58, 25, 31, 92, 46, 11]]),
   ([4, 5], [4, 5], [[83, 57, 94, 81, 95, 60], [0, 0, 0, 0, 0, 0]])]

def witCheck (R : Alg (List (List Int))) (cs : List (List (List Int)))
    (ll rr : List Nat) (ws : List (List Nat × List Nat × List (List Int))) : Bool :=
  (ws.map fun (l,r,_) => (l,r)) == assignments ll rr &&
    ws.all (fun (l,r,w) => R.eq (R.m (contact R cs l r) w) R.o)

def fixedClock {α : Type} (R : Alg α) (a b : α) : List α :=
  [a,R.m a (R.c 51),sub R R.o b,sub R R.o (R.m b (R.c 51))]

def checkThree (j : Nat) (g : List Int)
    (ll rr : List Nat) (ws : List (List Nat × List Nat × List (List Int))) : Bool :=
  let b := if j==0 then 100 else if j==1 then 97 else 50
  let clk := fixedClock F 3 b
  let cs := [get F clk 0, get F clk 1, get F clk (if j==2 then 3 else 2)]
  let ms := mm F cs 6
  let fit := (List.range 3).all (fun k =>
    F.eq (F.a (get F ms (k+3))
      (sumA F ((List.range 3).map (fun i => F.m (get F g i) (get F ms (k+i)))))) 0)
  let L := ext F g
  let t := root F g
  let p := L.a t (L.c (get F g 2))
  let q := L.a (L.c (get F g 1)) (L.m t p)
  let g' := [q,p]
  let R := ext L g'
  let u := root L g'
  let tr := liftC L g' t
  let w := R.n (sumA R [R.c (get F g 2),tr,u])
  let clocks := (clk.map R.c) ++ [tr,u,w]
  !(det3 F ms == 0) && fit && witCheck R clocks ll rr ws

def checkFour : Bool :=
  let g := (a2D.take 6).map (F.m 46)
  let L := ext F g
  let clk := fixedClock L (L.c 2) (root F g)
  let ms := mm L clk 5
  let m0 := get L ms 0
  let m1 := get L ms 1
  let m2 := get L ms 2
  let m3 := get L ms 3
  let delta := sub L (L.m m0 m2) (L.m m1 m1)
  let u := L.m invDelta (sub L (L.m m1 m2) (L.m m0 m3))
  let v := L.m invDelta (sub L (L.m m1 m3) (L.m m2 m2))
  let g' := [v,u]
  let R := ext L g'
  let t := root L g'
  let w := R.n (R.a (liftC L g' u) t)
  let interp := (List.range 7).all (fun b =>
    F.eq (eval F a2D b) (det3 F (mm F (fixedClock F 2 b) 5)))
  get F a2D 6 == 11 && interp && L.eq (L.m delta invDelta) L.o &&
    witCheck R ((clk.map (liftC L g')) ++ [t,w]) [2,3,4,5] [0,1,4,5] w3

def checkVerticalCoeffs : Bool := (List.range 7).all (fun a =>
  let z := (Rat.ofInt (Int.ofNat a))
  (det3 Q (mq [z,z/2,1,1] 1))*1408264704000 == eval Q vC z &&
  (det3 Q (mq [z,z/2] (1/2)))*28449792000 == eval Q vL z)

theorem denominatorAndPrime :
    (List.range 10).all (fun i => ((i+2 : Int)*(i+3)*get F invM i) % 101 == 1) = true ∧
    (List.range 99).all (fun i => 101 % (i+2) != 0) = true := by decide +kernel

theorem gramAndContacts : matCheck = true ∧ contactCheck = true := by decide +kernel

theorem verticalFactors :
    checkVerticalCoeffs = true ∧
      List.zipWith F.a (conv bezC vC) (conv bezL vL) = 1 :: List.replicate 11 0 := by
  decide +kernel

-- Closed modular witnesses use Lean's compiled decision procedure to bound
-- verification memory. The same unit identities are replayed independently.
theorem halfHalfWits :
    w0.length = 27 ∧ checkThree 0 g0 [2,4,5,6] [0,4,5,6] w0 = true := by native_decide
theorem plateauHalfWits :
    w1.length = 18 ∧ checkThree 1 g1 [2,4,5,6] [4,5,6] w1 = true := by native_decide
theorem halfPlateauWits :
    w2.length = 18 ∧ checkThree 2 g2 [4,5,6] [0,4,5,6] w2 = true := by native_decide
theorem fourWits :
    w3.length = 27 ∧ checkFour = true := by native_decide

end RKResearch.ERK11LiveTripleEightClockGate
#print axioms RKResearch.ERK11LiveTripleEightClockGate.halfJacobiBezout
#print axioms RKResearch.ERK11LiveTripleEightClockGate.leftCramer
#print axioms RKResearch.ERK11LiveTripleEightClockGate.derivativeContactScale
#print axioms RKResearch.ERK11LiveTripleEightClockGate.primitiveCalibration
#print axioms RKResearch.ERK11LiveTripleEightClockGate.denominatorAndPrime
#print axioms RKResearch.ERK11LiveTripleEightClockGate.gramAndContacts
#print axioms RKResearch.ERK11LiveTripleEightClockGate.verticalFactors
#print axioms RKResearch.ERK11LiveTripleEightClockGate.halfHalfWits
#print axioms RKResearch.ERK11LiveTripleEightClockGate.plateauHalfWits
#print axioms RKResearch.ERK11LiveTripleEightClockGate.halfPlateauWits
#print axioms RKResearch.ERK11LiveTripleEightClockGate.fourWits
