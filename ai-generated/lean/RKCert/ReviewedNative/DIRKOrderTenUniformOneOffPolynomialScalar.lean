module

public import RKCert.ReviewedNative.DIRKOrderTenConstantOneOffScalar

@[expose] public section

/-! # Uniform one-off nonconstant polynomial gates

Finite coefficient arithmetic, over the fixed splitting residue at
419. The companion proof derives the gate polynomials with actual
forward input degree at most four, without a weighted-block census. -/
namespace RKResearch.Certified.Graded.UniformOneOffPolynomialScalar

open ConstantOneOffScalar
def mul3 (a b c : Nat) : Nat := mul (mul a b) c

abbrev Poly := List Nat

def clean (a : Poly) : Poly := (a.reverse.dropWhile (fun k => k == 0)).reverse
def k (a : Nat) : Poly := clean [a%p]
def q : Poly := [0,1]
def c (a : Poly) (n : Nat) : Nat := a[n]?.getD 0

def plus (a b : Poly) : Poly :=
  clean ((List.range (max a.length b.length)).map (fun n => add (c a n) (c b n)))
def neg (a : Poly) : Poly := a.map (sub 0)
def minus (a b : Poly) : Poly := plus a (neg b)
def scale (t : Nat) (a : Poly) : Poly := clean (a.map (mul t))
def shift (n : Nat) (a : Poly) : Poly := if a.isEmpty then [] else List.replicate n 0 ++ a

def times (a b : Poly) : Poly :=
  a.zipIdx.foldl (fun r (v,n) => plus r (shift n (scale v b))) []
def power (a : Poly) : Nat → Poly
  | 0 => [1]
  | n+1 => times a (power a n)
def prod (a : List Poly) : Poly := a.foldl times [1]
def val (a : Poly) (x : Nat) : Nat :=
  a.reverse.foldl (fun n z => add z (mul n x)) 0

def leading (a : Poly) : Nat := a.getLast?.getD 0

def polyDiv : Nat → Poly → Poly → Poly → Poly × Poly
  | 0, a, _, b => (b, a)
  | fuel+1, a, d, b =>
    if a.isEmpty || d.isEmpty || a.length < d.length then (b,a)
    else
      let j := a.length - d.length
      let m := div (leading a) (leading d)
      polyDiv fuel (minus a (shift j (scale m d))) d (plus b (shift j (k m)))

def quot (a b : Poly) : Option Poly :=
  let (d,r) := polyDiv (a.length+1) a b []
  if r.isEmpty && !b.isEmpty && unit (leading b) then some d else none

def coprimeFuel : Nat → Poly → Poly → Bool
  | 0, _, _ => false
  | n+1, a, b =>
    if b.isEmpty then a.length == 1 && unit (leading a)
    else if !(unit (leading b)) then false
    else coprimeFuel n b (polyDiv (a.length+1) a b []).2

def cop (a b : Poly) : Bool := coprimeFuel (a.length+b.length+1) a b

def lin (t : Nat) : Poly := minus q (k t)

def deg (a : Poly) (n : Nat) : Bool := a.length == n+1 && unit (leading a)

/-- Polynomials in X with coefficients that are polynomials in q, low
coefficients first. These are short nodal products, not a general parser. -/
def externalNodal (roots : List Poly) : List Poly :=
  roots.foldl (fun a r => (List.range (a.length+1)).map (fun j =>
    minus (if j=0 then [] else a[j-1]?.getD []) (times r (a[j]?.getD [])))) [[1]]
def integral (a : List Poly) (x : Poly) : Poly :=
  a.zipIdx.foldl (fun r (v,n) => plus r (scale (inv (n+1)) (times v (power x (n+1))))) []
def I (r : List Poly) (x : Poly) : Poly := integral (externalNodal r) x

def QFcoeff (t : Nat) : List Poly :=
  let c3 := sub (mul 42 t) 84
  let c2 := add 56 (mul t c3)
  let c1 := sub (mul t c2) 14
  let c0 := add 1 (mul t c1)
  [k c0,k c1,k c2,k c3,k 42]

def Fpoly (t : Nat) : Poly := (QFcoeff t).map (fun a => c a 0)
def Ctpoly (t : Nat) : Poly := (Fpoly t).drop 1

def tauZeroCase (x : Nat) : Bool :=
  let d := sub 10 (mul 5 x)
  let ξ := div (mul x (sub 5 (mul 3 x))) d
  let test := add (mul (sub 1 (mul 2 ξ)) (jacobi ξ)) (mul (pow ξ 3) (sub 2 ξ))
  let other := fun z => ([k 0,k ξ,k 1,k x].filter (fun a => a != k z))
  unit d && unit ξ && !(fixed.contains ξ) && test != 0 &&
    [ξ,1].all (fun z => unit (c (I (other z) (k x)) 0))

theorem all_zero_shared_root_guards : interior.all tauZeroCase = true := by decide

/-- Constant, known core and head numerators at the receiver x, then
one absent-column primitive pα on the shared label, head 1, and q. -/
structure Data where
  t : Nat
  x : Nat
  C : Poly
  F : Poly
  nt : Poly
  n1 : Poly
  nq : Nat
  pt : Poly
  p1 : Poly
  pq : Poly
  Cp : Poly
  k0 : Nat
  r : Nat
  ft : Nat

def data (t x : Nat) : Data :=
  let z := k 0
  let o := k 1
  let T := k t
  let X := k x
  let xt := I [z,T,o,q] T
  let xo := I [z,T,o,q] o
  let v := scale (inv 60) (plus (minus (k (sub 0 (mul 10 t)))
    (scale (sub 0 (mul 5 (add t 1))) q)) (scale (sub 0 3) (power q 2)))
  ⟨t,x,Ctpoly t,Fpoly t,I [z,q,o,X] X,I [z,T,q,X] X,c (I [z,T,o,X] X) 0,
    xt,xo,times (power q 3) v,v,mul (mul t (sub t 1)) (sub t x),
    c (integral (QFcoeff t) X) 0,val (Fpoly t) t⟩

def dataGuard (d : Data) : Bool :=
  deg d.C 3 && deg d.nt 1 && deg d.n1 1 && deg d.pt 1 &&
    unit d.nq && unit d.r && unit d.k0 && unit (sub 1 d.t) && unit (sub 1 d.x)

def aBefore (v : Data) (y : Nat) : Poly :=
  times (scale (pow y 3) (minus (k y) (scale 2 q))) v.C

def aCore (v : Data) : Bool :=
  let t := v.t
  let K := minus (scale (mul v.r v.k0) (minus (k t) q)) (scale v.ft v.nt)
  let f := minus (times (times (lin t) v.p1) v.F) v.pq
  let raw := minus
    (times v.F (minus (scale (sub 1 t) (prod [K,lin t,v.p1])) (prod [minus (k 1) q,v.pt,v.nt])))
    (scale (sub 1 t) (times K v.pq))
  let s1 := div (sub 0 1) (sub 1 t)
  let beforeT := minus (times v.nt (aBefore v t)) (prod [power q 2,minus (k (mul 2 t)) q,K])
  let before1 := minus (aBefore v 1) (scale s1 (times (power q 2) (minus (k 2) q)))
  let after := plus (scale (mul (pow t 3) (mul (sub t 2) s1)) v.nt) (scale (sub (mul 2 t) 1) K)
  let endBeforeT := minus (scale (mul (pow t 3) (sub t 2)) v.nt)
    (scale (mul (sub (mul 2 t) 1) (sub 1 t)) K)
  let endBeforeQ := plus (times (power q 2) (lin 2))
    (scale (sub 1 t) (times (minus (scale 2 q) (k 1)) v.C))
  let endAfter := minus (prod [power q 2,lin (mul 2 t),K])
    (scale (pow t 3) (prod [minus (scale 2 q) (k t),v.C,v.nt]))
  match quot raw (prod [q,lin t,lin 1]) with
  | none => false
  | some A =>
    deg K 1 && deg A 4 && deg beforeT 5 && deg before1 4 && deg after 1 &&
      cop v.nt v.pt && cop v.pt K && cop v.pt v.n1 && cop v.pt f && cop v.n1 beforeT &&
      cop A beforeT && cop A before1 && cop A after && cop v.n1 A &&
      deg endBeforeT 1 && deg endBeforeQ 4 && deg endAfter 5 &&
      cop A endBeforeT && cop A endBeforeQ && cop A endAfter

def aHead (v : Data) : Bool :=
  let t := v.t
  let x := v.x
  let s1 := div (sub 0 1) (sub 1 t)
  let dc := inv (mul (pow (sub 1 t) 2) (sub 1 x))
  let b := minus (scale dc (prod [v.n1,lin t,lin x])) (scale v.nq v.C)
  let e := plus (times (power q 2) v.Cp) (prod [minus (k t) q,v.p1,v.C])
  match quot b (times (lin 1) (lin x)), quot e (lin 1) with
  | some B2, some E =>
    let rawA := minus (scale (mul (sub 1 t) v.k0) (times E B2)) (prod [v.C,v.nt,v.pt])
    let before1 := plus (scale (mul v.k0 (sub 1 (mul 2 t))) B2)
      (scale (mul3 (pow t 3) (sub 2 t) s1) v.nt)
    let beforeQ := minus
      (scale v.k0 (prod [power q 2,lin (mul 2 t),B2]))
      (scale (pow t 3) (prod [minus (scale 2 q) (k t),v.C,v.nt]))
    let after := minus (scale s1 (times (power q 2) (lin 2)))
      (times (minus (scale 2 q) (k 1)) v.C)
    match quot rawA (lin t) with
    | none => false
    | some A =>
      deg A 4 && deg beforeQ 5 && deg before1 1 && deg after 4 &&
        cop v.nt v.pt && cop v.nt B2 && cop v.pt v.n1 && cop v.pt E && cop v.pt B2 &&
        cop v.n1 v.nt && cop v.n1 beforeQ && cop A beforeQ && cop A before1 && cop A after
  | _, _ => false

def eachCase (t x : Nat) : Bool :=
  if t=x then true else
    let d := data t x
    dataGuard d && aCore d && aHead d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all_fixed_pair_gates :
    interior.all (fun t => interior.all (eachCase t)) = true := by decide

end RKResearch.Certified.Graded.UniformOneOffPolynomialScalar
