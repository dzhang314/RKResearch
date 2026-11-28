import Lean

/-!
Arithmetic for the dormant-middle mask in the ordered four-carrier ERK11
chart. The reproducing Gram and affine clock conditions are checked below.
The degree-preserving characteristic-13 resultant certificate computes both
Bézout determinants from their integer inputs; it is kernel-replayed.
-/
namespace RKResearch.ERK11TerminalMaskGate

def inverseRows : List (List Int) :=
  [[3,-32,108,-144,66],
    [-32,388,-1404,1956,-924],
    [108,-1404,5316,-7644,3696],
    [-144,1956,-7644,11256,-5544],
    [66,-924,3696,-5544,2772]]

def row (i : Nat) : List Int := inverseRows[i]?.getD []

def term (a : List Int) (i : Nat) : Int := a[i]?.getD 0

def gramNumerator (i j : Nat) : Int :=
  ((27720 : Int) / (Int.ofNat (i+j+2) * Int.ofNat (i+j+3)))

/-- Integer-cleared verification of the X(1-X) inverse Gram, scaled by 210. -/
theorem gramInverse : ∀ i j : Fin 5,
    ((List.finRange 5).foldl (fun a r =>
       a+gramNumerator i.val r.val*term (row r.val) j.val) 0) =
       (if i=j then 132 else 0) := by decide

section Fields
open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

def cubic (a b c d t : K) := a+b*t+c*t^2+d*t^3
def response (t : K) := t^2*(1-t)

/-- The same paid left clock calibration as in the tableau argument. -/
theorem normalizedClockFit (a b c d j k : K)
    (distinct1 : j ≠ 1/2) (distinct2 : k ≠ 1/2) (distinct3 : j ≠ k)
    (pair : 6*j*k-7*(j+k)+8=0)
    (h0 : cubic a b c d (1/2) = response (1/2))
    (h1 : cubic a b c d j = response j)
    (h2 : cubic a b c d k = response k) :
    6*b+10*c+13*d = -3 := by
  have hh : 8*a+4*b+2*(c-1)+(d+1)=0 := by
    clear distinct1 distinct2 distinct3 pair h1 h2
    unfold cubic response at h0
    grind
  let v := 4*(d+1)
  let w := 4*(c-1)+2*(d+1)
  let y := 4*b+2*(c-1)+(d+1)
  have factor (t : K) : 8*(cubic a b c d t-response t) =
      (2*t-1)*(v*t^2+w*t+y) := by
    clear distinct1 distinct2 distinct3 pair h0 h1 h2
    unfold cubic response
    dsimp [v,w,y]
    grind
  have hj : v*j^2+w*j+y=0 := by
    have h := factor j
    rw [h1] at h
    clear factor hh h0 h1 h2 distinct2 distinct3 pair
    grind
  have hk : v*k^2+w*k+y=0 := by
    have h := factor k
    rw [h2] at h
    clear factor hh h0 h1 h2 distinct1 distinct3 pair
    grind
  have hw : w + v*(j+k) = 0 := by
    clear hh factor h0 h1 h2 distinct1 distinct2 pair
    have ht : (j-k)*(w+v*(j+k))=0 := by grind
    grind
  have hy : y-v*j*k=0 := by
    clear hh factor h0 h1 h2 distinct1 distinct2 distinct3 hk pair
    have h : w = -v*(j+k) := by grind
    rw [h] at hj
    grind
  clear hh factor h0 h1 h2 distinct1 distinct2 distinct3 hj hk
  have hsum : 6*y+7*w+8*v=0 := calc
    _ = 6*(y-v*j*k)+7*(w+v*(j+k))+v*(6*j*k-7*(j+k)+8) := by
      clear hy hw pair
      grind
    _ = 0 := by rw [hy,hw,pair]; grind
  clear hy hw pair
  dsimp [v,w,y] at hsum
  grind

/-- This is the difference quotient of the degree-four kernel in its first slot. -/
def quotient (u k1 k2 k3 k4 t : K) :=
  cubic (k1+u*k2+u^2*k3+u^3*k4) (k2+u*k3+u^2*k4) (k3+u*k4) k4 t

theorem quotientIdentity (u t k0 k1 k2 k3 k4 : K) :
    (t-u)*quotient u k1 k2 k3 k4 t =
      (k0+k1*t+k2*t^2+k3*t^3+k4*t^4)-
      (k0+k1*u+k2*u^2+k3*u^3+k4*u^4) := by
  unfold quotient cubic
  grind

theorem leftKernelFit (u k1 k2 k3 k4 : K) :
    u*(6*(k2+u*k3+u^2*k4)+10*u*(k3+u*k4)+13*u^2*k4)
      +24*quotient u k1 k2 k3 k4 (u/2) =
          24*k1+42*u*k2+58*u^2*k3+74*u^3*k4 := by
  unfold quotient cubic
  grind

end Fields

/-! Integer polynomials are lists of coefficients in ascending power order. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def add (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map (fun i => term a i + term b i)
def neg (a : List Int) : List Int := a.map (- ·)
def sub (a b : List Int) : List Int := add a (neg b)
def scale (r : Int) (a : List Int) : List Int := a.map (r * ·)
def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)
def clip (a : List Int) : List Int :=
  (a.reverse.dropWhile (· == 0)).reverse
def red (a : List Int) : List Int := a.map (· % 13)

/-- Coefficient of W^j in F0(U,W). -/
def f0 (j : Nat) : List Int := (List.range 5).map (fun i => term (row i) j)
/-- Coefficient of W^j in FL(U,W). -/
def fl (j : Nat) : List Int :=
  [24*term (row 1) j,42*term (row 2) j,58*term (row 3) j,74*term (row 4) j]

def choose4 (i j : Nat) : Int :=
  term ([[1],[1,1],[1,2,1],[1,3,3,1],[1,4,6,4,1]][i]?.getD []) j

/-- Coefficient of W^j in FR(U,W) = -FL(1-U,1-W). -/
def fr (j : Nat) : List Int :=
  neg ((List.range (5-j)).foldl (fun a d =>
    let k := j+d
    add a (scale (((-1:Int)^j)*choose4 k j)
      ((List.range 4).map (fun i =>
         ((-1:Int)^i) * ((List.range (4-i)).foldl
           (fun z e => z+choose4 (i+e) i*term (fl k) (i+e)) 0))))) [])

/-- The coefficient of X^i Y^j in (f(X)g(Y)-g(X)f(Y))/(X-Y). -/
def bezout (f g : Nat → List Int) (i j : Nat) : List Int :=
  let boundary := i+j+1
  (List.range (min i j+1)).foldl (fun p k =>
    let h := boundary-k
    if h < 5 then
      add p (sub (product (f h) (g k)) (product (f k) (g h)))
    else p) []

def det2 (m : Nat → Nat → List Int) (a b c d : Nat) : List Int :=
  sub (product (m a c) (m b d)) (product (m a d) (m b c))
def det3 (m : Nat → Nat → List Int) (i j k : Nat) : List Int :=
  add (sub (product (m 1 i) (det2 m 2 3 j k))
           (product (m 1 j) (det2 m 2 3 i k)))
      (product (m 1 k) (det2 m 2 3 i j))
def det4 (m : Nat → Nat → List Int) : List Int :=
  sub (add (sub (product (m 0 0) (det3 m 1 2 3))
                (product (m 0 1) (det3 m 0 2 3)))
           (product (m 0 2) (det3 m 0 1 3)))
      (product (m 0 3) (det3 m 0 1 2))

def leftResultant : List Int := clip (det4 (bezout f0 fl))
def rightResultant : List Int := clip (det4 (bezout f0 fr))
def leftMod : List Int :=
  [11,8,6,1,11,10,9,9,3,4,8,0,7,1,1,6,5,6,3,2,10,1,4,11,11]
def rightMod : List Int :=
  [5,2,2,11,12,10,10,11,10,10,4,9,7,4,8,0,11,1,7,11,3,6,4,11,11]

theorem leftResultantCertificate : red leftResultant = leftMod := by decide
theorem rightResultantCertificate : red rightResultant = rightMod := by decide

/-- Coprimality in the residue field, with both exact leading coefficients retained. -/
theorem modularBezoutCertificate :
    red (add
      (product [7,4,1,2,11,7,10,11,6,0,4,0,2,8,10,1,10,1,12,0,6,9,4,7] leftMod)
      (product [3,10,9,10,12,0,12,0,2,5,0,2,2,10,1,7,9,11,11,6,9,4,9,6] rightMod)) =
      1::List.replicate 47 0 := by decide

end RKResearch.ERK11TerminalMaskGate
#print axioms RKResearch.ERK11TerminalMaskGate.gramInverse
#print axioms RKResearch.ERK11TerminalMaskGate.normalizedClockFit
#print axioms RKResearch.ERK11TerminalMaskGate.quotientIdentity
#print axioms RKResearch.ERK11TerminalMaskGate.leftKernelFit
#print axioms RKResearch.ERK11TerminalMaskGate.leftResultantCertificate
#print axioms RKResearch.ERK11TerminalMaskGate.rightResultantCertificate
#print axioms RKResearch.ERK11TerminalMaskGate.modularBezoutCertificate
