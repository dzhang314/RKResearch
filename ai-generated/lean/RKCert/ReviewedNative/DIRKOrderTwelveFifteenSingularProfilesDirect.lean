import Lean

/-! Core proof-producing replay of the fixed Legendre singular-profile
determinants and cubic/quartic gcds over modulus 181. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.SingularProfilesDirect

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000

def p : Nat := 181
def roots : List Nat := [52,81,91,101,130]

def neg (a : Nat) := (p - a % p) % p
def sub (a b : Nat) := (a + neg b) % p
def inv (a : Nat) : Nat := a^(p-2) % p
def trim (a : List Nat) : List Nat := (a.reverse.dropWhile (· == 0)).reverse

def add (a b : List Nat) : List Nat :=
  match a,b with
  | [], ys => ys
  | xs, [] => xs
  | x::xs,y::ys => ((x+y)%p) :: add xs ys

def scale (a : Nat) (f : List Nat) : List Nat := f.map fun z => a*z%p

def mul (a b : List Nat) : List Nat :=
  match a with
  | [] => []
  | x::xs => add (scale x b) (0::mul xs b)

def linComb (ts : List (Nat × List Nat)) : List Nat :=
  trim <| ts.foldl (fun f (a,g) => add f (scale a g)) []

def ev (a : List Nat) (x : Nat) : Nat := a.foldr (fun c t => (c+x*t)%p) 0
def hull (xs : List Nat) : List Nat := xs.foldr (fun x f => mul [neg x,1] f) [1]

def primitive (f : List Nat) : List Nat :=
  0 :: ((List.range f.length).map fun j => f[j]?.getD 0 * inv (j+1) % p)

def integral (f : List Nat) (u : Nat) : Nat := ev (primitive f) u

def quarticProfile (u : Nat) : List Nat :=
  mul (hull [0,u]) [u*u*inv 5 % p, neg u, 1]

def excludeClock (xs : List Nat) (u : Nat) : List Nat := xs.filter (· !=u)

def fourProfileDet (u d : Nat) : Nat :=
  let h := quarticProfile u
  let r := excludeClock (excludeClock roots u) d
  let a := r[0]?.getD 0
  let b := r[1]?.getD 0
  let c := r[2]?.getD 0
  let x := ev h a
  let y := ev h b
  let z := ev h c
  (integral h a*y*z*sub c b + integral h b*x*z*sub a c + integral h c*x*y*sub b a) % p

def get (a : List α) (i : Nat) (fallback : α) : α := a[i]?.getD fallback

def tripleIndices : List (Nat × Nat × Nat) := [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]

def sRemainder : Nat → List Nat → List Nat → List Nat
  | 0, f, _ => f
  | n+1, f, g => if g.isEmpty || f.length < g.length then f else
      let z := f.getLastD 0 * inv (g.getLastD 0) % p
      let gg := List.replicate (f.length-g.length) 0 ++ scale (neg z) g
      sRemainder n (trim (add f gg)) g

def constantGcd : Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | n+1, f, g => if g.isEmpty then f.length == 1 && f.getLastD 0 != 0 else
      constantGcd n g (sRemainder 8 f g)

/-- The same finite pivot certificate simultaneously serves both cubic
denominator profiles. -/
def sixDirtyReceipt (u : Nat) : Bool :=
  let K := excludeClock roots u
  let U := hull K
  let F := K.map fun z => integral (0::U) z
  let E := K.map fun z =>
    let h := mul (hull [0,u]) (hull (excludeClock K z))
    scale (inv (ev h z)) h
  let lambda := E.map fun e => integral e u
  let constant := (List.zipWith (· * ·) lambda F).foldl (· + ·) 0 % p
  let qs := K.map fun z => hull (excludeClock K z)
  let H := linComb (List.zip (List.zipWith (· * ·) lambda F) qs)
  let Ms := (List.zip K F).map fun (z,f) =>
    let Gamma := E.map fun e => integral e z
    let j := linComb (List.zip (List.zipWith (· * ·) Gamma F) qs)
    scale (inv f) (mul [z,neg 1] j)
  F.all (· != 0) && constant != 0 && H.length == 4 && H.getLastD 0 == constant &&
  tripleIndices.all fun (i,j,k) =>
    let a := get K i 0
    let b := get K j 0
    let c := get K k 0
    let G := linComb [(sub c b,get Ms i []),(sub a c,get Ms j []),(sub b a,get Ms k [])]
    G.length == 5 && constantGcd 9 H G

def primitiveRow (u : Nat) : List Nat := (excludeClock roots u).map (fourProfileDet u)

def derivative : List Int := [-42,840,-5040,12600,-13860,5544]
def reducedDerivative : List Nat := derivative.map fun a => (a % Int.ofNat p).toNat

theorem gridReceipt :
    (List.range p).filter (fun x => ev reducedDerivative x == 0) = roots ∧
    (roots.map (fun x => sub 1 x)).reverse = roots ∧
    roots.Nodup ∧ reducedDerivative.getLastD 0 ≠ 0 := by decide_cbv

theorem primeReceipt :
    ((List.range 12).map (·+2)).all (fun d => p%d != 0) = true := by decide

theorem short52 : primitiveRow 52 = [75,28,89,165] := by decide_cbv
theorem short81 : primitiveRow 81 = [178,97,119,95] := by decide_cbv
theorem short91 : primitiveRow 91 = [62,52,163,163] := by decide_cbv
theorem short101 : primitiveRow 101 = [122,40,168,67] := by decide_cbv
theorem short130 : primitiveRow 130 = [36,111,135,116] := by decide_cbv

theorem long52 : sixDirtyReceipt 52 = true := by decide_cbv
theorem long81 : sixDirtyReceipt 81 = true := by decide_cbv
theorem long91 : sixDirtyReceipt 91 = true := by decide_cbv
theorem long101 : sixDirtyReceipt 101 = true := by decide_cbv
theorem long130 : sixDirtyReceipt 130 = true := by decide_cbv

theorem allShort :
    (roots.flatMap primitiveRow).length = 20 ∧
    (roots.flatMap primitiveRow).all (· !=0) = true := by
  simp [roots,List.flatMap_cons,short52,short81,short91,short101,short130]

theorem allLong : roots.all sixDirtyReceipt = true := by
  simp [roots,long52,long81,long91,long101,long130]

#print axioms gridReceipt
#print axioms primeReceipt
#print axioms allShort
#print axioms allLong

end RKResearch.Certified.Graded.OrderTwelveFifteen.SingularProfilesDirect
