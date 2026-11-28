import Lean

/-! Core proof-producing replay of the fixed Legendre singular-profile
determinants and cubic/quartic gcds over modulus 181. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.SingularProfilesArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

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

/-- The integer vectors are the expanded degree-three and degree-four
fixed-node results. The coefficient quotient and primality checks
below are performed by the core kernel. -/
structure PairReceipt where
  primitive : List Nat
  constant : Nat
  cubic : List Nat
  quartics : List (List Nat)

def pass (r : PairReceipt) : Bool :=
  r.primitive.length == 4 && r.primitive.all (· != 0) &&
  r.constant != 0 && r.cubic.length == 4 && r.cubic.getLastD 0 == r.constant &&
  r.quartics.length == 4 &&
  r.quartics.all (fun g => g.length == 5 && g.getLastD 0 != 0 && constantGcd 9 r.cubic g)

def at52 : PairReceipt := ⟨[149, 58, 63, 104], 138, [157, 35, 95, 138], [[159, 149, 161, 76, 29], [164, 29, 134, 134, 175], [110, 70, 4, 149, 45], [105, 9, 31, 91, 80]]⟩
def at81 : PairReceipt := ⟨[50, 105, 177, 171], 136, [2, 38, 126, 136], [[88, 47, 34, 142, 120], [10, 4, 91, 126, 105], [180, 157, 167, 111, 59], [77, 19, 110, 127, 74]]⟩
def at91 : PairReceipt := ⟨[106, 180, 158, 164], 93, [165, 169, 132, 93], [[82, 65, 148, 105, 173], [47, 167, 178, 36, 98], [121, 176, 40, 78, 81], [156, 74, 10, 147, 156]]⟩
def at101 : PairReceipt := ⟨[144, 128, 43, 96], 145, [48, 124, 152, 145], [[96, 4, 15, 124, 51], [142, 37, 12, 6, 93], [120, 39, 7, 74, 94], [74, 6, 10, 11, 52]]⟩
def at130 : PairReceipt := ⟨[111, 61, 118, 27], 164, [114, 59, 85, 164], [[115, 174, 136, 175, 144], [94, 173, 25, 138, 93], [7, 51, 41, 177, 69], [28, 52, 152, 33, 120]]⟩

def receipts : List PairReceipt := [at52,at81,at91,at101,at130]

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

theorem long52 : pass at52 = true := by decide_cbv
theorem long81 : pass at81 = true := by decide_cbv
theorem long91 : pass at91 = true := by decide_cbv
theorem long101 : pass at101 = true := by decide_cbv
theorem long130 : pass at130 = true := by decide_cbv

theorem allShort :
    (roots.flatMap primitiveRow).length = 20 ∧
    (roots.flatMap primitiveRow).all (· !=0) = true := by
  simp [roots,List.flatMap_cons,short52,short81,short91,short101,short130]

theorem allLong : receipts.length = 5 ∧ receipts.all pass = true := by
  simp [receipts,long52,long81,long91,long101,long130]

#print axioms gridReceipt
#print axioms primeReceipt
#print axioms allShort
#print axioms allLong

end RKResearch.Certified.Graded.OrderTwelveFifteen.SingularProfilesArithmetic
