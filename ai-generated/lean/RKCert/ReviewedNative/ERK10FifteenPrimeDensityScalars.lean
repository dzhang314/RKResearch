namespace RKResearch.Certified.ERK10FifteenPrimeDensityScalars

/-! Literal arithmetic for the two fixed ERK10 coefficient fields. The
Galois group, Chebotarev argument, and transfer are proved separately. -/

def nonic : List Int :=
  [5376000,-10590720,9105600,-4477616,1385568,-279450,36720,-3036,144,-3]
def gram : List Int := [896,-840,300,-48,3]
def numeratorM : List Int := [5600,-5400,1984,-327,21]
def numeratorN : List Int := [1600,-1600,611,-105,7]

def mul (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map fun j =>
    (List.range (j+1)).foldl (fun v k => v+a[k]!*b[j-k]!) 0

def T : List Int :=
  List.zipWith (fun a b => a-20*b) (mul numeratorM numeratorM) (mul gram numeratorN)

theorem tailDiscriminant :
    T.reverse = [21,-714,10797,-94176,515616,-1807200,3951680,-4928000,2688000] := by
  decide +kernel

def sylvester (f g : List Int) : Array (Array Int) :=
  let nf := f.length-1
  let ng := g.length-1
  ((List.range (nf+ng)).map fun i =>
    let (h,k) := if i<ng then (f,i) else (g,i-ng)
    ((List.range (nf+ng)).map fun j =>
      if j<k then 0 else h[j-k]!).toArray).toArray

/-- Bareiss elimination with a checked exact quotient at each step. -/
def bareiss (input : Array (Array Int)) : Option Int := Id.run do
  let n := input.size
  let mut a := input
  let mut prev : Int := 1
  let mut sign : Int := 1
  for k in List.range (n-1) do
    let hit := (List.range (n-k)).find? fun t => a[k+t]![k]! != 0
    let some delta := hit | return some 0
    if delta != 0 then
      let save := a[k]!
      a := (a.set! k a[k+delta]!).set! (k+delta) save
      sign := -sign
    let pivot := a[k]![k]!
    for i in List.range (n-k-1) do
      let i := k+1+i
      let old := a[i]!
      let mut row := old
      for j in List.range (n-k-1) do
        let j := k+1+j
        let num := pivot*old[j]! - old[k]!*a[k]![j]!
        if num%prev != 0 then return none
        row := row.set! j (num/prev)
      a := a.set! i (row.set! k 0)
    prev := pivot
  return some (sign*a[n-1]![n-1]!)

def derivative (f : List Int) : List Int :=
  (List.range (f.length-1)).map fun j => ((f.length-1-j : Nat) : Int)*f[j]!

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem resultantReceipt :
    bareiss (sylvester nonic T) = some 195940905549539664747294418998325590097920000000 := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem derivativeResultantReceipt :
    bareiss (sylvester nonic (derivative nonic)) =
      some (-18265097881475268102630310354125563743835258880000 * 5376000) := by
  decide +kernel

theorem resultantValuation223 :
    let r : Int := 195940905549539664747294418998325590097920000000
    r % 223 = 0 ∧ r % (223^2) ≠ 0 := by decide +kernel

theorem discriminantValuations :
    let d : Int := -18265097881475268102630310354125563743835258880000
    d % (13^3)=0 ∧ d % (13^4)≠0 ∧ d % 223≠0 := by decide +kernel


def normalize (p : Int) (a : List Int) : List Int :=
  ((a.map (· % p)).reverse.dropWhile (· == 0)).reverse

def add (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map fun i => a[i]!+b[i]!

def F31_2 : List Int := [4,8,1]
def F31_7 : List Int := [26,2,29,25,22,1,17,1]

theorem factorization31 :
    normalize 31 (nonic.reverse.map (17 * ·)) = normalize 31 (mul F31_2 F31_7) := by
  decide +kernel

def value (p : Int) (a : List Int) (x : Int) : Int :=
  a.reverse.foldl (fun v c => (v*x+c)%p) 0

theorem noLinearFactors31 :
    (List.range 31).all
      (fun i => (value 31 F31_2 i != 0) && (value 31 F31_7 i != 0)) = true := by
  decide +kernel

def stepX (p : Int) (f a : List Int) : List Int :=
  let last := a[f.length-2]!
  (List.range (f.length-1)).map fun i =>
    ((if i=0 then (0 : Int) else a[i-1]!) - last*f[i]!)%p

def mulMod (p : Int) (f a b : List Int) : List Int :=
  a.reverse.foldl (fun acc c =>
      List.zipWith (fun x y => (x+c*y)%p) (stepX p f acc) b)
    (List.replicate (f.length-1) 0)

def powMod (p : Int) (f : List Int) : Nat → List Int → List Int
  | 0, _ => 1 :: List.replicate (f.length-2) 0
  | n+1, a => mulMod p f a (powMod p f n a)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem frobenius31DegreeSeven :
    (List.range 7).foldl (fun a _ => powMod 31 F31_7 31 a) [0,1,0,0,0,0,0]
      = [0,1,0,0,0,0,0] := by decide +kernel

def Nq223 : List Int := [36, 42, 141, 139, 33, 14, 156, 212, 139]
def Tq223 : List Int := [194, 192, 73, 155, 42, 154, 185, 181]
def U223 : List Int := [111, 109, 112, 157, 25, 159, 60]
def V223 : List Int := [107, 174, 51, 206, 38, 14, 189, 103]

theorem divisor223 :
    normalize 223 nonic.reverse = normalize 223 (mul [130,1] Nq223) ∧
    normalize 223 T.reverse = normalize 223 (mul [130,1] Tq223) := by
  decide +kernel

theorem quotientBezout223 :
    normalize 223 (add (mul U223 Nq223) (mul V223 Tq223)) = [1] := by
  decide +kernel

end RKResearch.Certified.ERK10FifteenPrimeDensityScalars
#print axioms RKResearch.Certified.ERK10FifteenPrimeDensityScalars.resultantReceipt
#print axioms RKResearch.Certified.ERK10FifteenPrimeDensityScalars.derivativeResultantReceipt
#print axioms RKResearch.Certified.ERK10FifteenPrimeDensityScalars.factorization31
#print axioms RKResearch.Certified.ERK10FifteenPrimeDensityScalars.frobenius31DegreeSeven
#print axioms RKResearch.Certified.ERK10FifteenPrimeDensityScalars.quotientBezout223
