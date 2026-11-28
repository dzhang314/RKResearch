namespace RKResearch.Certified.ERK10FifteenPrimeGeometry

/-! The five signed-pair seed equations, computed in arrays of
integer residues by inspection of the geometric construction. These
certificates do not check literal tree weights or formalize Hensel's lemma. -/

def pmul (modulus : Int) (u v : List Int) : List Int :=
  (List.range (u.length+v.length-1)).map fun j =>
    ((List.range (j+1)).foldl (fun s k => s+u[k]!*v[j-k]!) 0)%modulus

def hull (modulus : Int) (xs : List Int) : List Int :=
  xs.foldl (fun q x => pmul modulus q [-x,1]) [1]

def integral (modulus : Int) (inv : Nat → Int) (f : List Int) : Int :=
  ((List.range f.length).foldl (fun s i => s+f[i]!*inv (i+1)) 0)%modulus

def primitive (modulus : Int) (inv : Nat → Int) (f : List Int) : List Int :=
  0::((List.range f.length).map fun i => (f[i]!*inv (i+1))%modulus)

def value (modulus : Int) (f : List Int) (x : Int) : Int :=
  (f.reverse.foldl (fun a b => (a*x+b)%modulus) 0)

def geometry (modulus : Int) (inv : Nat → Int) (v : List Int) : List Int :=
  let a := v[0]!
  let b := 2*a%modulus
  let c := v[1]!
  let d := v[2]!
  let e := v[3]!
  let f := v[4]!
  let g := v[5]!
  let sites := [0,1,a,b,c,d,e,f,g]
  let μ (x : Int) := integral modulus inv (hull modulus (sites.filter (· != x)))
  let G := hull modulus [0,a,b,c]
  let JG := primitive modulus inv G
  let Q := [0,0,0,b*b*inv 12,(-b)*inv 8,inv 20]
  let E4 := hull modulus [1,e,f,g]
  let E3 := (hull modulus [1,f,g]).map (fun t => -t)
  let Zd := (d-b)*((-a*a*μ a)*d-μ d*d*d*(d-b))
  [integral modulus inv (hull modulus sites), (c*(c-b)*μ c+a*a*μ a)%modulus,
    integral modulus inv (pmul modulus E4 JG), integral modulus inv (pmul modulus E4 Q),
    (Zd*integral modulus inv (pmul modulus E3 JG)+4*μ d*value modulus G d*integral modulus inv (pmul modulus E3 Q))%modulus]

def det : Nat → List (List Int) → Int
  | 0,_ => 1
  | _+1,[] => 0
  | n+1,r::rs =>
    (List.range (n+1)).foldl (fun z j =>
      let sub := rs.map (fun row => row.take j ++ row.drop (j+1))
      z+(if j%2=0 then 1 else -1)*r[j]!*det n sub) 0

def verify (p : Int) (inverses base lift : List Int) (expectedDet : Int) : Bool := Id.run do
  let m := p*p
  let inv := fun i : Nat => inverses[i]!
  let r := geometry m inv base
  let cols := ([0,1,3,4,5] : List Nat).map fun j =>
    let b := (List.range 6).map fun k => base[k]!+(if k=j then p else 0)
    List.zipWith (fun u v => ((u-v)%m)/p) (geometry m inv b) r
  let nodes : List Int := [0,1,base[0]!,2*base[0]!%p,base[1]!,base[2]!,base[3]!,base[4]!,base[5]!]
  return p > 20 && p < 3600 && (List.range 60).all
    (fun k => k < 2 || (k:Int)*(k:Int) > p || p % (k:Int) != 0) &&
    (nodes.eraseDups.length == nodes.length) && (List.range 6).all (fun j => lift[j]!%p == base[j]!) &&
    (List.range 20).all (fun j => (((j+1 : Nat):Int)*inv (j+1))%m == 1) &&
    r.all (fun q => q%p == 0) && geometry m inv lift == [0,0,0,0,0] &&
    expectedDet != 0 && det 5 cols%p == expectedDet

end RKResearch.Certified.ERK10FifteenPrimeGeometry
