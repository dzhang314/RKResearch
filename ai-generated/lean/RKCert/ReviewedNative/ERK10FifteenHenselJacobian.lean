namespace RKResearch.Certified.ERK10FifteenHenselJacobian

/-! The finite-difference calculation of the actual five polynomial
geometry equations modulo 17^2. This does not formalize Hensel recursion. -/

def modulus : Int := 289

def inverses : List Int :=
  [0,1,145,193,217,58,241,124,253,257,29,184,265,89,62,212,271,0,273,213,159]

def inv (i : Nat) : Int := inverses[i]!

def pmul (u v : List Int) : List Int :=
  (List.range (u.length+v.length-1)).map fun j =>
    ((List.range (j+1)).foldl (fun s k => s+u[k]!*v[j-k]!) 0)%modulus

def hull (xs : List Int) : List Int :=
  xs.foldl (fun q x => pmul q [-x,1]) [1]

def integral (f : List Int) : Int :=
  ((List.range f.length).foldl (fun s i => s+f[i]!*inv (i+1)) 0)%modulus

def primitive (f : List Int) : List Int :=
  0::((List.range f.length).map fun i => (f[i]!*inv (i+1))%modulus)

def value (f : List Int) (x : Int) : Int :=
  (f.reverse.foldl (fun a b => (a*x+b)%modulus) 0)

def geometry (v : List Int) : List Int :=
  let a := v[0]!
  let b := 2*a
  let c := v[1]!
  let d := v[2]!
  let e := v[3]!
  let f := v[4]!
  let g := v[5]!
  let sites := [0,1,a,b,c,d,e,f,g]
  let μ (x : Int) := integral (hull (sites.filter (· != x)))
  let G := hull [0,a,b,c]
  let JG := primitive G
  let Q := [0,0,0,b*b*inv 12,(-b)*inv 8,inv 20]
  let E4 := hull [1,e,f,g]
  let E3 := (hull [1,f,g]).map (fun t => -t)
  let Zd := (d-b)*((-a*a*μ a)*d-μ d*d*d*(d-b))
  [integral (hull sites), (c*(c-b)*μ c+a*a*μ a)%modulus,
    integral (pmul E4 JG), integral (pmul E4 Q),
    (Zd*integral (pmul E3 JG)+4*μ d*value G d*integral (pmul E3 Q))%modulus]

def base : List Int := [16,2,8,9,4,6]

def displaced (j : Nat) : List Int :=
  (List.range 6).map fun k => base[k]!+(if k=j then 17 else 0)

def jacobianColumn (j : Nat) : List Int :=
  List.zipWith (fun u v => ((u-v)%modulus)/17) (geometry (displaced j)) (geometry base)

def det : Nat → List (List Int) → Int
  | 0,_ => 1
  | _+1,[] => 0
  | n+1,r::rs =>
    (List.range (n+1)).foldl (fun z j =>
      let sub := rs.map (fun row => row.take j ++ row.drop (j+1))
      z+(if j%2=0 then 1 else -1)*r[j]!*det n sub) 0

theorem paid_inverse_table :
  ([1,2,3,4,5,6,7,8,9,10,12,20] : List Nat).all
    (fun i => ((i:Int)*inv i)%modulus == 1) = true := by
  decide +kernel

theorem base_residual : geometry base = [0,136,187,102,272] := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geometry_jacobian :
    (List.range 6).map jacobianColumn =
      [[14,2,6,0,1],[1,14,0,0,1],[12,15,0,0,12],
       [14,2,3,0,2],[13,8,14,6,15],[15,7,4,10,13]] := by
  decide +kernel

theorem jacobian_minor_unit :
    det 5 [[14,2,6,0,1],[1,14,0,0,1],[14,2,3,0,2],[13,8,14,6,15],[15,7,4,10,13]]
      % 17 = 10 := by
  decide +kernel

end RKResearch.Certified.ERK10FifteenHenselJacobian

#print axioms RKResearch.Certified.ERK10FifteenHenselJacobian.base_residual
#print axioms RKResearch.Certified.ERK10FifteenHenselJacobian.geometry_jacobian
#print axioms RKResearch.Certified.ERK10FifteenHenselJacobian.jacobian_minor_unit
