namespace RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod

def A (a : Int) : Int := -8694*a^4 + 11340*a^3 - 4536*a^2 + 630*a - 21
def B (a : Int) : Int := 17010*a^5 - 20412*a^4 + 7560*a^3 - 966*a^2 + 25*a
def P (a d : Int) : Int := A a*d^2 + B a*d + 6*a^2

def residues : List Int := (List.range 19).map Int.ofNat

def row0 (a d : Int) : List Int :=
  [1260*a^2*d - 630*a^2 - 1050*a*d + 630*a + 252*d - 168,
   630*a^2*d - 378*a^2 - 630*a*d + 420*a + 168*d - 120,
   378*a^2*d - 252*a^2 - 420*a*d + 300*a + 120*d - 90,
   252*a^2*d - 180*a^2 - 300*a*d + 225*a + 90*d - 70]

def row1 (a d : Int) : List Int :=
  (row0 a d).drop 1 ++ [180*a^2*d - 135*a^2 - 225*a*d + 175*a + 70*d - 56]

def row2 (a d : Int) : List Int :=
  [-6300*a*d + 3150*a + 1470*d - 882,
   -3150*a*d + 1890*a + 882*d - 588,
   -1890*a*d + 1260*a + 588*d - 420,
   -1260*a*d + 900*a + 420*d - 315]

def row3 (a d : Int) : List Int :=
  [3780*a^2*d + 1890*a^2 - 3150*a*d - 630*a + 756*d,
   1890*a^2*d + 1134*a^2 - 1890*a*d - 420*a + 504*d,
   1134*a^2*d + 756*a^2 - 1260*a*d - 300*a + 360*d,
   756*a^2*d + 540*a^2 - 900*a*d - 225*a + 270*d]

structure Candidate where
  a : Int
  d : Int
  useRow3 : Bool
  constant : Int
  linear : Int
  quadratic : Int

def candidates : List Candidate :=
  [⟨0,0,false,3,1,2⟩,⟨1,17,false,7,15,5⟩,⟨4,5,true,18,10,3⟩,
   ⟨4,10,false,14,2,10⟩,⟨5,7,false,7,5,18⟩,⟨5,10,false,10,3,9⟩,
   ⟨10,5,false,18,10,3⟩,⟨10,15,true,8,13,12⟩,⟨11,1,false,8,5,17⟩,
   ⟨11,15,false,6,0,13⟩,⟨12,15,false,6,0,13⟩,⟨12,16,false,18,3,17⟩,
   ⟨14,13,false,14,6,7⟩,⟨14,15,true,0,18,7⟩]

def dot (x y : List Int) : Int :=
  (List.zipWith (· * ·) x y).foldl (· + ·) 0

def det3 (x y z : List Int) : Int :=
  x[0]! * (y[1]! * z[2]! - y[2]! * z[1]!) -
  x[1]! * (y[0]! * z[2]! - y[2]! * z[0]!) +
  x[2]! * (y[0]! * z[1]! - y[1]! * z[0]!)

def square (x : Int) : Bool := residues.any (fun t => t^2 % 19 == x % 19)

def splitMonic (c0 c1 c2 : Int) : Bool :=
  residues.any fun r =>
    ((r^3+c2*r^2+c1*r+c0) % 19 == 0) &&
    square ((c2+r)^2-4*(c1+c2*r+r^2))

def receipt (w : Candidate) : Bool :=
  let s := row0 w.a w.d
  let t := row1 w.a w.d
  let u := row2 w.a w.d
  let v := row3 w.a w.d
  ([s,t,u,v].all fun a => dot a [w.constant,w.linear,w.quadratic,1] % 19 == 0) &&
  !(det3 s t (if w.useRow3 then v else u) % 19 == 0) &&
  !(splitMonic w.constant w.linear w.quadratic)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem affine_residue_pairs :
    (residues.flatMap fun a =>
      (residues.filter fun d => P a d % 19 == 0).map fun d => (a,d)) =
    candidates.map (fun w => (w.a,w.d)) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem affine_rank_three_and_nonsplit :
    candidates.all receipt = true := by
  decide +kernel

theorem no_integral_a_pole_d : residues.all (fun a => !(A a % 19 == 0)) = true := by
  decide +kernel

theorem boundary_nonsplits :
    ((!(splitMonic 13 4 11)) && (!(splitMonic 4 2 8))) = true := by
  decide +kernel

end RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod

#print axioms RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod.affine_residue_pairs
#print axioms RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod.affine_rank_three_and_nonsplit
#print axioms RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod.no_integral_a_pole_d
#print axioms RKResearch.Certified.ERK10FifteenSignedTripleCubicPressureMod.boundary_nonsplits
