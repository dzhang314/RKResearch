namespace RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod

/-- Each pair gives a prime and ascending coefficients of a nonlinear
factor in the exact invisible-collision determinant/resultant computation. -/
def receipts : List (Int × List Int) := [
  (5, [-509,439,66]),
  (11, [-18065,15553,2370]),
  (5, [271,-3331,11208,-13086,4144,792]),
  (5, [-548357708351,3026802758566,-6467627881667,6474902811628,-2676296514380,-27038596256,199239796800,18375515136]),
  (11, [23,-161,150]),
  (5, [23,-119,102]),
  (7, [-5,81,-492,1306,-1488,600]),
  (11, [-742669,12675362,-81254993,252350764,-426102532,402337120,-200351040,41088000])]

def horner (p x : Int) (a : List Int) : Int :=
  a.foldr (fun c v => (c+x*v)%p) 0

def projectiveRootless (p : Int) (a : List Int) : Bool :=
  decide (a.getLast! % p ≠ 0) &&
  (List.range p.toNat).all (fun x => decide (horner p x a ≠ 0))

theorem all_projective_receipts :
    receipts.all (fun r => projectiveRootless r.1 r.2) = true := by
  decide +kernel

end RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod

#print axioms RKResearch.Certified.ERK10DirtySixthInvisibleCollisionMod.all_projective_receipts
