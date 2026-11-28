namespace RKResearch.Certified.ERK10FifteenPureDonorMirrorMod

def horner (p x : Nat) (cs : List Nat) : Nat :=
  cs.foldl (fun a c => (a*x+c)%p) 0

def projectiveNoRoots (p : Nat) (cs : List Nat) : Bool :=
  !(cs[0]! % p == 0) && (List.range p).all (fun x => !(horner p x cs == 0))

theorem same_pair_quintic_mod7 :
    projectiveNoRoots 7 [3,5,4,5,3,5] = true := by
  decide +kernel

theorem cross_pair_degree_twelve_mod19 :
    projectiveNoRoots 19 [16,1,8,2,11,17,6,18,4,2,18,7,8] = true := by
  decide +kernel

def differentPairResidues : List (Nat × List Nat) := [
  (11,[6,4,5,5,9,8,3,9,2,6,5,0,1]),
  (13,[3,8,10,8,10,2,10,12,12,5,6,7,12,2,0,1,8,8,1,8,0,10,2,10,5,11,1]),
  (11,[7,7,6,6,2,8,5,5,0,7,4,8,10,10]),
  (17,[6,1,10,0,10,16,13,12,16,3,8,9,11,7,15,10,2,3,0,5,0,5,12,12,15,9,15]),
  (11,[8,5,2,9,0,3]),
  (13,[5,4,4,4,6,4,8]),
  (19,[16,6,0,14,13,2,1,6,14,12,18,6,9,4,0,0,8,15,18,12,14,12,11,8,13,17,4]),
  (13,[12,9,2,1,7,8,8,7,0,9,11,11,5,5,9,4,3,2,7,12,9,10,12,11,3,3,9]),
  (11,[7,1,0,7,2]),
  (29,[17,5,9,7,23,10,21,16,15,11,28,3,28])
]

theorem different_pair_factors :
    differentPairResidues.all (fun f => projectiveNoRoots f.1 f.2) = true := by
  decide +kernel

end RKResearch.Certified.ERK10FifteenPureDonorMirrorMod

#print axioms RKResearch.Certified.ERK10FifteenPureDonorMirrorMod.same_pair_quintic_mod7
#print axioms RKResearch.Certified.ERK10FifteenPureDonorMirrorMod.cross_pair_degree_twelve_mod19

#print axioms RKResearch.Certified.ERK10FifteenPureDonorMirrorMod.different_pair_factors
