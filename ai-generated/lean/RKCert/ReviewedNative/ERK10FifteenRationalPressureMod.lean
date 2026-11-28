namespace RKResearch.Certified.ERK10FifteenRationalPressureMod

def horner (p x : Nat) (cs : List Nat) : Nat :=
  cs.foldl (fun h a => (h*x+a)%p) 0

def projectiveNoRoots (p : Nat) (cs : List Nat) : Bool :=
  !(cs[0]! % p == 0) && (List.range p).all (fun x => !(horner p x cs == 0))

theorem gram_quartic_mod19 :
    projectiveNoRoots 19 [3,15,15,9,3] = true := by
  decide +kernel

theorem zero_first_donor_nonic_mod11 :
    projectiveNoRoots 11 [3,3,9,0,8,5,2,0,1,8] = true := by
  decide +kernel

end RKResearch.Certified.ERK10FifteenRationalPressureMod

#print axioms RKResearch.Certified.ERK10FifteenRationalPressureMod.gram_quartic_mod19
#print axioms RKResearch.Certified.ERK10FifteenRationalPressureMod.zero_first_donor_nonic_mod11
