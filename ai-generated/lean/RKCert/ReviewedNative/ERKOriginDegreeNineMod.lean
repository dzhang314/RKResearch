namespace RKResearch.Certified.ERKOriginDegreeNineMod

def rows : List (List Nat) := [
  [210,140,105,84,70,60], [280,210,168,140,120,105],
  [630,504,420,360,315,280], [504,420,360,315,280,252]
]

def coeffs (m : Nat) (factors : List (Nat × Nat)) : List Nat :=
  factors.foldl (fun A r =>
    List.zipWith (fun a b => (a+b)%m)
      ((A.map (fun q => q*(m-r.1%m)%m))++[0])
      (0::(A.map (fun q => q*r.2%m)))) [1]

def satisfies (m : Nat) (factors : List (Nat × Nat)) : Bool :=
  rows.all fun row => decide ((List.zipWith (· * ·) row (coeffs m factors)).foldl (· + ·) 0 % m = 0)

def multisets : Nat → List (Nat × Nat) → List (List (Nat × Nat))
  | 0, _ => [[]]
  | k+1, a => (List.range a.length).flatMap fun i =>
      (multisets k (a.drop i)).map fun w => a[i]! :: w

def mod2Shapes : List (List (Nat × Nat)) :=
  (multisets 5 [(0,1),(1,1),(1,0)]).filter (satisfies 2)

def fourCopies (off : Nat) : List (Nat × Nat) :=
  List.replicate (4-off) (1,0) ++ List.replicate off (1,2)

def mod4Lifts : List (List (Nat × Nat)) :=
  ((List.range 4).flatMap fun a =>
    (List.range 5).map fun off => (a,1) :: fourCopies off) ++
  ((List.range 6).map fun off =>
    List.replicate (5-off) (1,0) ++ List.replicate off (1,2))

theorem mod2_only_three_shapes :
    mod2Shapes = [[(0,1),(1,0),(1,0),(1,0),(1,0)],
                  [(1,1),(1,0),(1,0),(1,0),(1,0)],
                  [(1,0),(1,0),(1,0),(1,0),(1,0)]] := by
  decide +kernel

theorem no_mod4_lifts : mod4Lifts.all (fun t => !satisfies 4 t) = true := by
  decide +kernel

end RKResearch.Certified.ERKOriginDegreeNineMod

#print axioms RKResearch.Certified.ERKOriginDegreeNineMod.mod2_only_three_shapes
#print axioms RKResearch.Certified.ERKOriginDegreeNineMod.no_mod4_lifts
