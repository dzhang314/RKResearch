namespace RKResearch.Certified.ERK10ThreeWitnessDensity

/-- Count signed permutations on n labels with no usable orbit, peeling
off the cycle containing the first base label. -/
def signedNo (n : Nat) (usable : Nat → Bool) : Nat :=
  let counts := (List.range n).foldl (fun counts n0 =>
    let terms := (List.range (n0 + 1)).map fun j0 =>
      let j := j0 + 1
      let choices := (List.range j0).foldl (fun v i => v * (n0 - i)) 1
      let signs := (if usable j then 0 else 1) + (if usable (2*j) then 0 else 1)
      choices * 2^j0 * signs * (counts[j0]?.getD 0)
    terms.sum :: counts) [1]
  counts.headD 0

def dihedralNo (usable : Nat → Bool) : Nat :=
  (if usable 1 then 0 else 1) + (if usable 2 then 0 else 5) +
    (if usable 4 then 0 else 2)

def total : Nat := 8 * 2^19 * 362880 * 3628800
def noPlace (usable : Nat → Bool) : Nat :=
  signedNo 9 usable * signedNo 10 usable * dihedralNo usable
def minNo (m : Nat) : Nat := noPlace (fun r => decide (r ≤ m))
def availability (k : Nat) : Nat := total - noPlace (fun r => k % r == 0)

theorem specifiedDegreeCounts :
    availability 1 * 789019852013568000 = total * 535038692663489723 ∧
    availability 2 * 2080899072000 = total * 2038195978321 ∧
    availability 3 * 1391569403904000 = total * 1070788017536573 ∧
    availability 4 = total := by decide

theorem leastDegreeCounts :
    (total - minNo 1) * 789019852013568000 = total * 535038692663489723 ∧
    (minNo 1 - minNo 2) * 5523138964094976000 = total * 1664525222582996707 ∧
    (minNo 2 - minNo 3) * 832359628800 = total * 4838132071 ∧
    (minNo 3 - minNo 4) * 4161798144000 = total * 61215527003 ∧
    minNo 4 = 0 := by decide

/-- For each nonempty character selection there is a receipt row with
odd pairing. Bits from left to right represent the six columns in the
arithmetic proof. -/
def oddPairing (row mask : Nat) : Bool :=
  ((List.range 6).filter (fun j => row.testBit j && mask.testBit j)).length % 2 == 1

def detectsEveryNonzeroCharacter : Bool :=
  (List.range 63).all fun i =>
    ([26,49,42,63,19,12] : List Nat).any fun row => oddPairing row (i+1)

theorem characterRowsHaveZeroKernel : detectsEveryNonzeroCharacter = true := by decide

end RKResearch.Certified.ERK10ThreeWitnessDensity

#print axioms RKResearch.Certified.ERK10ThreeWitnessDensity.specifiedDegreeCounts
#print axioms RKResearch.Certified.ERK10ThreeWitnessDensity.leastDegreeCounts
#print axioms RKResearch.Certified.ERK10ThreeWitnessDensity.characterRowsHaveZeroKernel
