namespace RKResearch.Certified.ERK10ResidueDegreeDensity

/-- Integer count of signed permutations with no usable orbit. Select the
base cycle containing the first index; its signed product is negative or
positive, independently of the signed permutation on the complement. -/
def signedNo (usable : Nat → Bool) : Nat :=
  let counts := (List.range 9).foldl (fun counts n0 =>
    let n := n0 + 1
    let terms := (List.range n).map fun j0 =>
      let j := j0 + 1
      let choices := (List.range j0).foldl (fun v i => v * (n0 - i)) 1
      let signs := (if usable j then 0 else 1) + (if usable (2*j) then 0 else 1)
      choices * 2^j0 * signs * (counts[j0]?.getD 0)
    terms.sum :: counts) [1]
  counts.headD 0

def dihedralNo (usable : Nat → Bool) : Nat :=
  (if usable 1 then 0 else 1) + (if usable 2 then 0 else 5) +
    (if usable 4 then 0 else 2)

def total : Nat := 8 * 2^9 * 362880
def noPlace (usable : Nat → Bool) : Nat := signedNo usable * dihedralNo usable
def minNo (m : Nat) : Nat := noPlace (fun r => decide (r ≤ m))
def availability (k : Nat) : Nat := total - noPlace (fun r => k % r == 0)

/-- The four differences of nested 'no place' counts, in reduced fractional form. -/
theorem leastDegrees :
    (total - minNo 1) * 212336640 = total * 99646543 ∧
    (minNo 1 - minNo 2) * 165150720 = total * 75818719 ∧
    (minNo 2 - minNo 3) * 82944 = total * 913 ∧
    (minNo 3 - minNo 4) * 2903040 = total * 175979 ∧ minNo 4 = 0 := by decide

theorem quadraticAndCubic :
    availability 2 * 1451520 = total * 1347553 ∧
    availability 3 * 23592960 = total * 13001399 := by decide

end RKResearch.Certified.ERK10ResidueDegreeDensity

#print axioms RKResearch.Certified.ERK10ResidueDegreeDensity.leastDegrees
#print axioms RKResearch.Certified.ERK10ResidueDegreeDensity.quadraticAndCubic
