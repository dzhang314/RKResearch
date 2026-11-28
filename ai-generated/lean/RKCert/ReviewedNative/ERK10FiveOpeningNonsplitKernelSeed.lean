namespace RKResearch.Certified.ERK10FiveOpeningNonsplitKernelSeed

def denominator : Int := 4032

def A : List (List Int) :=
  [[], [504],[-448,1792],[-315,1512,-189],[-288,1728,1728,-1152]]

def c : List Int := [0,504,1344,1008,2016]

def dot (a b : List Int) : Int :=
  (List.zipWith (· * ·) a b).foldl (· + ·) 0

def mul (x : List Int) : List Int := A.map (fun row => dot row x)

def d : List Int := List.zipWith (fun v s => 2*v - s*s) (mul c) c
def ad : List Int := mul d
def cad : List Int := List.zipWith (· * ·) c ad
def aad : List Int := mul ad

def det3 (x y z : List Int) : Int :=
  x[0]!*(y[1]!*z[2]!-y[2]!*z[1]!) -
  x[1]!*(y[0]!*z[2]!-y[2]!*z[0]!) +
  x[2]!*(y[0]!*z[1]!-y[1]!*z[0]!)

def det4 (x y z w : List Int) : Int :=
  let tail (p : List Int) (i : Nat) := ((List.range 4).filter (fun j => j != i)).map fun j => p[j]!
  x[0]!*det3 (tail y 0) (tail z 0) (tail w 0) -
  x[1]!*det3 (tail y 1) (tail z 1) (tail w 1) +
  x[2]!*det3 (tail y 2) (tail z 2) (tail w 2) -
  x[3]!*det3 (tail y 3) (tail z 3) (tail w 3)

def decoderRows : List (List Int) :=
  [[1,0,0,0,0],[-21,0,-135,128,28],[26,0,162,-160,-28]]

theorem literal_row_clocks : A.map (fun r => r.foldl (·+·) 0) = c := by
  decide +kernel

theorem scaled_pivot :
    det4 (d.drop 1) (ad.drop 1) (cad.drop 1) (aad.drop 1)
      * 541165879296 = -16 * denominator^13 := by
  decide +kernel

theorem decoder_profiles :
    (decoderRows.map (fun r => dot r [1,1,1,1,1])) = [1,0,0] ∧
    (decoderRows.map (fun r => dot r c)) = [0,denominator,0] ∧
    (decoderRows.map (fun r => dot r (c.map (· ^ 2)))) = [0,0,denominator^2] ∧
    (decoderRows.map (fun r => dot r (c.map (· ^ 3)))) = [0,denominator^3/2,0] ∧
    (decoderRows.map (fun r => dot r d)) = [0,0,0] ∧
    (decoderRows.map (fun r => dot r ad)) = [0,0,0] := by
  decide +kernel

end RKResearch.Certified.ERK10FiveOpeningNonsplitKernelSeed

#print axioms RKResearch.Certified.ERK10FiveOpeningNonsplitKernelSeed.literal_row_clocks
#print axioms RKResearch.Certified.ERK10FiveOpeningNonsplitKernelSeed.scaled_pivot
#print axioms RKResearch.Certified.ERK10FiveOpeningNonsplitKernelSeed.decoder_profiles
