import RKCert.ReviewedNative.DIRKOrderTwelveFifteenNineSiteNonrootZeroCore
open RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteNonrootZeroCore

example : f132.length = 133 ∧ factor37.map (fun p => p.length-1) = [1,1,9,20,49,52] :=
  regularDegrees
example : f132.getLast? = some 1 ∧ eval37 f132 36 = 0 ∧ eval37 f132 24 = 0 :=
  unitLeadingAndLinear
example : (List.range 73).filter (fun a => d3 (Int.ofNat a) % 73 == 0) =
    [18,40,65] := cubicResidues
example : (List.range 37).filter (fun a => t4 (Int.ofNat a) % 37 == 0) =
    [6,8,30,32] := quarticResidues
example :
    ([18,40,65] : List Int).all (fun a => 792*t4 a % 73 != 0) = true ∧
    ([6,8,30,32] : List Int).all (fun a => k3 a % 37 != 0) = true :=
  singularLeading
