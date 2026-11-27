import Lean

namespace RKResearch.ERK10ReorderedCoorderMod227

private def subsets : List Int → List (List Int)
  | [] => [[]]
  | a :: as =>
    let S := subsets as
    S ++ S.map (fun s => a :: s)

private def timesLinear (f : List Int) (a : Int) : List Int :=
  List.zipWith (· + ·) ((f.map (fun x => -a * x)) ++ [0]) (0 :: f)

private def hull (xs : List Int) : List Int :=
  xs.foldl timesLinear [0, 1]

private def numerator (r : Int) (f : List Int) : Int :=
  (f.zipIdx.map (fun (c,i) => c * r ^ (i+1) * (60 / (Int.ofNat (i+1))))).sum

private def sites : List Int := [51, 24, 204, 177]
private def supportCases : List (List Int) := (subsets sites).filter (fun S => S.length ≤ 3)

theorem countCases : (sites.length * supportCases.length) = 60 := by decide

/-- 60 times the primitive is nonzero in the splitting-field reduction. -/
theorem allSupportMoments :
    sites.all (fun r =>
      supportCases.all (fun S => !(numerator r (hull S) % 227 == 0))) = true := by decide

end RKResearch.ERK10ReorderedCoorderMod227
