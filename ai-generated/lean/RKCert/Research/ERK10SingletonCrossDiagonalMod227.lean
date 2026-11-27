import Lean

namespace RKResearch.ERK10SingletonCrossDiagonalMod227

private def timesLinear (f : List Int) (a : Int) : List Int :=
  List.zipWith (· + ·) ((f.map (fun x => -a * x)) ++ [0]) (0 :: f)

private def primitive60 (r : Int) (f : List Int) : Int :=
  (f.zipIdx.map (fun (c,i) => c * r ^ (i+1) * (60 / (Int.ofNat (i+1))))).sum

private def data : List (Int × Int) := [(51,128), (24,137), (204,64), (177,67)]

private def clockCardinalNumerator (b : Int) : List Int :=
  ((data.map Prod.fst).filter (· != b)).foldl timesLinear [0, 1]

/-- Ratios of a column's exact primitive to the possible rank-one site error
are distinct at its own row and any other interior row. -/
theorem crossDiagonals :
    data.all (fun (a,na) =>
      data.all (fun (b,nb) =>
        if a == b then true else
        let f := clockCardinalNumerator b
        !((na * primitive60 a f - nb * primitive60 b f) % 227 == 0))) = true := by
  decide

end RKResearch.ERK10SingletonCrossDiagonalMod227
