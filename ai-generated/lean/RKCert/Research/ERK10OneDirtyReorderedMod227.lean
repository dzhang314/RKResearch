import Lean

namespace RKResearch.ERK10OneDirtyReorderedMod227

private def sites : List Int := [51,24,204,177]

private def ev (x : Int) : List Int := [x, x^2, x^3, x^4]
private def primitive60 (x : Int) : List Int := [30*x^2, 20*x^3, 15*x^4, 12*x^5]

private def eraseAt : Nat → List Int → List Int
  | _, [] => []
  | 0, _ :: t => t
  | n+1, a :: t => a :: eraseAt n t

private def determinant : Nat → List (List Int) → Int
  | 0, _ => 1
  | Nat.succ _, [] => 0
  | n+1, h :: t =>
    (h.zipIdx.map (fun (a,i) =>
      (if i % 2 = 0 then a else -a) * determinant n (t.map (eraseAt i)))).sum

private def subsets : List Int → List (List Int)
  | [] => [[]]
  | a :: as => let s := subsets as; s ++ s.map (fun x => a :: x)

private def productLinear (f : List Int) (a : Int) : List Int :=
  List.zipWith (· + ·) (f.map (fun k => -a*k) ++ [0]) (0 :: f)

private def upperPrimitive60 (a : Int) (f : List Int) : Int :=
  (f.zipIdx.map (fun (c,i) =>
    c * (1 - a^(i+1)) * (60/(Int.ofNat (i+1))))).sum

/-- Determinants of two primitive and two chronological evaluation rows. -/
theorem allPred :
    sites.all (fun a => sites.all (fun b => sites.all (fun c =>
      if a == b || a == c || b == c then true else
      !(determinant 4 [primitive60 a, ev a, ev b, primitive60 c] % 227 == 0)))) = true := by
  decide

/-- No upper-interval support consisting of the endpoint and at most two other
interior Lobatto knots integrates its own vanishing hull. -/
theorem allSucc :
    sites.all (fun a =>
      (((subsets (sites.filter (· != a))).filter (fun s => s.length ≤ 2))).all
       (fun s => !((upperPrimitive60 a (s.foldl productLinear [-1,1])) % 227 == 0))) = true := by
  decide

end RKResearch.ERK10OneDirtyReorderedMod227
