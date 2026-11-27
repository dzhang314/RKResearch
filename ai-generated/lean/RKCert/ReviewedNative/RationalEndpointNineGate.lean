import Lean

namespace RKResearch.RationalEndpointNineGate

private def denom (k j : Nat) : Nat := (j+k+2)*(j+k+3)
private def rows : List (List Nat) :=
  (List.range 3).map fun k =>
    let ds := (List.range 6).map (denom k)
    let l := ds.foldl Nat.lcm 1
    ds.map (fun d => (l/d)%4)

theorem weighted_rows :
    rows = [[0,2,2,0,0,3],[2,2,0,0,1,3],[2,0,0,1,3,0]] := by decide

private def orderedLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n+1, lo => (List.range (6-lo)).flatMap fun c =>
      let j := lo+c
      (orderedLists n j).map (fun xs => j::xs)

private def multiply (p : List Nat) (j : Nat) : List Nat :=
  let (a,b) := if j < 4 then (j,1) else (1,2*(j-4))
  List.zipWith (fun x y => (a*x+b*y)%4) (p++[0]) (0::p)

private def badReads (ids : List Nat) : Bool :=
  let p := ids.foldl multiply [1]
  rows.all fun row => ((List.zipWith (· * ·) row p).sum % 4) == 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem none_of_252_multisets :
    ((orderedLists 5 0).length, ((orderedLists 5 0).filter badReads).length) =
      (252, 0) := by decide

#print axioms weighted_rows
#print axioms none_of_252_multisets

end RKResearch.RationalEndpointNineGate
