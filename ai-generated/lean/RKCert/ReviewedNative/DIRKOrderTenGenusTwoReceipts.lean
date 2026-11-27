import Init

/-! # Finite receipts for the genus-two rational DIRK10 clock cut

The 22 global square-class generators are represented by bit masks in
each local space. See the exact rational/Python replay for the arithmetic
that produces these columns and the Cantor coordinates. This file checks
the finite linear algebra and local disk scalars in the standard kernel. -/

namespace RKResearch.Certified.DIRKTenGenusTwoReceipts

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- Every mask here has at most 22 bits (the size of the global basis).
private def leadBit (a : Nat) : Nat :=
  (List.range 22).foldl (fun j i => if a.testBit i then i else j) 0

private def reduce (a : Nat) (basis : List Nat) : Nat :=
  basis.foldl (fun acc row => if acc.testBit (leadBit row) then acc ^^^ row else acc) a

private def insertOrdered (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b::bs => if leadBit b < leadBit a then a::b::bs else b::insertOrdered a bs

private def insert (basis : List Nat) (a : Nat) : List Nat :=
  let b := reduce a basis
  if b == 0 then basis else insertOrdered b basis

def echelon (rows : List Nat) : List Nat := rows.foldl insert []

private def columnsToRows (cols : List Nat) : List Nat :=
  (List.range 16).map fun bit =>
    cols.zipIdx.foldl (fun r (col,i) => if col.testBit bit then r + 2^i else r) 0

def normColumns : List Nat := [1, 2, 4, 8, 16, 1, 2, 4, 8, 16, 1, 2, 4, 8, 16, 0, 0, 0, 5, 16, 9, 9]

def localData : List (List Nat × List Nat) := [
  ([27, 10], [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 24, 0, 0, 16, 0, 16, 8]),
  ([1044, 6744, 6874, 2904, 1332], [2, 1, 6, 4, 2, 16, 8, 48, 32, 16, 128, 64, 384, 256, 128, 3072, 3072, 512, 4096, 5120, 1024, 2048]),
  ([201, 228, 210], [2, 2, 1, 2, 0, 8, 8, 4, 8, 0, 32, 32, 16, 32, 0, 128, 0, 128, 192, 128, 128, 128]),
  ([612, 408, 952, 748], [0, 2, 2, 1, 2, 0, 8, 8, 4, 8, 0, 32, 32, 16, 32, 0, 640, 640, 512, 128, 64, 256]),
  ([203, 138, 40], [2, 0, 2, 2, 1, 8, 0, 8, 8, 4, 32, 0, 32, 32, 16, 128, 128, 0, 128, 64, 0, 0])
]

private def localEquations (D : List Nat × List Nat) : List Nat :=
  columnsToRows (D.2.map (fun a => reduce a (echelon D.1)))

private def constraints (k : Nat) : List Nat :=
  columnsToRows normColumns ++ (localData.take k).flatMap localEquations

theorem local_ranks :
    localData.map (fun d => (echelon d.1).length) = [2,5,3,4,3] := by decide

theorem descent_allowed_dimensions :
    (List.range 6).map (fun k => 22 - (echelon (constraints k)).length) =
      [17,15,10,7,4,4] := by decide

private def g121 (coeff : List Nat) (x : Nat) : Nat :=
  coeff.foldr (fun c r => (c+x*r)%121) 0

private def u121 := [97,34,1]
private def v121 := [67,72]

theorem translated_two_supports :
    (List.range 121).filter (fun x => g121 u121 x == 0) = [9,78] ∧
    g121 v121 9 = 110 ∧ g121 v121 78 = 117 := by decide

/-- In order (constant form, x times the form). -/
def logReceipt11 : Nat × Nat :=
  let p := ((78-1)/11)*4       -- inverse of 2*40 modulo 11
  let w := (110/11)*8         -- inverse of f'(9)=2*81*60 modulo 11
  ((p+w)%11,(p+9*w)%11)

theorem logarithm_leading_receipt :
    logReceipt11 = (9,0) ∧ (2*40*4)%11 = 1 ∧ (2*81*60*8)%11 = 1 := by decide

def possibleXs : List Nat :=
  ((List.range 11).filter (fun w => w^4%11==1)).map (fun w => w^2%11)

def possibleYs : List Nat :=
  (List.range 11).filter (fun y => y*y%11 == (20*80)%11)

theorem target_disks : possibleXs = [1,1] ∧ possibleYs = [4,7] := by decide

end RKResearch.Certified.DIRKTenGenusTwoReceipts
