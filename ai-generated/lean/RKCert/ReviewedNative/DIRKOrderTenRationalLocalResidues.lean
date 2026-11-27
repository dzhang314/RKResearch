import Init

/-! # Exact finite residue gates for rational DIRK10 clocks

No field construction or unproved valuation transport is claimed here.
The integer evaluations and complete residue censuses are standard Lean
kernel reductions, without Mathlib or compiler evaluation. -/

namespace RKResearch.Certified.DIRKTenRationalLocalResidues

def remN (p : Nat) (x : Int) : Nat := (x % (p : Int)).toNat

def ev (p : Nat) (coeff : List Int) (x : Nat) : Nat :=
  remN p (coeff.foldr (fun c a => c + (x : Int)*a) 0)

def roots (p : Nat) (coeff : List Int) : List Nat :=
  (List.range p).filter (fun x => ev p coeff x == 0)

def prime29Char (x : Nat) : Nat := x^7 % 29

def early (s t : Int) : Int :=
  420*s^4-1008*s^3+1008*s^2-504*s+108+
    (-168*s^2+252*s-108)*t+(33-28*s)*t^2-3*t^3

private def ratio29Candidates : List (Nat × Nat) :=
  ((List.range 29).filter (fun r => r != 0 && prime29Char r == 28)).map
    (fun (r : Nat) => let ri : Nat := r^27 % 29; (remN 29 (4-Int.ofNat r-Int.ofNat ri),r))

def negative29 : List (Nat × Nat × Nat) :=
  (List.range 29).flatMap fun s =>
    ratio29Candidates.filterMap fun (t,r) =>
      let d := remN 29 (5*(t : Int)-3)
      let d' := if d == 0 then 16 else d
      if remN 29 (early s t) == 0 && prime29Char d' == prime29Char 27
      then some (s,t,r) else none

theorem neg_case_ledger : negative29 = [(0,6,28),(14,6,28)] := by decide

theorem mod11_origin_two_cut :
    roots 11 [35,-196,336,-180] = [] ∧
    roots 11 [30,-175,308,-168] = [] := by decide

theorem mod29_double_root_reduction :
    roots 29 [112,-39,8] = [10,13] ∧
    roots 29 [25,20,8,19] = [12] ∧
    ev 29 [20,16,57] 12 ≠ 0 ∧
    roots 29 [24,27,27,18] = [6] ∧
    ev 29 [27,54,54] 6 ≠ 0 := by decide

theorem mod29_remaining_suffixes :
    roots 29 [-56,324,-567,308] = [17] ∧
    ev 29 [324,-1134,924] 17 ≠ 0 ∧
    roots 29 [-14,76,-124,63] = [] ∧
    roots 29 [-40,220,-371,196] = [] := by decide

end RKResearch.Certified.DIRKTenRationalLocalResidues
