module

public import RKCert.ReviewedNative.LobattoDIRK109Deriv9

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix

def derivBucket : ℕ → Array Vec
  | 0 => dBucket0
  | 1 => dBucket1
  | 2 => dBucket2
  | 3 => dBucket3
  | 4 => dBucket4
  | 5 => dBucket5
  | 6 => dBucket6
  | 7 => dBucket7
  | 8 => dBucket8
  | 9 => dBucket9
  | _ => #[]

def deriv (i : Fin Count) : Vec :=
  ((derivBucket (i.val / 20))[i.val % 20]?).getD (fun _ => QExpr.zero)

def prodPacked : List (Fin Count) → Vec
  | [] => fun _ => QExpr.const 1
  | i :: is => point (deriv i) (prodPacked is)

def stage (i : Fin Count) : Vec := prodPacked (keys i).children

theorem prodPacked_val {K : Type*} [CommRing K] {x y : K} (hy : y^2 = 7)
    (is : List (Fin Count)) :
    VecVal x y (prodPacked is) = (is.map (fun i => VecVal x y (deriv i))).prod := by
  induction is with
  | nil =>
    funext i
    exact (QExpr.val_const x y 1).trans Int.cast_one
  | cons i is ih =>
    simp only [prodPacked, point_val hy, ih, List.map_cons, List.prod_cons]

def joinOK (i : Fin Count) : Bool :=
  (List.range (cutoff (9-(keys i).order))).all fun j =>
    decide (keys (joins i (tag j)) = merged (keys i) (keys (tag j)) (tag j))

/-- Each factor has degree at most three. The extra matrix/weight factor
still yields quotient length at most three times the immediate arity.
The decoder need not trust this bound to prove soundness. -/
def digits (i : Fin Count) : ℕ := 3*(keys i).children.length

def derivOK (i : Fin Count) : Bool :=
  QExpr.checkVec innerMod (digits i) (act (stage i)) (deriv i)

def payOK (i : Fin Count) : Bool :=
  QExpr.eqMod innerMod (digits i)
    ((sumWord (stage i)).scale (.atom [((keys i).order*(keys i).forest:ℕ)]))
    (QExpr.const (weightDen*stageDen^((keys i).order-1)))

end RKResearch.Certified.LobattoDIRK109
