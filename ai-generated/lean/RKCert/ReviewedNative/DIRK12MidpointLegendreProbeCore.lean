module

public import Init.Data.Rat.Lemmas

@[expose] public section

/-! Exact coefficient and moment tables for the reflected signs of
the three ordinary Legendre derivative tap shapes. -/
namespace RKResearch.Certified.DIRK12MidpointShape

/-- Coefficients of (1−Y) L'_d(1−Y), d=5,6,7. -/
def coef (d : Fin 3) (i : Fin 8) : Int :=
  match d.val with
  | 0 => match i.val with
    | 0 => 30 | 1 => -450 | 2 => 2100 | 3 => -4200 | 4 => 3780 | 5 => -1260 | _ => 0
  | 1 => match i.val with
    | 0 => 42 | 1 => -882 | 2 => 5880 | 3 => -17640 | 4 => 26460 | 5 => -19404
    | 6 => 5544 | _ => 0
  | _ => match i.val with
    | 0 => 56 | 1 => -1568 | 2 => 14112 | 3 => -58800 | 4 => 129360 | 5 => -155232
    | 6 => 96096 | _ => -24024

def add8 (f : Fin 8 → Rat) : Rat := f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7

theorem coef_bound : ∀ d : Fin 3, ∀ i : Fin 8, d.val+5<i.val → coef d i=0 := by
  decide +kernel

theorem reflected_integrals : ∀ d : Fin 3, ∀ k : Fin 7, k.val<d.val+5 →
    add8 (fun i => (coef d i : Rat)/((k.val+i.val+1 : Nat):Rat)) =
      if k=0 then 1 else 0 := by
  decide +kernel

end RKResearch.Certified.DIRK12MidpointShape

#print axioms RKResearch.Certified.DIRK12MidpointShape.coef_bound
#print axioms RKResearch.Certified.DIRK12MidpointShape.reflected_integrals
