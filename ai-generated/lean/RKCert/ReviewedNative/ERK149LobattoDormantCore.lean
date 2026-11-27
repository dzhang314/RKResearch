import Std

namespace RKResearch.Certified.ERK149LobattoDormantCore

def p (x : Nat) : Nat :=
  (42*x^4 + 143*x^3 + 56*x^2 + 213*x + 1) % 227

def threeHalves (a t : Nat) : Nat := (2*t + 224*a) % 227

def cubic (a b t : Nat) : Nat :=
  (6*a*b + 223*(a+b)*t + 3*t^2) % 227

def roots : List Nat := (List.range 227).filter (fun x => p x = 0)

theorem roots_exact : roots = [24,51,177,204] := by decide +kernel

theorem no_three_halves :
    (roots.all fun a => roots.all fun t => threeHalves a t != 0) = true := by
  decide +kernel

theorem no_two_donor_cubic :
    (roots.all fun a => roots.all fun b =>
       roots.all fun t => a == b || cubic a b t != 0) = true := by
  decide +kernel

end RKResearch.Certified.ERK149LobattoDormantCore
