module

@[expose] public section

/-! Exact coefficient-domain arithmetic for the two rational DIRK10 tableaux.
This file imports only Lean's default prelude. -/

namespace RKResearch.Certified.DIRK10RationalPortfolio.Arithmetic

def D₁ : Nat := 101588047290852467338246934187117072000
def D₂ : Nat := 27200218281512417863777752865356303988517513768290967792990592000

theorem denomCover : Nat.gcd D₁ (19891 * D₂) = 27216000 := by decide +kernel
theorem coverSmooth : (27216000 : Nat) = 2^7 * 3^5 * 5^3 * 7 := by decide +kernel

theorem coverBezout :
    1761374130916471727129987906589657431558423718257995510158477 * (D₁ : Int) +
      (-330723624932663944996782097049) * ((D₂ : Int) * 19891) = 27216000 := by
  decide +kernel

theorem coverDivFactorialSquared :
    (27216000 : Int) * 483840 = 3628800^2 := by decide +kernel

theorem starBaseDivisor : (D₁^2) % 2488320 = 0 := by decide +kernel
theorem starAlternateDivisor : (D₂^2) % 520224768 = 0 := by decide +kernel
theorem mixedAlternateDivisor : (D₂^2) % 247726080 = 0 := by decide +kernel
theorem nextBezout : (-907 : Int) * 19891 + (-5546)*(-3253) = 1 := by decide +kernel

def exceptional : List (Nat × Nat × Nat) :=
  [(11,6,10), (17,14,16), (19,18,2), (151,115,34), (173,114,125), (607,600,478),
    (653,191,92), (1063,863,1029), (1499,360,1008), (1553,256,341)]

theorem primeReceipts :
    exceptional.all (fun (p,d,b) =>
      decide (D₂%p=d ∧ D₁%p=0 ∧ d≠0 ∧ b≠0 ∧
        (b*520224768)%p=19891%p)) = true := by decide +kernel

#print axioms denomCover
#print axioms coverBezout
#print axioms nextBezout
#print axioms primeReceipts

end RKResearch.Certified.DIRK10RationalPortfolio.Arithmetic
