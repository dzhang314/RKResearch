module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay

@[expose] public section

/-! The Shanks order-eight tableau, with every coefficient scaled by 139482000.
No floating-point computation or field assumption is used. -/

namespace RKResearch.Certified.ERK8ShanksQuadraticCertificate
open RKResearch.Certified.ERKQuadraticIntegerReplay
open FiniteRootedTree
open scoped Matrix

def D : Int := 139482000
def rows : Array (Array Pair) := #[
    #[],
    #[(15498000,0)],
    #[(5811750,0),(17435250,0)],
    #[(8717625,0),(0,0),(26152875,0)],
    #[(8089956,0),(0,0),(9205812,0),(-3347568,0)],
    #[(4735500,0),(0,0),(0,0),(574000,0),(17937500,0)],
    #[(-81364500,0),(0,0),(0,0),(294462000,0),(484312500,0),(-627669000,0)],
    #[(-17220000,0),(0,0),(0,0),(-18368000,0),(71750000,0),(0,0),(56826000,0)],
    #[(505837500,0),(0,0),(0,0),(-1487808000,0),(-2690625000,0),(3626532000,0),(104181000,0),(-11623500,0)],
    #[(126136500,0),(0,0),(0,0),(-366786000,0),(-591937500,0),(790398000,0),(-50799000,0),(69741000,0),(139482000,0)],
    #[(112188300,0),(0,0),(0,0),(-366786000,0),(-591937500,0),(860139000,0),(88683000,0),(0,0),(0,0),(13948200,0)],
    #[(-270742500,0),(0,0),(0,0),(967680000,0),(1535625000,0),(-2082024000,0),(11907000,0),(-22963500,0),(-61236000,0),(-40824000,0),(102060000,0)] ]
def nums : Array Pair := #[(6808050,0),(0,0),(0,0),(0,0),(0,0),(35866800,0),(45165600,0),(4483350,0),(4483350,0),(5977800,0),(29889000,0),(6808050,0)]
def M (i j : Fin 12) : Pair := if j < i then rows[i.val]![j.val]! else pack 0
def w (i : Fin 12) : Pair := nums[i.val]!

set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem pay0 : checkOn 0 D M w 0 = true := by decide +kernel
private theorem pay1 : checkOn 0 D M w 1 = true := by decide +kernel
private theorem pay2 : checkOn 0 D M w 2 = true := by decide +kernel
private theorem pay3 : checkOn 0 D M w 3 = true := by decide +kernel
private theorem pay4 : checkOn 0 D M w 4 = true := by decide +kernel
private theorem pay5 : checkOn 0 D M w 5 = true := by decide +kernel
private theorem pay6 : checkOn 0 D M w 6 = true := by decide +kernel
private theorem pay7 : checkOn 0 D M w 7 = true := by decide +kernel

variable {R : Type*} [CommRing R]

theorem explicit (s d : R) : ERK (tableau s d M) := by
  intro i j hij
  change val s (if j<i then _ else pack 0)*d = 0
  simp [Fin.not_lt.mpr hij, val_pack]

theorem order_eight {s : R} (hs : s*s=(0 : Int)) (d : R) (hd : (D:R)*d=1) :
    HasOrder 8 (tableau s d M) (weights s d w) := by
  apply order_of_check D hs d hd
  intro k hk
  have h8 : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact pay0 | exact pay1 | exact pay2 | exact pay3 | exact pay4 | exact pay5 | exact pay6 | exact pay7

def ninthBush := FiniteRootedTree.leaf.addBush 8
private theorem bushReceipt : mul 0 (pack 4320) (numer 0 M w ninthBush) =
    pack ((4320+1) * (D * scale D ninthBush)) := by decide +kernel

theorem ninth_defect {s : R} (hs : s*s=(0 : Int)) (d : R) (hd : (D:R)*d=1) :
    (4320:R)*((ninthBush.factorial:R)*(weights s d w ⬝ᵥ Φ ninthBush (tableau s d M))-1) = 1 := by
  simpa only [Int.cast_ofNat] using exact_defect D 4320 hs d hd M w ninthBush bushReceipt

theorem not_order_nine [Nontrivial R] {s : R} (hs : s*s=(0 : Int))
    (d : R) (hd : (D:R)*d=1) : ¬ HasOrder 9 (tableau s d M) (weights s d w) := by
  intro h
  have ht : (ninthBush.order : Nat) ≤ 9 := by decide
  simpa only [h ninthBush ht, sub_self, mul_zero, zero_ne_one] using ninth_defect hs d hd

end RKResearch.Certified.ERK8ShanksQuadraticCertificate

#print axioms RKResearch.Certified.ERK8ShanksQuadraticCertificate.order_eight
#print axioms RKResearch.Certified.ERK8ShanksQuadraticCertificate.not_order_nine
