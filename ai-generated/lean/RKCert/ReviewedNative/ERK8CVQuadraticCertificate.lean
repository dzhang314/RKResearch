module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay

@[expose] public section

/-! The CV order-eight tableau, with every coefficient scaled by 282240.
No floating-point computation or field assumption is used. -/

namespace RKResearch.Certified.ERK8CVQuadraticCertificate
open RKResearch.Certified.ERKQuadraticIntegerReplay
open FiniteRootedTree
open scoped Matrix

def D : Int := 282240
def rows : Array (Array Pair) := #[
    #[],
    #[(141120,0)],
    #[(70560,0),(70560,0)],
    #[(40320,0),(-20160,8640),(120960,-28800)],
    #[(36960,-3360),(0,0),(80640,-17920),(23520,1120)],
    #[(29400,-5880),(0,0),(70560,-7840),(-181104,-10976),(222264,24696)],
    #[(67200,6720),(0,0),(-387072,-82432),(1985088,454720),(-2032128,-463680),(508032,104832)],
    #[(20160,0),(0,0),(0,0),(0,0),(31360,6720),(58240,13440),(31360,0)],
    #[(8820,0),(0,0),(0,0),(0,0),(44590,10290),(43120,0),(-94325,18375),(138915,-28665)],
    #[(20160,0),(0,0),(0,0),(0,0),(31360,0),(-93824,18816),(288400,-62160),(-257040,55440),(152064,-32256)],
    #[(0,0),(0,0),(0,0),(0,0),(-658560,-109760),(-112896,-175616),(-1070160,207760),(1179920,-207760),(175616,175616),(768320,109760)] ]
def nums : Array Pair := #[(14112,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(76832,0),(100352,0),(76832,0),(14112,0)]
def M (i j : Fin 11) : Pair := if j < i then rows[i.val]![j.val]! else pack 0
def w (i : Fin 11) : Pair := nums[i.val]!

set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem pay0 : checkOn 21 D M w 0 = true := by decide +kernel
private theorem pay1 : checkOn 21 D M w 1 = true := by decide +kernel
private theorem pay2 : checkOn 21 D M w 2 = true := by decide +kernel
private theorem pay3 : checkOn 21 D M w 3 = true := by decide +kernel
private theorem pay4 : checkOn 21 D M w 4 = true := by decide +kernel
private theorem pay5 : checkOn 21 D M w 5 = true := by decide +kernel
private theorem pay6 : checkOn 21 D M w 6 = true := by decide +kernel
private theorem pay7 : checkOn 21 D M w 7 = true := by decide +kernel

variable {R : Type*} [CommRing R]

theorem explicit (s d : R) : ERK (tableau s d M) := by
  intro i j hij
  change val s (if j<i then _ else pack 0)*d = 0
  simp [Fin.not_lt.mpr hij, val_pack]

theorem order_eight {s : R} (hs : s*s=(21 : Int)) (d : R) (hd : (D:R)*d=1) :
    HasOrder 8 (tableau s d M) (weights s d w) := by
  apply order_of_check D hs d hd
  intro k hk
  have h8 : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact pay0 | exact pay1 | exact pay2 | exact pay3 | exact pay4 | exact pay5 | exact pay6 | exact pay7

def ninthBush := FiniteRootedTree.leaf.addBush 8
private theorem bushReceipt : mul 21 (pack 3920) (numer 21 M w ninthBush) =
    pack ((3920+1) * (D * scale D ninthBush)) := by decide +kernel

theorem ninth_defect {s : R} (hs : s*s=(21 : Int)) (d : R) (hd : (D:R)*d=1) :
    (3920:R)*((ninthBush.factorial:R)*(weights s d w ⬝ᵥ Φ ninthBush (tableau s d M))-1) = 1 := by
  simpa only [Int.cast_ofNat] using exact_defect D 3920 hs d hd M w ninthBush bushReceipt

theorem not_order_nine [Nontrivial R] {s : R} (hs : s*s=(21 : Int))
    (d : R) (hd : (D:R)*d=1) : ¬ HasOrder 9 (tableau s d M) (weights s d w) := by
  intro h
  have ht : (ninthBush.order : Nat) ≤ 9 := by decide
  simpa only [h ninthBush ht, sub_self, mul_zero, zero_ne_one] using ninth_defect hs d hd

end RKResearch.Certified.ERK8CVQuadraticCertificate

#print axioms RKResearch.Certified.ERK8CVQuadraticCertificate.order_eight
#print axioms RKResearch.Certified.ERK8CVQuadraticCertificate.not_order_nine
