module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay

@[expose] public section

/-! # A universal nine-stage explicit order-seven tableau

Each coefficient is the displayed signed integer divided by the one
common denominator `D`, which divides `(7!)^6`. The repeated
stage clock 1/3 occurs at both stage 3 and stage 7; these are literal
distinct chronological stages. No field or ordering is assumed.
-/

namespace RKResearch.Certified.ERK7FactorialNine

open ERKQuadraticIntegerReplay FiniteRootedTree
open scoped Matrix

def D : Int := 11435482800

def rows : Array (Array Int) := #[
  #[],
  #[1905913800],
  #[0,3811827600],
  #[1429435350,0,4288306050],
  #[1429435350,0,2144153025,-714717675],
  #[731870899200,0,5420418847200,-1006322486400,-5123096294400],
  #[1776499900,0,5505973200,-1317668800,-2151296000,-1680700],
  #[1608261480,0,3800714400,-1019511360,-1022077440,-903960,-99202320],
  #[14853421548,0,29732255280,88163337024,-1068299172864,-7865676,-1086828285312,2033821792800] ]

def nums : Array Int := #[2001209490,0,0,27783987840,-167284776960,-1512630,-208411674030,355918813740,1429435350]

def M (i j : Fin 9) : Pair := if j < i then pack rows[i.val]![j.val]! else pack 0
def w (i : Fin 9) : Pair := pack nums[i.val]!

set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem pay0 : checkOn 0 D M w 0 = true := by decide +kernel
private theorem pay1 : checkOn 0 D M w 1 = true := by decide +kernel
private theorem pay2 : checkOn 0 D M w 2 = true := by decide +kernel
private theorem pay3 : checkOn 0 D M w 3 = true := by decide +kernel
private theorem pay4 : checkOn 0 D M w 4 = true := by decide +kernel
private theorem pay5 : checkOn 0 D M w 5 = true := by decide +kernel
private theorem pay6 : checkOn 0 D M w 6 = true := by decide +kernel

variable {R : Type*} [CommRing R]

def A (d : R) : Matrix (Fin 9) (Fin 9) R := tableau 0 d M
def b (d : R) : Fin 9 → R := weights 0 d w

theorem explicit (d : R) : ERK (A d) := by
  intro i j hij
  change val (0:R) (if j<i then _ else pack 0)*d = 0
  simp [Fin.not_lt.mpr hij, val_pack]

theorem order_seven (d : R) (hd : (D:R)*d=1) : HasOrder 7 (A d) (b d) := by
  apply order_of_check D (s:=0) (δ:=0) (by simp) d hd
  intro k hk
  have h7 : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact pay0 | exact pay1 | exact pay2 | exact pay3 | exact pay4 | exact pay5 | exact pay6

/-- The eight-vertex tree consisting of a six-vertex bush with two
successive unary grafts above it. Its cleared defect is 1/12. -/
def nextTree : FiniteRootedTree :=
  .butcherProduct .leaf (.butcherProduct .leaf (FiniteRootedTree.leaf.addBush 5))

private theorem nextReceipt : mul 0 (pack 12) (numer 0 M w nextTree) =
    pack ((12+1) * (D * scale D nextTree)) := by decide +kernel

theorem unit_defect (d : R) (hd : (D:R)*d=1) :
    (12:R)*((nextTree.factorial:R)*(b d ⬝ᵥ Φ nextTree (A d))-1) = 1 := by
  simpa only [Int.cast_ofNat,A,b] using
    exact_defect D 12 (s:=0) (δ:=0) (by simp) d hd M w nextTree nextReceipt

theorem not_order_eight [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 8 (A d) (b d) := by
  intro h
  have ht : (nextTree.order : Nat) ≤ 8 := by decide
  simpa only [h nextTree ht, sub_self, mul_zero, zero_ne_one] using unit_defect d hd

theorem denom_unit (h : IsUnit (Nat.factorial 7 : R)) : IsUnit (D:R) := by
  have hd : 11435482800 ∣ (Nat.factorial 7)^6 := by decide
  have hpow : IsUnit (((Nat.factorial 7)^6 : Nat) : R) := by
    simpa only [Nat.cast_pow] using h.pow 6
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) hd) hpow

theorem exists_exact_order_seven [Nontrivial R] (h : IsUnit (Nat.factorial 7 : R)) :
    ∃ A' : Matrix (Fin 9) (Fin 9) R, ∃ b' : Fin 9 → R,
      ERK A' ∧ HasOrder 7 A' b' ∧ ¬ HasOrder 8 A' b' := by
  obtain ⟨u,hu⟩ := denom_unit h
  let d : R := (↑(u⁻¹) : R)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d, b d, explicit d, order_seven d hd, not_order_eight d hd⟩

/-- The existence criterion is counterpart to the unrestricted
ring lower bound of nine stages in ReviewedNative.ERKUniform. -/
theorem exact_order_seven_iff [Nontrivial R] :
    (∃ A' : Matrix (Fin 9) (Fin 9) R, ∃ b' : Fin 9 → R,
      ERK A' ∧ HasOrder 7 A' b' ∧ ¬ HasOrder 8 A' b') ↔
        IsUnit (Nat.factorial 7 : R) := by
  refine ⟨?_, exists_exact_order_seven⟩
  rintro ⟨A', b', -, hp, -⟩
  have h := hp (tallTree 7) (by decide)
  have he : ((tallTree 7).factorial : R) = (Nat.factorial 7 : R) := by
    norm_cast
  exact IsUnit.of_mul_eq_one _ (he ▸ h)

end RKResearch.Certified.ERK7FactorialNine

#print axioms RKResearch.Certified.ERK7FactorialNine.order_seven
#print axioms RKResearch.Certified.ERK7FactorialNine.exact_order_seven_iff
