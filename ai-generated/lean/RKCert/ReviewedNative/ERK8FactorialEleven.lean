module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A universal eleven-stage explicit order-eight tableau

The coefficients are integral numerators divided by `D`, a divisor of
`(8!)^4`. Neither the exact order proof nor the specialization needs
an ordered coefficient ring or even a domain. Exact order follows
from a Bézout identity on two ninth-order residuals. -/

namespace RKResearch.Certified.ERK8FactorialEleven

open ERKQuadraticIntegerReplay FiniteRootedTree
open scoped Matrix

def D : Int := 746807040
def rows : Array (Array Int) := #[
  #[],
  #[93350880],
  #[0,186701760],
  #[373403520,-746807040,746807040],
  #[62233920,0,248935680,62233920],
  #[76930560,0,150958080,-133622784,119107584],
  #[62233920,0,-73684961280,-165364416000,155904860160,82335476160],
  #[-49787136000,0,768713379840,-101708006400,172405739520,-788794191360,663828480],
  #[168143040,0,-528353280,296317440,0,598631040,-2004480,699840],
  #[534822750,0,248935680,62233920,1867017600,-1667674575,-9724050,4862025,-667069830],
  #[-237081600,0,2181150720,-854171136,351031296,-1282710240,5268480,-1042720,752953600,-168591360]]

def nums : Array Int := #[65345616,0,0,0,0,322828856,-19208,-19208,322828856,-29503488,65345616]
def M (i j : Fin 11) : Pair := if j < i then pack rows[i.val]![j.val]! else pack 0
def w (i : Fin 11) : Pair := pack nums[i.val]!

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

def A (d : R) : Matrix (Fin 11) (Fin 11) R := tableau 0 d M
def b (d : R) : Fin 11 → R := weights 0 d w

theorem explicit (d : R) : ERK (A d) := by
  intro i j hij
  change val (0:R) (if j<i then _ else pack 0)*d = 0
  simp [Fin.not_lt.mpr hij, val_pack]

theorem order_eight (d : R) (hd : (D:R)*d=1) : HasOrder 8 (A d) (b d) := by
  apply order_of_check D (s:=0) (δ:=0) (by simp) d hd
  intro k hk
  have h8 : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact pay0 | exact pay1 | exact pay2 | exact pay3 | exact pay4 | exact pay5 | exact pay6 | exact pay7

def bush9 : FiniteRootedTree := bushyTree 9
def tall9 : FiniteRootedTree := tallTree 9

private theorem bushReceipt : mul 0 (pack 27440) (numer 0 M w bush9) =
    pack (27177 * (D * scale D bush9)) := by decide +kernel
private theorem tallReceipt : mul 0 (pack 210) (numer 0 M w tall9) =
    pack (761 * (D * scale D tall9)) := by decide +kernel

private theorem scaled_read {k m : Int} {t : FiniteRootedTree} (d : R)
    (hd : (D:R)*d=1)
    (h : mul 0 (pack k) (numer 0 M w t) = pack (m*(D*scale D t))) :
    (k:R)*((t.factorial:R)*(b d ⬝ᵥ Φ t (A d))) = (m:R) := by
  have hz : (0:R)*0 = ((0:Int):R) := by simp
  have h' := congrArg (val (0:R)) h
  simp only [val_mul hz,val_pack,Int.cast_mul] at h'
  rw [A,b,paid_eq hz d]
  calc
    _ = ((k:R) * val (0:R) (numer 0 M w t))*(d*scale d t) := by ring
    _ = (m:R)*(((D:R)*d)*(((scale D t:Int):R)*scale d t)) := by rw [h']; ring
    _ = (m:R) := by rw [hd,scales_cancel D d hd t]; simp

/-- The ninth-order bush residue is −263/27440. The ninth-order
tall residue is 551/210. The integer numerators are relatively prime;
a single residue need not be nonzero after every specialization. -/
theorem ninth_defects_bezout (d : R) (hd : (D:R)*d=1) :
    -(44:R)*(27440*((bush9.factorial:R)*(b d ⬝ᵥ Φ bush9 (A d))-1))
      -21*(210*((tall9.factorial:R)*(b d ⬝ᵥ Φ tall9 (A d))-1)) = 1 := by
  have hb := scaled_read d hd bushReceipt
  have ht := scaled_read d hd tallReceipt
  simp only [Int.cast_ofNat] at hb ht
  calc
    _ = -(44:R)*(27440*((bush9.factorial:R)*(b d ⬝ᵥ Φ bush9 (A d)))-27440)
          -21*(210*((tall9.factorial:R)*(b d ⬝ᵥ Φ tall9 (A d)))-210) := by ring
    _ = 1 := by rw [hb,ht]; ring

theorem not_order_nine [Nontrivial R] (d : R) (hd : (D:R)*d=1) :
    ¬ HasOrder 9 (A d) (b d) := by
  intro h
  have hb : (bush9.order:Nat) ≤ 9 := by decide
  have ht : (tall9.order:Nat) ≤ 9 := by decide
  simpa only [h bush9 hb,h tall9 ht,sub_self,mul_zero,zero_sub,neg_zero,zero_ne_one] using
    ninth_defects_bezout d hd

theorem denom_unit (h : IsUnit (Nat.factorial 8 : R)) : IsUnit (D:R) := by
  have hd : 746807040 ∣ (Nat.factorial 8)^4 := by decide
  have hpow : IsUnit (((Nat.factorial 8)^4 : Nat) : R) := by
    simpa only [Nat.cast_pow] using h.pow 4
  simpa only [D,Int.cast_ofNat,Nat.cast_ofNat] using
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) hd) hpow

theorem exists_exact_order_eight [Nontrivial R] (h : IsUnit (Nat.factorial 8 : R)) :
    ∃ A' : Matrix (Fin 11) (Fin 11) R, ∃ b' : Fin 11 → R,
      ERK A' ∧ HasOrder 8 A' b' ∧ ¬ HasOrder 9 A' b' := by
  obtain ⟨u,hu⟩ := denom_unit h
  let d : R := (↑(u⁻¹) : R)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d, b d, explicit d, order_eight d hd, not_order_nine d hd⟩

theorem exact_order_eight_iff [Nontrivial R] :
    (∃ A' : Matrix (Fin 11) (Fin 11) R, ∃ b' : Fin 11 → R,
      ERK A' ∧ HasOrder 8 A' b' ∧ ¬ HasOrder 9 A' b') ↔
        IsUnit (Nat.factorial 8 : R) := by
  refine ⟨?_, exists_exact_order_eight⟩
  rintro ⟨A', b', -, hp, -⟩
  have h := hp (tallTree 8) (by decide)
  have he : ((tallTree 8).factorial : R) = (Nat.factorial 8 : R) := by norm_cast
  exact IsUnit.of_mul_eq_one _ (he ▸ h)

end RKResearch.Certified.ERK8FactorialEleven

#print axioms RKResearch.Certified.ERK8FactorialEleven.order_eight
#print axioms RKResearch.Certified.ERK8FactorialEleven.exact_order_eight_iff
