module

public import RKCert.ReviewedNative.ERK10TerminalBlockClockAdapter
public import RKCert.ReviewedNative.ERK10UniversalSeventeen
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact integer affine directions for the 17-stage half-port family and
its terminal contribution. The reference order for noncentral parameters
is a hypothesis; it is not inferred from the central literal build. -/
namespace RKResearch.Certified.ERK10TerminalBlockHalfPort
open ERK10TerminalBlockPolynomial ERK10TerminalBlockClockAdapter
open scoped Matrix BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 50000

open ERK10UniversalSeventeen
def uRows : Array (Array ℤ) := #[#[],
  #[0],
  #[0, 0],
  #[0, 0, 0],
  #[0, 0, 0, 0],
  #[0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[-5601052800, 0, 0, 0, 0, 0, 0, -800150400, 28005264000, 16803158400, -16803158400, 5601052800, -28005264000, 800150400],
  #[-49787136000, 0, 0, 0, 0, 0, 0, -7112448000, 248935680000, 149361408000, -149361408000, 49787136000, -248935680000, 7112448000, 0],
  #[-142884000, 0, 0, 0, 0, 0, 0, -20412000, 714420000, 428652000, -428652000, 142884000, -714420000, 20412000, 0, 0]]
def vRows : Array (Array ℤ) := #[#[],
  #[0],
  #[0, 0],
  #[0, 0, 0],
  #[0, 0, 0, 0],
  #[0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[-133358400, 0, -2000376000, -2000376000, -246960000, 1580544000, -24696000, 138297600, 1086624000, 800150400, 0, 800150400],
  #[-4096008000, 0, -61440120000, -61440120000, -7585200000, 48545280000, -758520000, 4247712000, 33374880000, 24576048000, 0, 24576048000, 0],
  #[-26004888000, 0, -390073320000, -390073320000, -48157200000, 308206080000, -4815720000, 26968032000, 211891680000, 156029328000, 0, 156029328000, 0, 0],
  #[-100818950400, 0, -1512284256000, -1512284256000, -186701760000, 1194891264000, -18670176000, 104552985600, 821487744000, 604913702400, 0, 604913702400, 0, 0, 0],
  #[-26244000, 0, -393660000, -393660000, -48600000, 311040000, -4860000, 27216000, 213840000, 157464000, 0, 157464000, 0, 0, 0, 0]]

def uNum (i j : Fin 17) : ℤ := (uRows[i.val]!)[j.val]!
def vNum (i j : Fin 17) : ℤ := (vRows[i.val]!)[j.val]!

variable {R : Type*} [CommRing R]

def familyA (d l m : R) : Matrix (Fin 17) (Fin 17) R :=
  fun i j => d * ((aNum i j:R) + l*(uNum i j:R) + m*(vNum i j:R))

theorem familyA_origin (d : R) : familyA d 0 0 = A d := by
  ext i j
  simp only [familyA,A,integerA,Matrix.smul_apply,Matrix.map_apply,Matrix.of_apply,
    smul_eq_mul,zero_mul,add_zero]
  rfl

private theorem u_strict : ∀ i j : Fin 17, i≤j → uNum i j=0 := by decide +kernel
private theorem v_strict : ∀ i j : Fin 17, i≤j → vNum i j=0 := by decide +kernel

theorem family_explicit (d l m : R) : ERK (familyA d l m) := by
  intro i j h
  have h0 := explicit d (i:=i) (j:=j) h
  rw [←familyA_origin] at h0
  simpa only [familyA, u_strict i j h, v_strict i j h, Int.cast_zero,
    mul_zero, zero_mul, add_zero] using h0

private theorem affine_read (d l m : R) (i : Fin 17) (z : Fin 17→ℤ) :
    (familyA d l m *ᵥ (fun j => (z j:R))) i =
      d * (((∑ j, aNum i j*z j : ℤ):R) +
        l*((∑ j, uNum i j*z j : ℤ):R) + m*((∑ j, vNum i j*z j : ℤ):R)) := by
  simp only [familyA,Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul]
  calc
    _ = ∑ j, d * ((aNum i j:R)*(z j:R) +
          l*((uNum i j:R)*(z j:R)) + m*((vNum i j:R)*(z j:R))) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum]

private theorem clock_constant : ∀ i : Fin 17,
    6*(∑ j : Fin 17, aNum i j)=D*node (sixClockIndex i) := by decide +kernel
private theorem clock_u : ∀ i : Fin 17, (∑ j : Fin 17, uNum i j)=0 := by decide +kernel
private theorem clock_v : ∀ i : Fin 17, (∑ j : Fin 17, vNum i j)=0 := by decide +kernel

theorem family_clock (d l m : R) (hd : (D:R)*d=1) :
    GridClocks (familyA d l m *ᵥ 1) := by
  intro i
  have W := affine_read d l m i (fun _ => 1)
  simp only [Int.cast_one,mul_one,clock_u,clock_v,Int.cast_zero,mul_zero,add_zero] at W
  change (familyA d l m *ᵥ 1) i = _ at W
  rw [W]
  have H := congrArg (Int.castRingHom R) (clock_constant i)
  simp only [map_mul,map_ofNat] at H
  change (6:R)*((∑ j : Fin 17, aNum i j : ℤ):R) =
    (D:R)*(node (sixClockIndex i):R) at H
  calc
    _ = d*((6:R)*((∑ j : Fin 17, aNum i j : ℤ):R)) := by ring
    _ = _ := by rw [H,←mul_assoc,mul_comm d (D:R),hd,one_mul]

def qInt (j : Fin 17) : ℤ := qNum (node (sixClockIndex j))
private theorem p_last : pNum (node (sixClockIndex last))=8 := by decide +kernel
private theorem last_u : (∑ j : Fin 17, uNum last j*qInt j)=0 := by decide +kernel
private theorem last_v : (∑ j : Fin 17, vNum last j*qInt j)=0 := by decide +kernel
private theorem last_a :
    35*8*bNum last*(∑ j : Fin 17, aNum last j*qInt j) = -2304*D^2 := by
  decide +kernel

theorem affine_terminal (d l m : R) (hd : (D:R)*d=1) :
    (35:R)*(b d last*(pVec (familyA d l m *ᵥ 1) last*
        (familyA d l m *ᵥ qVec (familyA d l m *ᵥ 1)) last)) = (-2304:R) := by
  have Hc := family_clock d l m hd
  have HQ : qVec (familyA d l m *ᵥ 1) = fun i => (qInt i:R) := by
    funext i
    exact q_grid Hc i
  have H := affine_read d l m last qInt
  simp only [last_u,last_v,Int.cast_zero,mul_zero,add_zero] at H
  rw [p_grid Hc last,p_last,HQ,H]
  simp only [b,Pi.smul_apply,smul_eq_mul,Function.comp_apply,Int.cast_ofNat]
  change (35:R)*( (d*(bNum last:R)) * (8*(d*((∑ j : Fin 17, aNum last j*qInt j : ℤ):R)))) = -2304
  have T := congrArg (Int.castRingHom R) last_a
  simp only [map_mul,map_pow,map_neg,map_ofNat] at T
  change (35:R)*8*(bNum last:R)*((∑ j : Fin 17, aNum last j*qInt j : ℤ):R) =
    (-2304:R)*(D:R)^2 at T
  calc
    _ = ((35:R)*8*(bNum last:R)*((∑ j : Fin 17, aNum last j*qInt j : ℤ):R))*d^2 := by ring
    _ = _ := by rw [T,mul_assoc,←mul_pow,hd,one_pow,mul_one]

/-- The reference matrix at any paid parameters, if order ten, cannot be
modified in the stated chart to an order-ten zero-weight terminal row. -/
theorem no_half_port_family_fixed_block [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d l m : R) (hd : (D:R)*d=1)
    (hpay : IsUnit (Nat.factorial 10:R))
    (hA : HasOrder 10 (familyA d l m) (b d))
    (eB : ERK B) (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (fixed : ∀ i j : Fin 17, ¬ Old i → ¬ Old j → i≠last → j≠last →
      familyA d l m i j=B i j) (hv : v last=0) : False :=
  no_fixed_block_compensation hpay (family_explicit d l m) eB hA hB
    (family_clock d l m hd) cB fixed hv (affine_terminal d l m hd)

/-- For the central literal member, the reference order is kernel-certified. -/
theorem no_half_port_literal_fixed_block [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (eB : ERK B) (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (fixed : ∀ i j : Fin 17, ¬ Old i → ¬ Old j → i≠last → j≠last →
      A d i j=B i j) (hv : v last=0) : False := by
  apply no_half_port_family_fixed_block d 0 0 hd hpay
    (by rw [familyA_origin]; exact order_ten d hd) eB hB cB ?_ hv
  simpa only [familyA_origin] using fixed

end RKResearch.Certified.ERK10TerminalBlockHalfPort

#print axioms RKResearch.Certified.ERK10TerminalBlockHalfPort.affine_terminal
#print axioms RKResearch.Certified.ERK10TerminalBlockHalfPort.no_half_port_family_fixed_block
#print axioms RKResearch.Certified.ERK10TerminalBlockHalfPort.no_half_port_literal_fixed_block
