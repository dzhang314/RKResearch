module

public import RKCert.ReviewedNative.ERK10FrozenTailMixedMoments
import Mathlib.Tactic.Ring

@[expose] public section

/-! Distinct masks for unrestricted retapping of the final three or four
surviving rows of the half-port reference method. All indices start at 0. -/
namespace RKResearch.Certified.ERK10FrozenTailCompensation
open scoped Matrix BigOperators
open ERK10FrozenTailMixedMoments ERK10TerminalBlockClockAdapter
open ERK10TerminalBlockHalfPort ERK10UniversalSeventeen
set_option maxHeartbeats 0
set_option maxRecDepth 50000

variable {R : Type*} [CommRing R]

def Frozen (k : ℕ) (A B : Matrix (Fin 17) (Fin 17) R) : Prop :=
  ∀ i j : Fin 17, i.val<k → A i j=B i j

private theorem score_frozen {n k : ℕ} (T : Fin n → Monomial)
    {A B : Matrix (Fin 17) (Fin 17) R}
    (cA : GridClocks (A *ᵥ 1)) (cB : GridClocks (B *ᵥ 1))
    (h : Frozen k A B) (i : Fin 17) (hi : i.val<k) :
    score T A i = score T B i := by
  rw [score_grid T cA,score_grid T cB]
  exact Finset.sum_congr rfl (fun j _ => by rw [h i j hi])

private theorem score_zero {n : ℕ} (T : Fin n → Monomial)
    {B : Matrix (Fin 17) (Fin 17) R} (cB : GridClocks (B *ᵥ 1)) (i : Fin 17)
    (h : ∀ j, loadInt T i j=0) : score T B i=0 := by
  rw [score_grid T cB]
  simp only [h,Int.cast_zero,mul_zero,Finset.sum_const_zero]

theorem tail_gap {n : ℕ} (T : Fin n → Monomial)
    (hT : ∀ t, (T t).outExp.val+(T t).inExp.val+2≤10)
    (hpay : IsUnit (Nat.factorial 10:R))
    {A B : Matrix (Fin 17) (Fin 17) R} {w v : Fin 17→R}
    (hA : HasOrder 10 A w) (hB : HasOrder 10 B v)
    (cA : GridClocks (A *ᵥ 1)) (cB : GridClocks (B *ᵥ 1))
    (f : Fin 10→R)
    (knownA : ∀ i, i≠last → w i*score T A i=w i*f (sixClockIndex i))
    (knownB : ∀ i, v i*score T B i=v i*f (sixClockIndex i))
    (bad : w last*(score T A last-f (sixClockIndex last))≠0) : False := by
  let ff := fun i => f (sixClockIndex i)
  have group : (w ⬝ᵥ ff) = (v ⬝ᵥ ff) :=
    grid_integrate_agrees hpay cA cB hA.hasQuadratureOrder hB.hasQuadratureOrder f
  have hB0 : (v ⬝ᵥ score T B) = (v ⬝ᵥ ff) :=
    Finset.sum_congr rfl (fun i _ => knownB i)
  have H := (score_agrees T hT hpay hA hB).trans (hB0.trans group.symm)
  have hs : ∑ i, (w i*score T A i-w i*ff i)=0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr H
  have hsingle : (∑ i, (w i*score T A i-w i*ff i)) =
      w last*score T A last-w last*ff last :=
    Finset.sum_eq_single last
      (fun i _ hi => sub_eq_zero.mpr (knownA i hi))
      (fun h => (h (Finset.mem_univ _)).elim)
  rw [hsingle,←mul_sub] at hs
  exact bad hs
def three : Fin 19 → Monomial := ![⟨0,2,44064⟩,
  ⟨0,4,-2700⟩,
  ⟨0,5,216⟩,
  ⟨1,2,78840⟩,
  ⟨1,4,-4950⟩,
  ⟨1,5,396⟩,
  ⟨2,1,-20304⟩,
  ⟨2,2,44712⟩,
  ⟨2,4,-2700⟩,
  ⟨2,5,216⟩,
  ⟨3,1,-37224⟩,
  ⟨3,2,12474⟩,
  ⟨3,4,-450⟩,
  ⟨3,5,36⟩,
  ⟨4,1,-20304⟩,
  ⟨4,2,2700⟩,
  ⟨5,1,-3384⟩,
  ⟨5,2,54⟩,
  ⟨6,2,-108⟩]
def four : Fin 14 → Monomial := ![⟨0,2,-41472⟩,
  ⟨0,4,5400⟩,
  ⟨0,5,-432⟩,
  ⟨1,2,-44928⟩,
  ⟨1,4,1800⟩,
  ⟨1,5,-144⟩,
  ⟨2,4,-1350⟩,
  ⟨2,5,108⟩,
  ⟨3,2,11880⟩,
  ⟨3,4,-450⟩,
  ⟨3,5,36⟩,
  ⟨4,2,2808⟩,
  ⟨5,2,-162⟩,
  ⟨6,2,-54⟩]

private theorem three_small : ∀ i, (three i).outExp.val+(three i).inExp.val+2≤10 := by
  decide +kernel
private theorem four_small : ∀ i, (four i).outExp.val+(four i).inExp.val+2≤10 := by
  decide +kernel

-- One chosen representative for each scalar grid site. In particular index 4
-- (rather than the deleted last row) represents clock one.
def siteRep : Fin 10 → Fin 17 := ![15,14,13,0,9,1,5,2,11,4]
def siteThree (g : Fin 10) : ℤ := aScore three (siteRep g)
def siteFour (g : Fin 10) : ℤ := aScore four (siteRep g)

private theorem three_group : ∀ i : Fin 17, i≠last →
    aScore three i=siteThree (sixClockIndex i) := by decide +kernel
private theorem three_u : ∀ i, uScore three i=0 := by decide +kernel
private theorem three_v : ∀ i, vScore three i=0 := by decide +kernel
private theorem three_mask : ∀ i j : Fin 17, ¬ i.val<13 → i≠last →
    loadInt three i j=0 := by decide +kernel
private theorem three_site_zero : ∀ i : Fin 17, ¬ i.val<13 → i≠last →
    siteThree (sixClockIndex i)=0 := by decide +kernel
private theorem three_gap :
    5*bNum last*(aScore three last-siteThree (sixClockIndex last)) =
      -746496*D^2 := by decide +kernel

private theorem four_group : ∀ i : Fin 17, i≠last → i≠13 →
    aScore four i=siteFour (sixClockIndex i) := by decide +kernel
private theorem four_u : ∀ i : Fin 17, i≠13 → uScore four i=0 := by decide +kernel
private theorem four_v : ∀ i : Fin 17, i≠13 → vScore four i=0 := by decide +kernel
private theorem four_mask : ∀ i j : Fin 17, ¬ i.val<12 → i≠last → i≠13 →
    loadInt four i j=0 := by decide +kernel
private theorem four_site_zero : ∀ i : Fin 17, ¬ i.val<12 → i≠last → i≠13 →
    siteFour (sixClockIndex i)=0 := by decide +kernel
private theorem four_gap :
    35*bNum last*(aScore four last-siteFour (sixClockIndex last)) =
      -2985984*D^2 := by decide +kernel
private theorem b13_receipt : bNum (13:Fin 17)=11*3429216 := by decide +kernel

private theorem gap_from_int [Nontrivial R] {n : ℕ}
    {T : Fin n → Monomial} {site : Fin 10 → ℤ}
    (d l m : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (hs : uScore T last=0 ∧ vScore T last=0)
    (den num : ℕ) (hunit : num∣(Nat.factorial 10)^2)
    (data : (den:ℤ)*bNum last*(aScore T last-site (sixClockIndex last)) =
        -(num:ℤ)*D^2) :
    b d last*(score T (familyA d l m) last-d*(site (sixClockIndex last):R))≠0 := by
  intro hz
  rw [score_family T d l m hd,hs.1,hs.2] at hz
  simp only [Int.cast_zero,mul_zero,add_zero] at hz
  change (d*(bNum last:R))*(d*(aScore T last:R)-d*(site (sixClockIndex last):R))=0 at hz
  have H := congrArg (Int.castRingHom R) data
  simp only [map_mul,map_pow,map_sub,map_neg,map_natCast] at H
  change (den:R)*(bNum last:R)*((aScore T last:R)-(site (sixClockIndex last):R)) =
      -(num:R)*(D:R)^2 at H
  have q : -(num:R)=0 := by
    calc
      -(num:R) = (-(num:R)*(D:R)^2)*d^2 := by rw [mul_assoc,←mul_pow,hd,one_pow,mul_one]
      _ = (den:R)*((d*(bNum last:R))*
          (d*(aScore T last:R)-d*(site (sixClockIndex last):R))) := by rw [←H]; ring
      _ = 0 := by rw [hz,mul_zero]
  have U : IsUnit ((num:ℕ):R) := isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) hunit)
    (by simpa only [Nat.cast_pow] using hpay.pow 2)
  exact U.ne_zero (neg_eq_zero.mp q)

/-- Freeze only the first thirteen actual rows; all three remaining
surviving rows can be retapped arbitrarily. The deleted row is zero-weight
chronological padding at the original clock one. -/
theorem no_three_tail_retap [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d l m : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (hA : HasOrder 10 (familyA d l m) (b d))
    (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (hf : Frozen 13 (familyA d l m) B) (hv : v last=0) : False := by
  let cA := family_clock d l m hd
  let f := fun g => d*(siteThree g:R)
  have H (i : Fin 17) (hi : i≠last) : score three (familyA d l m) i=f (sixClockIndex i) := by
    rw [score_family three d l m hd,three_group i hi,three_u i,three_v i]
    simp only [f,Int.cast_zero,mul_zero,add_zero]
  refine tail_gap three three_small hpay hA hB cA cB f
    (fun i hi => by rw [H i hi]) ?_ ?_
  · intro i
    by_cases hil : i=last
    · subst i
      simp only [hv,zero_mul]
    by_cases ht : i.val<13
    · rw [←score_frozen three cA cB hf i ht,H i hil]
    · rw [score_zero three cB i (fun j => three_mask i j ht hil)]
      simp only [f,three_site_zero i ht hil,Int.cast_zero,mul_zero]
  · exact gap_from_int d l m hd hpay ⟨three_u last,three_v last⟩ 5 746496
      (by decide +kernel) three_gap

/-- In characteristic eleven, the unique clock minus one sixth has zero
output. A different mask can therefore free four retapped surviving rows. -/
theorem no_four_tail_retap_char11 [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d l m : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (h11 : (11:R)=0)
    (hA : HasOrder 10 (familyA d l m) (b d))
    (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (hf : Frozen 12 (familyA d l m) B) (hv : v last=0) : False := by
  let cA := family_clock d l m hd
  let f := fun g => d*(siteFour g:R)
  have HB13 : b d (13:Fin 17)=0 := by
    change d*(bNum (13:Fin 17):R)=0
    have hp : ((11:ℤ):R)=0 := by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h11
    rw [b13_receipt,Int.cast_mul,hp,zero_mul,mul_zero]
  have HV13 : v (13:Fin 17)=0 := by
    rw [←weight_agrees hpay cA cB hA.hasQuadratureOrder hB.hasQuadratureOrder 13
      (by decide +kernel) (by decide +kernel) (by decide +kernel),HB13]
  have H (i : Fin 17) (hi : i≠last) (hh : i≠13) :
      score four (familyA d l m) i=f (sixClockIndex i) := by
    rw [score_family four d l m hd,four_group i hi hh,four_u i hh,four_v i hh]
    simp only [f,Int.cast_zero,mul_zero,add_zero]
  refine tail_gap four four_small hpay hA hB cA cB f ?_ ?_ ?_
  · intro i hi
    by_cases hh : i=13
    · subst i
      simp only [HB13,zero_mul]
    · rw [H i hi hh]
  · intro i
    by_cases hil : i=last
    · subst i
      simp only [hv,zero_mul]
    by_cases hii : i=13
    · subst i
      simp only [HV13,zero_mul]
    by_cases ht : i.val<12
    · rw [←score_frozen four cA cB hf i ht,H i hil hii]
    · rw [score_zero four cB i (fun j => four_mask i j ht hil hii)]
      simp only [f,four_site_zero i ht hil hii,Int.cast_zero,mul_zero]
  · exact gap_from_int d l m hd hpay
      ⟨four_u last (by decide +kernel),four_v last (by decide +kernel)⟩ 35 2985984
      (by decide +kernel) four_gap

theorem no_three_tail_retap_literal [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (hf : Frozen 13 (A d) B) (hv : v last=0) : False := by
  refine no_three_tail_retap d 0 0 hd hpay
    (by rw [familyA_origin]; exact order_ten d hd) hB cB ?_ hv
  simpa only [familyA_origin] using hf

theorem no_four_tail_retap_char11_literal [Nontrivial R]
    {B : Matrix (Fin 17) (Fin 17) R} {v : Fin 17→R}
    (d : R) (hd : (D:R)*d=1) (hpay : IsUnit (Nat.factorial 10:R))
    (h11 : (11:R)=0)
    (hB : HasOrder 10 B v) (cB : GridClocks (B *ᵥ 1))
    (hf : Frozen 12 (A d) B) (hv : v last=0) : False := by
  refine no_four_tail_retap_char11 d 0 0 hd hpay h11
    (by rw [familyA_origin]; exact order_ten d hd) hB cB ?_ hv
  simpa only [familyA_origin] using hf

end RKResearch.Certified.ERK10FrozenTailCompensation

#print axioms RKResearch.Certified.ERK10FrozenTailCompensation.no_three_tail_retap
#print axioms RKResearch.Certified.ERK10FrozenTailCompensation.no_four_tail_retap_char11
#print axioms RKResearch.Certified.ERK10FrozenTailCompensation.no_three_tail_retap_literal
#print axioms RKResearch.Certified.ERK10FrozenTailCompensation.no_four_tail_retap_char11_literal
