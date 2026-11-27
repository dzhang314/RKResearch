module

public import RKCert.ReviewedNative.ERK10TerminalBlockPolynomial
public import RKResearch.ERK
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

@[expose] public section

/-! The literal clock grouping and preserved high-block interface for
the terminal deletion obstruction. -/
namespace RKResearch.Certified.ERK10TerminalBlockClockAdapter
open ERK10TerminalBlockPolynomial
open scoped Matrix BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 50000

def cardRows : Array (Array ℤ) := #[#[0, 1440, -1368, -1324, 1638, -231, -252, 114, -18, 1],
#[0, 2160, -2412, -1464, 2527, -791, -98, 94, -17, 1],
#[0, 4320, -6984, 1644, 1946, -1001, 14, 76, -16, 1],
#[4320, -2664, -5340, 3590, 945, -987, 90, 60, -15, 1],
#[0, -4320, -1656, 3684, 94, -851, 136, 46, -14, 1],
#[0, -2160, 252, 2796, -397, -671, 158, 34, -13, 1],
#[0, -1440, 408, 1916, -558, -501, 162, 24, -12, 1],
#[0, -1080, 396, 1434, -539, -371, 154, 16, -11, 1],
#[0, -864, 360, 1140, -490, -287, 140, 10, -10, 1],
#[0, -720, 324, 944, -441, -231, 126, 6, -9, 1]]
def pivots : Array ℤ := #[-362880, 40320, -10080, 4320, -2880, 2880, -4320, 10080, -40320, 362880]
def cofactors : Array ℤ := #[-36288000, 326592000, -1306368000, 3048192000, -4572288000, 4572288000, -3048192000, 1306368000, -326592000, 36288000]

def sixClockIndex : Fin 17 → Fin 10 := ![3,5,7,5,9,6,9,9,6,4,7,8,5,2,1,0,9]
def node (j : Fin 10) : ℤ := (j.val:ℤ)-3

def cp (j k : Fin 10) : ℤ := (cardRows[j.val]!)[k.val]!
def pivot (j : Fin 10) : ℤ := pivots[j.val]!
def cof (j : Fin 10) : ℤ := cofactors[j.val]!

theorem cp_receipt : ∀ (g j : Fin 10),
    (∑ k : Fin 10, cp g k * (node j)^k.val) =
      if g=j then pivot g else 0 := by decide +kernel

theorem pivot_receipt : ∀ j : Fin 10, pivot j*cof j = (Nat.factorial 10:ℤ)^2 := by
  decide +kernel

def Old (i : Fin 17) : Prop := i.val<9
def Dup (i : Fin 17) : Prop := i=10 ∨ i=12
def last : Fin 17 := 16
instance (i : Fin 17) : Decidable (Old i) := inferInstanceAs (Decidable (i.val<9))
instance (i : Fin 17) : Decidable (Dup i) := inferInstanceAs (Decidable (i=10 ∨ i=12))

theorem unique_clock : ∀ i j : Fin 17,
    ¬ Old i → ¬ Dup i → i≠last → sixClockIndex i = sixClockIndex j → j=i := by
  decide +kernel

def pNum (z : ℤ) : ℤ := (z-2)*(z-4)
def qNum (z : ℤ) : ℤ := z*(z-2)*(z-3)*(z-4)*(z-6)

theorem old_zero : ∀ i : Fin 17, Old i → qNum (node (sixClockIndex i))=0 := by
  decide +kernel

theorem dup_zero : ∀ i : Fin 17, Dup i → pNum (node (sixClockIndex i))=0 := by
  decide +kernel

variable {R : Type*} [CommRing R]

def GridClocks (c : Fin 17→R) : Prop :=
  ∀ i, (6:R)*c i=(node (sixClockIndex i):R)

private theorem p_eval (c : Fin 17→R) (i : Fin 17) :
    pVec c i=(6*c i-2)*(6*c i-4) := by
  simp only [pVec,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply,
    Fin.sum_univ_succ,pCoeff]
  change (8:R)*c i^0 + ((-36)*c i^1 + (36*c i^2 + 0)) = _
  ring

private theorem q_eval (c : Fin 17→R) (i : Fin 17) :
    qVec c i=(6*c i)*(6*c i-2)*(6*c i-3)*(6*c i-4)*(6*c i-6) := by
  simp only [qVec,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply,
    Fin.sum_univ_succ,qCoeff]
  change (864:R)*c i^1 + ((-6480)*c i^2 + (17280*c i^3 + ((-19440)*c i^4 + (7776*c i^5 + 0)))) = _
  ring

theorem p_grid {c : Fin 17→R} (hc : GridClocks c) (i : Fin 17) :
    pVec c i=(pNum (node (sixClockIndex i)):R) := by
  rw [p_eval,hc i]
  simp only [pNum,Int.cast_mul,Int.cast_sub,Int.cast_ofNat]

theorem q_grid {c : Fin 17→R} (hc : GridClocks c) (i : Fin 17) :
    qVec c i=(qNum (node (sixClockIndex i)):R) := by
  rw [q_eval,hc i]
  simp only [qNum,Int.cast_mul,Int.cast_sub,Int.cast_ofNat]

def cardVec (g : Fin 10) (c : Fin 17→R) : Fin 17→R :=
  ∑ k : Fin 10, ((cp g k:R)*(6:R)^k.val) • c^k.val

theorem cardVec_grid (g : Fin 10) {c : Fin 17→R} (hc : GridClocks c) :
    cardVec g c = fun i => if g=sixClockIndex i then (pivot g:R) else 0 := by
  funext i
  simp only [cardVec,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply]
  have H := congrArg (Int.castRingHom R) (cp_receipt g (sixClockIndex i))
  simp only [map_sum,map_mul,map_pow] at H
  calc
    _ = ∑ k : Fin 10, (cp g k:R)*((6:R)*c i)^k.val := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow,mul_assoc]
    _ = _ := by
      rw [hc i]
      by_cases h : g=sixClockIndex i
      · simp only [ite_eq_left h] at H ⊢
        exact H
      · simp only [ite_eq_right h,map_zero] at H ⊢
        exact H

theorem pivot_unit (hpay : IsUnit (Nat.factorial 10:R)) (g : Fin 10) :
    IsUnit (pivot g:R) := by
  have H := congrArg (Int.castRingHom R) (pivot_receipt g)
  simp only [map_mul,map_pow,map_natCast] at H
  change (pivot g:R)*(cof g:R)=(Nat.factorial 10:R)^2 at H
  exact isUnit_of_dvd_unit ⟨(cof g:R),rfl⟩ (H.symm ▸ hpay.pow 2)

theorem isolated_card (g : Fin 10) {c b : Fin 17→R} (hc : GridClocks c) (i : Fin 17)
    (hi : g=sixClockIndex i) (Hu : ∀ j, g=sixClockIndex j → j=i) :
    (b ⬝ᵥ cardVec g c) = b i*(pivot g:R) := by
  rw [cardVec_grid g hc,dotProduct]
  calc
    _ = b i*(if g=sixClockIndex i then (pivot g:R) else 0) := by
      apply Finset.sum_eq_single i
      · intro j _ h
        rw [ite_eq_right fun h₀ => h (Hu j h₀),mul_zero]
      · intro h
        exact (h (Finset.mem_univ i)).elim
    _ = _ := by rw [ite_eq_left hi]

theorem card_agrees {c d b v : Fin 17→R} (g : Fin 10)
    (h : HasQuadratureOrder 10 b c) (h' : HasQuadratureOrder 10 v d) :
    (b ⬝ᵥ cardVec g c) = (v ⬝ᵥ cardVec g d) := by
  simp only [cardVec,dotProduct_sum,dotProduct_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have huc : IsUnit ((k.val+1:ℕ):R) := h.isUnit (by omega) (Nat.succ_le_of_lt k.isLt)
  have eq0 : (b ⬝ᵥ c^k.val) = (v ⬝ᵥ d^k.val) :=
    huc.mul_left_cancel ((h k.val k.isLt).trans (h' k.val k.isLt).symm)
  rw [eq0]

theorem weight_agrees {c d b v : Fin 17→R}
    (hpay : IsUnit (Nat.factorial 10:R))
    (hc : GridClocks c) (hd : GridClocks d)
    (h : HasQuadratureOrder 10 b c) (h' : HasQuadratureOrder 10 v d)
    (i : Fin 17) (hi : ¬ Old i) (hj : ¬ Dup i) (hl : i≠last) :
    b i=v i := by
  let g := sixClockIndex i
  have hu (j : Fin 17) : g=sixClockIndex j → j=i := fun q => unique_clock i j hi hj hl q
  have W := card_agrees g h h'
  rw [isolated_card g hc i rfl hu,isolated_card g hd i rfl hu] at W
  exact (pivot_unit hpay g).mul_right_cancel W

theorem no_fixed_block_compensation [Nontrivial R]
    {A B : Matrix (Fin 17) (Fin 17) R} {w v : Fin 17→R}
    (hpay : IsUnit (Nat.factorial 10:R))
    (eA : ERK A) (eB : ERK B) (hA : HasOrder 10 A w) (hB : HasOrder 10 B v)
    (cA : GridClocks (A *ᵥ 1)) (cB : GridClocks (B *ᵥ 1))
    (fixed : ∀ i j : Fin 17, ¬ Old i → ¬ Old j → i≠last → j≠last → A i j=B i j)
    (hv : v last = 0)
    (bad : (35:R)*(w last*(pVec (A *ᵥ 1) last*(A *ᵥ qVec (A *ᵥ 1)) last)) =
      (-2304:R)) :
    False := by
  have pEq i : pVec (A *ᵥ 1) i = pVec (B *ᵥ 1) i := by rw [p_grid cA,p_grid cB]
  have qEq i : qVec (A *ᵥ 1) i = qVec (B *ᵥ 1) i := by rw [q_grid cA,q_grid cB]
  have oldA i (hi : Old i) : qVec (A *ᵥ 1) i=0 := by rw [q_grid cA,old_zero i hi,Int.cast_zero]
  have oldB i (hi : Old i) : qVec (B *ᵥ 1) i=0 := by rw [←qEq,oldA i hi]
  have hl (i : Fin 17) (hi : i≠last) : i≤last := by
    change i.val≤16
    have := i.isLt
    omega
  have matchRead i (hi : i≠last) :
      (A *ᵥ qVec (A *ᵥ 1)) i = (B *ᵥ qVec (B *ᵥ 1)) i := by
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hf : Old j
    · simp only [oldA j hf,oldB j hf,mul_zero]
    · by_cases hh : Old i
      · have h : i≤j := show i.val≤j.val from by
          simp only [Old] at hf hh
          omega
        simp only [eA h,eB h,zero_mul]
      · by_cases hj : j=last
        · subst j
          simp only [eA (hl i hi),eB (hl i hi),zero_mul]
        · rw [fixed i j hh hf hi hj,qEq j]
  have zeroA i (hi : Old i) : (A *ᵥ qVec (A *ᵥ 1)) i=0 := by
    rw [Matrix.mulVec,dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : Old j
    · rw [oldA j h,mul_zero]
    · have h' : i≤j := show i.val≤j.val from by
        simp only [Old] at hi h
        omega
      rw [eA h',zero_mul]
  have hA9 : HasOrder 9 A w := fun t ht => hA t (ht.trans (by decide))
  have hB9 : HasOrder 9 B v := fun t ht => hB t (ht.trans (by decide))
  refine last_contribution_impossible hpay hA9 hB9 last ?_ hv ?_
  · intro i h
    by_cases hi : Old i
    · rw [←matchRead i h]
      simp [zeroA i hi]
    · by_cases hj : Dup i
      · simp only [p_grid cA i,p_grid cB i,dup_zero i hj,Int.cast_zero,zero_mul,mul_zero]
      · rw [weight_agrees hpay cA cB hA.hasQuadratureOrder hB.hasQuadratureOrder i hi hj h,
          pEq i,matchRead i h]
  · intro h
    rw [h,mul_zero] at bad
    have hD : IsUnit (((Nat.factorial 10)^2:ℕ):R) := by
      simpa only [Nat.cast_pow] using hpay.pow 2
    have hU : IsUnit ((2304:ℕ):R) := isUnit_of_dvd_unit
      (Nat.cast_dvd_cast (α:=R) (show (2304:ℕ)∣(Nat.factorial 10)^2 by decide +kernel)) hD
    apply hU.ne_zero
    apply neg_eq_zero.mp
    simpa only [Nat.cast_ofNat] using bad.symm

end RKResearch.Certified.ERK10TerminalBlockClockAdapter

#print axioms RKResearch.Certified.ERK10TerminalBlockClockAdapter.no_fixed_block_compensation
