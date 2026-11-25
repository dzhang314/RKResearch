module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortInteger
public import RKCert.ReviewedNative.WeakFiveThreeInteriorCertified

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal homogeneous ratio endpoints for the nine released words

The integers come from the frozen row, never from a second endpoint table.
Gamma is coordinate zero, then the optional extra root, then roots 1,2,3. -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

def wordRootRank : ThreeInteriorWord → Fin 3 → Fin 7
  | .w0 | .w1 => ![0,2,5]
  | .w2 | .w3 => ![1,3,5]
  | .w4 | .w5 | .w6 => ![1,3,5]
  | .w7 | .w8 => ![1,4,6]

def wordMarkRank : ThreeInteriorWord → Fin 4 → Fin 7
  | .w0 => ![6,3,4,1]
  | .w1 => ![6,4,3,1]
  | .w2 => ![4,6,0,2]
  | .w3 => ![6,4,0,2]
  | .w4 => ![6,2,4,0]
  | .w5 => ![4,6,2,0]
  | .w6 => ![6,4,2,0]
  | .w7 => ![5,2,3,0]
  | .w8 => ![5,3,2,0]

def wordSiteRank (w : ThreeInteriorWord) : ThreeInteriorSite → Fin 7 :=
  Sum.elim (wordRootRank w) (wordMarkRank w)

theorem word_label_at_rank (w : ThreeInteriorWord) (a : ThreeInteriorSite) :
    w.labels (wordSiteRank w a) = a := by
  rcases a with a | a <;> cases w <;> fin_cases a <;> rfl

def portStop : ThreeInteriorPort → Fin 4
  | .l1 | .l2 => 0
  | .la => 1
  | .r1 | .r2 => 3
  | .rh => 2

def portFactorSite : (p : ThreeInteriorPort) → Fin p.count → ThreeInteriorSite
  | .l1 | .l2 | .r1 | .r2 => fun i => .inl i
  | .la => Fin.cons (.inr 0) (fun i => .inl i)
  | .rh => Fin.cons (.inr 3) (fun i => .inl i)

def portCageIndex (c : ThreeInteriorCell) (w : ThreeInteriorWord)
    (upper : Bool) (label : ThreeInteriorSite) : ℕ :=
  cond upper (c.high (wordSiteRank w label)) (c.low (wordSiteRank w label))

def portDensityIndex (c : ThreeInteriorCell) (upper : Bool) : ℕ :=
  cond upper (c.rect.xIndex+1) c.rect.xIndex

def portDensityDen (c : ThreeInteriorCell) : ℕ := 2^c.rect.xDepth

/-- If `s = i/S` and `d = dNum/8192`, these fractions are exactly
the left and right density coordinates used by the published checker. -/
def homogeneousGamma (right : Bool) (S i dNum : ℤ) : PortFraction :=
  if right then ⟨(S-i)*(8192-dNum), S*8192⟩
  else ⟨(S-i)*dNum, i*8192+(S-i)*dNum⟩

def homogeneousRoot (right : Bool) (dNum xNum : ℤ) : PortFraction :=
  if right then ⟨xNum-dNum,8192-dNum⟩ else ⟨xNum,dNum⟩

def wordGammaEnd (c : ThreeInteriorCell) (w : ThreeInteriorWord) (upper : Bool) : PortFraction :=
  homogeneousGamma w.port.side (portDensityDen c) (portDensityIndex c (!upper))
    (portCageIndex c w (cond w.port.side (!upper) upper) (.inr (portStop w.port)))

def wordRootEnd (c : ThreeInteriorCell) (w : ThreeInteriorWord)
    (j : Fin w.port.count) (upper : Bool) : PortFraction :=
  homogeneousRoot w.port.side (portCageIndex c w (!upper) (.inr (portStop w.port)))
    (portCageIndex c w upper (portFactorSite w.port j))

def wordPortBounds (c : ThreeInteriorCell) (w : ThreeInteriorWord) (upper : Bool) :
    Fin (w.port.count+1) → ℚ :=
  Fin.cons ((wordGammaEnd c w upper).value) (fun j => (wordRootEnd c w j upper).value)

def checkPortWord (c : ThreeInteriorCell) (w : ThreeInteriorWord) : Bool :=
  checkPortRootCorners w.port.count (portBaseMoments w.port.side w.port.exponent)
    (wordRootEnd c w) (wordGammaEnd c w) w.positive

def portWords : List ThreeInteriorWord := [.w0,.w1,.w2,.w3,.w4,.w5,.w6,.w7,.w8]

theorem mem_portWords (w : ThreeInteriorWord) : w ∈ portWords := by
  cases w <;> simp [portWords]

def checkPortRow (c : ThreeInteriorCell) : Bool := portWords.all (checkPortWord c)

theorem checkPortRow_intro {c : ThreeInteriorCell}
    (h : ∀ w, checkPortWord c w = true) : checkPortRow c = true :=
  List.all_eq_true.mpr (fun w _ => h w)

section OrderedField
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def portDensityEnd (c : ThreeInteriorCell) (upper : Bool) : K :=
  gridCoord (portDensityDen c) (portDensityIndex c upper)

def portCageEnd (c : ThreeInteriorCell) (w : ThreeInteriorWord) (upper : Bool)
    (label : ThreeInteriorSite) : K :=
  gridCoord 8192 (portCageIndex c w upper label)

theorem portFraction_value_cast (a : PortFraction) :
    (a.value (K := ℚ) : K) = a.value := by
  simp only [PortFraction.value,Rat.cast_div,Rat.cast_intCast]

private theorem homogeneousGamma_value (right : Bool) {S i d : ℤ} (Sn : (S:K) ≠ 0) :
    (homogeneousGamma right S i d).value (K := K) =
      if right then threeInteriorRightGamma ((i:K)/(S:K)) ((d:K)/8192)
      else threeInteriorLeftGamma ((i:K)/(S:K)) ((d:K)/8192) := by
  have Gn : (8192:K) ≠ 0 := by norm_num
  have both : (S:K)*8192 ≠ 0 := mul_ne_zero Sn Gn
  have num :
      (1-(i:K)/(S:K))*((d:K)/8192) =
        (((S:K)-(i:K))*(d:K))/((S:K)*8192) := by
    field_simp [Sn,Gn] <;> ring
  have den :
      (i:K)/(S:K)+(1-(i:K)/(S:K))*((d:K)/8192) =
        ((i:K)*8192+((S:K)-(i:K))*(d:K))/((S:K)*8192) := by
    field_simp [Sn,Gn] <;> ring
  cases right
  · simp only [homogeneousGamma,Bool.false_eq_true,if_false,PortFraction.value,
      Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_ofNat,threeInteriorLeftGamma,
      threeInteriorLeftScale]
    rw [den,num,div_div_div_cancel_right₀ both]
  · simp only [homogeneousGamma,if_true,PortFraction.value,Int.cast_add,Int.cast_mul,
      Int.cast_sub,Int.cast_ofNat,threeInteriorRightGamma]
    field_simp [Sn,Gn] <;> ring

private theorem homogeneousRoot_value (right : Bool) (d x : ℤ) :
    (homogeneousRoot right d x).value (K := K) =
      if right then threeInteriorRightRoot ((d:K)/8192) ((x:K)/8192)
      else threeInteriorLeftRoot ((d:K)/8192) ((x:K)/8192) := by
  have Gn : (8192:K) ≠ 0 := by norm_num
  cases right
  · simp only [homogeneousRoot,Bool.false_eq_true,if_false,PortFraction.value,
      threeInteriorLeftRoot,div_div_div_cancel_right₀ Gn]
  · have num : (x:K)/8192-(d:K)/8192 = ((x:K)-(d:K))/8192 := (sub_div _ _ _).symm
    have den : 1-(d:K)/8192 = (8192-(d:K))/8192 := by field_simp [Gn] <;> ring
    simp only [homogeneousRoot,if_true,PortFraction.value,Int.cast_sub,Int.cast_ofNat,
      threeInteriorRightRoot]
    rw [num,den,div_div_div_cancel_right₀ Gn]

theorem wordGammaEnd_value (c : ThreeInteriorCell) (w : ThreeInteriorWord) (b : Bool) :
    (wordGammaEnd c w b).value (K := K) =
      if w.port.side then
        threeInteriorRightGamma (portDensityEnd c (!b))
          (portCageEnd c w (!b) (.inr (portStop w.port)))
      else
        threeInteriorLeftGamma (portDensityEnd c (!b))
          (portCageEnd c w b (.inr (portStop w.port))) := by
  have hp : (portDensityDen c : K) ≠ 0 := by unfold portDensityDen; positivity
  simp only [wordGammaEnd,portDensityEnd,portCageEnd,gridCoord]
  rw [homogeneousGamma_value w.port.side (by simpa only [Int.cast_natCast] using hp)]
  cases hs : w.port.side <;> simp [hs]

theorem wordRootEnd_value (c : ThreeInteriorCell) (w : ThreeInteriorWord)
    (j : Fin w.port.count) (b : Bool) :
    (wordRootEnd c w j b).value (K := K) =
      if w.port.side then threeInteriorRightRoot
        (portCageEnd c w (!b) (.inr (portStop w.port))) (portCageEnd c w b (portFactorSite w.port j))
      else threeInteriorLeftRoot
        (portCageEnd c w (!b) (.inr (portStop w.port))) (portCageEnd c w b (portFactorSite w.port j)) := by
  simp only [wordRootEnd,homogeneousRoot_value,portCageEnd,gridCoord,Int.cast_natCast] <;> norm_num

theorem portCage_actual {c : ThreeInteriorCell} {w : ThreeInteriorWord}
    {r : Fin 3 → K} {m : Fin 4 → K} (h : c.contains (w.sites r m)) (a : ThreeInteriorSite) :
    threeInteriorSites r m a ∈ Set.Icc (portCageEnd c w false a) (portCageEnd c w true a) := by
  simpa only [portCageEnd,portCageIndex,Bool.cond_false,Bool.cond_true,ThreeInteriorCell.lowCoord,
    ThreeInteriorCell.highCoord,ThreeInteriorWord.sites,Function.comp_apply,word_label_at_rank]
    using h (wordSiteRank w a)

theorem actualLocalizerArgs_cons (p : ThreeInteriorPort) (s : K) (r : Fin 3 → K)
    (m : Fin 4 → K) :
    threeInteriorLocalizerArgs p s r m =
      Fin.cons
        (if p.side then threeInteriorRightGamma s (m (portStop p))
         else threeInteriorLeftGamma s (m (portStop p)))
        (fun j => if p.side then threeInteriorRightRoot (m (portStop p))
          (threeInteriorSites r m (portFactorSite p j))
         else threeInteriorLeftRoot (m (portStop p)) (threeInteriorSites r m (portFactorSite p j))) := by
  cases p <;> first | rfl | {
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun _ => rfl) j
  }

end OrderedField

end RKCert.ReviewedNative.ThreeInteriorPencil
