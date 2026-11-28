module
public import RKCert.ReviewedNative.DIRK12MidpointRealStarBridge
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! The ten literal real reflected support nodes of the positive
orientation lie in checked, pairwise disjoint rational boxes. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox Polynomial
open scoped Polynomial BigOperators

def sBox : Box := ⟨338/1000,339/1000⟩
def uBox : Box := ⟨621/1000,622/1000⟩
def rBox : Box := ⟨174/1000,175/1000⟩
def dBox : Box := mul (point (1/2)) (add sBox rBox)
def vBox : Box := mul (point (1/2)) (sub sBox rBox)
def discNumBox := mul (mul (point 12) (power EBox 2)) ABBox
def discDenBox := mul (power ABox 2) BBox

theorem between_div {p q : ℝ} {P Q : Box} {l u : ℚ}
    (hp : Encloses P p) (hq : Encloses Q q) (pos : 0 < q)
    (hL : 0 < (sub P (mul (point l) Q)).lo)
    (hU : 0 < (sub (mul (point u) Q) P).lo) :
    (l:ℝ) < p/q ∧ p/q < (u:ℝ) := by
  exact ⟨(lt_div_iff₀ pos).2 (sub_pos.mp (positive (enclose_sub hp
      (enclose_mul (enclose_point l) hq)) hL)),
    (div_lt_iff₀ pos).2 (sub_pos.mp (positive (enclose_sub
      (enclose_mul (enclose_point u) hq) hp) hU))⟩

section
variable {n : Fin 6 → ℝ}

theorem s_enclose (h : ∀ j, Encloses (bounds j) (n j)) : Encloses sBox (S n) := by
  have h6 : Encloses (point 6) (6:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 6
  have t := between_div (enclose_mul h6 (pE h)) (pA h) (all_pivots h).1
    (l:=sBox.lo) (u:=sBox.hi) (by decide +kernel) (by decide +kernel)
  exact ⟨t.1.le,t.2.le⟩

theorem u_enclose (h : ∀ j, Encloses (bounds j) (n j)) : Encloses uBox (U n) := by
  have t := between_div (pE h) (pC h) (all_pivots h).2.2.1
    (l:=uBox.lo) (u:=uBox.hi) (by decide +kernel) (by decide +kernel)
  exact ⟨t.1.le,t.2.le⟩

theorem sqrt_enclose (h : ∀ j, Encloses (bounds j) (n j)) :
    Encloses rBox (Real.sqrt ((S n)^2-4*P n)) := by
  obtain ⟨ha,hb,hc,he,hlab⟩ := all_pivots h
  have h12 : Encloses (point 12) (12:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 12
  have hNum : Encloses discNumBox (12*(ee n)^2*lab n) :=
    enclose_mul (enclose_mul h12 (enclose_pow (pE h) 2)) (pAB h)
  have hDen : Encloses discDenBox ((aa n)^2*bb n) :=
    enclose_mul (enclose_pow (pA h) 2) (pB h)
  have hB := between_div hNum hDen (mul_pos (pow_pos ha _) hb)
    (l:=rBox.lo^2) (u:=rBox.hi^2) (by decide +kernel) (by decide +kernel)
  have eq : (S n)^2-4*P n = 12*(ee n)^2*lab n/((aa n)^2*bb n) := by
    unfold S P
    field_simp [ha.ne',hb.ne']
    unfold aa bb
    ring
  rw [← eq] at hB
  push_cast at hB
  have square := Real.sq_sqrt (discriminant_pos h).le
  have nr : 0 ≤ Real.sqrt ((S n)^2-4*P n) := Real.sqrt_nonneg _
  have l : 0 ≤ (rBox.lo:ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have u : 0 ≤ (rBox.hi:ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  exact ⟨(sq_lt_sq₀ l nr).1 (hB.1.trans_eq square.symm) |>.le,
    ((sq_lt_sq₀ nr u).1 (square.trans_lt hB.2)).le⟩

end

noncomputable def dPlus (x f : ℝ) : ℝ :=
  let n := moments x f
  (S n+Real.sqrt ((S n)^2-4*P n))/2
noncomputable def dMinus (x f : ℝ) : ℝ :=
  let n := moments x f
  (S n-Real.sqrt ((S n)^2-4*P n))/2

theorem orientation_sum (x f : ℝ) : dPlus x f+dMinus x f=S (moments x f) := by
  unfold dPlus dMinus
  ring

theorem orientation_prod (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    dPlus x f*dMinus x f=P (moments x f) := by
  have hh := Real.sq_sqrt (discriminant_pos (moments_enclosed hx hf)).le
  unfold dPlus dMinus
  dsimp
  nlinarith

theorem d_plus_enclose {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Encloses dBox (dPlus x f) := by
  have h := moments_enclosed hx hf
  have e := enclose_mul (enclose_point (K:=ℝ) (1/2)) (enclose_add (s_enclose h) (sqrt_enclose h))
  have adj : dPlus x f = ((1/2 : ℚ) : ℝ)*
      (S (moments x f)+Real.sqrt ((S (moments x f))^2-4*P (moments x f))) := by
    unfold dPlus
    push_cast
    ring
  rw [adj]
  exact e

theorem d_minus_enclose {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Encloses vBox (dMinus x f) := by
  have h := moments_enclosed hx hf
  have e := enclose_mul (enclose_point (K:=ℝ) (1/2)) (enclose_sub (s_enclose h) (sqrt_enclose h))
  have adj : dMinus x f = ((1/2 : ℚ) : ℝ)*
      (S (moments x f)-Real.sqrt ((S (moments x f))^2-4*P (moments x f))) := by
    unfold dMinus
    push_cast
    ring
  rw [adj]
  exact e

def outerFixed : List Box :=
  [point 0,point 1,point (1/2),⟨935/1000,936/1000⟩,⟨600/1000,601/1000⟩,
   ⟨831/1000,833/1000⟩,⟨765/1000,766/1000⟩]

theorem widen_fixed (j : Fin 7) :
    (outerFixed.get j).lo ≤ (fixedBoxes.get j).lo ∧
    (fixedBoxes.get j).hi ≤ (outerFixed.get j).hi := by
  fin_cases j <;> decide +kernel

def siteBoxes : List Box := outerFixed++[dBox,vBox,uBox]

noncomputable def siteList (x f : ℝ) : List ℝ :=
  fixed x f++[dPlus x f,dMinus x f,U (moments x f)]

noncomputable def site (x f : ℝ) (i : Fin 10) : ℝ := (siteList x f).get i

theorem site_enclosed {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (i : Fin 10) : Encloses (siteBoxes.get i) (site x f i) := by
  have hf0 (j : Fin 7) : Encloses (outerFixed.get j) ((fixed x f).get j) := by
    have h0 := (fixed_sound hx hf).get (i:=j.val) j.isLt j.isLt
    have h1 := widen_fixed j
    exact ⟨(Rat.cast_le.mpr h1.1).trans h0.1,h0.2.trans (Rat.cast_le.mpr h1.2)⟩
  fin_cases i
  · exact hf0 0
  · exact hf0 1
  · exact hf0 2
  · exact hf0 3
  · exact hf0 4
  · exact hf0 5
  · exact hf0 6
  · exact d_plus_enclose hx hf
  · exact d_minus_enclose hx hf
  · exact u_enclose (moments_enclosed hx hf)

theorem boxes_separate : ∀ i j : Fin 10, i ≠ j →
    (siteBoxes.get i).hi < (siteBoxes.get j).lo ∨
    (siteBoxes.get j).hi < (siteBoxes.get i).lo := by decide +kernel

theorem site_distinct {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Function.Injective (site x f) := by
  intro i j he
  by_contra ne
  have hi := site_enclosed hx hf i
  have hj := site_enclosed hx hf j
  rcases boxes_separate i j ne with g|g
  · exact (ne_of_lt ((hi.2.trans_lt (Rat.cast_lt.mpr g)).trans_le hj.1)) he
  · exact (ne_of_lt ((hj.2.trans_lt (Rat.cast_lt.mpr g)).trans_le hi.1)) he.symm

theorem hull_as_product {K : Type*} [Field K] (ls : List K) :
    hull ls = (ls.map fun r => X-C r).prod := by
  induction ls with
  | nil => simp [hull]
  | cons r rs ih => simp [hull,ih]

theorem support_nodal_eq (x f : ℝ) :
    Lagrange.nodal Finset.univ (site x f)=supportHull x f (dPlus x f) (dMinus x f) := by
  change Finset.prod (Finset.univ : Finset (Fin 10)) (fun i => X-C (site x f i)) = hull (siteList x f)
  rw [← Fin.prod_ofFn, hull_as_product]
  exact congrArg List.prod (List.ofFn_getElem_eq_map (siteList x f) (fun a : ℝ => X-C a))

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.site_distinct
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.support_nodal_eq
