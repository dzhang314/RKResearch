module

public import RKCert.ReviewedNative.DIRK12MidpointRealPhysicalWeights
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! The true denominator guards for terminal correction and deweighting:
the ten cardinal integrals are all nonzero at the isolated real support.
Only directed rational inequalities are computed. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox Polynomial
open scoped Polynomial BigOperators

def fineS : Box := ⟨338563414841/10^12,338563414842/10^12⟩
def fineU : Box := ⟨621050777002/10^12,621050777003/10^12⟩
def fineR : Box := ⟨174846987918/10^12,174846987919/10^12⟩
def fineD : Box := mul (point (1/2)) (add fineS fineR)
def fineV : Box := mul (point (1/2)) (sub fineS fineR)

set_option maxHeartbeats 0
set_option maxRecDepth 16000

private theorem fine_s {n : Fin 6 → ℝ} (h : ∀ j, Encloses (bounds j) (n j)) :
    Encloses fineS (S n) := by
  have h6 : Encloses (point 6) (6:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 6
  have t := between_div (enclose_mul h6 (pE h)) (pA h) (all_pivots h).1
    (l:=fineS.lo) (u:=fineS.hi) (by decide +kernel) (by decide +kernel)
  exact ⟨t.1.le,t.2.le⟩

private theorem fine_u {n : Fin 6 → ℝ} (h : ∀ j, Encloses (bounds j) (n j)) :
    Encloses fineU (U n) := by
  have t := between_div (pE h) (pC h) (all_pivots h).2.2.1
    (l:=fineU.lo) (u:=fineU.hi) (by decide +kernel) (by decide +kernel)
  exact ⟨t.1.le,t.2.le⟩

private theorem fine_r {n : Fin 6 → ℝ} (h : ∀ j, Encloses (bounds j) (n j)) :
    Encloses fineR (Real.sqrt ((S n)^2-4*P n)) := by
  obtain ⟨ha,hb,hc,he,hlab⟩ := all_pivots h
  have h12 : Encloses (point 12) (12:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 12
  have hNum : Encloses discNumBox (12*(ee n)^2*lab n) :=
    enclose_mul (enclose_mul h12 (enclose_pow (pE h) 2)) (pAB h)
  have hDen : Encloses discDenBox ((aa n)^2*bb n) :=
    enclose_mul (enclose_pow (pA h) 2) (pB h)
  have hB := between_div hNum hDen (mul_pos (pow_pos ha _) hb)
    (l:=fineR.lo^2) (u:=fineR.hi^2) (by decide +kernel) (by decide +kernel)
  have eq : (S n)^2-4*P n = 12*(ee n)^2*lab n/((aa n)^2*bb n) := by
    unfold S P
    field_simp [ha.ne',hb.ne']
    unfold aa bb
    ring
  rw [← eq] at hB
  push_cast at hB
  have sq := Real.sq_sqrt (discriminant_pos h).le
  have nr : 0 ≤ Real.sqrt ((S n)^2-4*P n) := Real.sqrt_nonneg _
  have l : 0 ≤ (fineR.lo:ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have u : 0 ≤ (fineR.hi:ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  exact ⟨((sq_lt_sq₀ l nr).1 (hB.1.trans_eq sq.symm)).le,
    ((sq_lt_sq₀ nr u).1 (sq.trans_lt hB.2)).le⟩

def fineFixed : List Box :=
  [point 0,point 1,point (1/2),
    ⟨935163423387/10^12,935163423388/10^12⟩,
    ⟨600005227335/10^12,600005227336/10^12⟩,
    ⟨831905816910/10^12,831905816911/10^12⟩,
    ⟨765227149711/10^12,765227149712/10^12⟩]

private theorem fixed_widen (j : Fin 7) :
    (fineFixed.get j).lo ≤ (fixedBoxes.get j).lo ∧
    (fixedBoxes.get j).hi ≤ (fineFixed.get j).hi := by
  fin_cases j <;> decide +kernel

def fineSite (j : Fin 10) : Box := (fineFixed++[fineD,fineV,fineU]).get j

private theorem fine_site_enclosed {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (j : Fin 10) : Encloses (fineSite j) (site x f j) := by
  have F (i : Fin 7) :
      Encloses (fineFixed.get i) ((fixed x f).get i) := by
    have h := (fixed_sound hx hf).get (i:=i.val) i.isLt i.isLt
    have q := fixed_widen i
    exact ⟨(Rat.cast_le.mpr q.1).trans h.1,h.2.trans (Rat.cast_le.mpr q.2)⟩
  have m := moments_enclosed hx hf
  have half : Encloses (point (1/2)) ((1/2:ℚ):ℝ) := enclose_point _
  fin_cases j
  · exact F 0
  · exact F 1
  · exact F 2
  · exact F 3
  · exact F 4
  · exact F 5
  · exact F 6
  · change Encloses fineD (dPlus x f)
    have e := enclose_mul half (enclose_add (fine_s m) (fine_r m))
    have eq : dPlus x f = ((1/2:ℚ):ℝ)*(S (moments x f)+
        Real.sqrt ((S (moments x f))^2-4*P (moments x f))) := by
      unfold dPlus
      push_cast
      ring
    rw [eq]
    exact e
  · change Encloses fineV (dMinus x f)
    have e := enclose_mul half (enclose_sub (fine_s m) (fine_r m))
    have eq : dMinus x f = ((1/2:ℚ):ℝ)*(S (moments x f)-
        Real.sqrt ((S (moments x f))^2-4*P (moments x f))) := by
      unfold dMinus
      push_cast
      ring
    rw [eq]
    exact e
  · exact fine_u m

def omitted {L : Type*} (c : Fin 10 → L) (j : Fin 10) : List L :=
  List.ofFn fun k : Fin 9 => c (j.succAbove k)

private theorem omit_sound {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (j : Fin 10) : List.Forall₂ Encloses (omitted fineSite j) (omitted (site x f) j) := by
  rw [List.forall₂_iff_get]
  constructor
  · simp [omitted]
  · intro i hi hj
    simpa only [omitted,List.get_eq_getElem,List.getElem_ofFn] using fine_site_enclosed hx hf
      (j.succAbove ⟨i,by simpa [omitted] using hi⟩)

def numeratorBox (j : Fin 10) : Box := momentBox (omitted fineSite j) 0

theorem numerator_sign (j : Fin 10) : (numeratorBox j).hi<0 ∨ 0<(numeratorBox j).lo := by
  fin_cases j
  · left; decide +kernel
  · right; decide +kernel
  · right; decide +kernel
  · left; decide +kernel
  · right; decide +kernel
  · right; decide +kernel
  · left; decide +kernel
  · left; decide +kernel
  · right; decide +kernel
  · right; decide +kernel

private theorem nodal_omitted (c : Fin 10 → ℝ) (j : Fin 10) :
    Lagrange.nodal (Finset.univ.erase j) c = hull (omitted c j) := by
  have e : (Finset.univ : Finset (Fin 10)).erase j = Finset.univ.map (Fin.succAboveEmb j) := by
    ext i
    simp [Fin.exists_succAbove_eq_iff]
  rw [e]
  unfold Lagrange.nodal
  rw [Finset.prod_map,← Fin.prod_ofFn,hull_as_product,omitted,List.map_ofFn]
  rfl

theorem cardinalWeight_nonzero {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (j : Fin 10) : cardinalWeight x f j ≠ 0 := by
  have e := moment_sound (omit_sound hx hf j) 0
  have h : moment (omitted (site x f) j) 0 ≠ 0 := by
    rcases numerator_sign j with n|p
    · exact (negative e n).ne
    · exact (positive e p).ne'
  have d := Lagrange.nodalWeight_ne_zero
    (Set.injOn_of_injective (site_distinct hx hf)) (Finset.mem_univ j)
  have integral_eq : integral (hull (omitted (site x f) j)) =
      moment (omitted (site x f) j) 0 := by
    simpa only [pow_zero,one_mul] using integral_hull (omitted (site x f) j) 0
  rw [cardinalWeight,Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ j),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ j),nodal_omitted,
    ← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,integral_eq]
  exact mul_ne_zero d h

theorem physicalWeight_nonzero {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (j : Fin 15) (hj : ¬ ghostRow j) : physicalWeight x f j ≠ 0 := by
  rw [physicalWeight,ite_eq_right hj]
  split
  · exact div_ne_zero (cardinalWeight_nonzero hx hf _) (by norm_num)
  · exact cardinalWeight_nonzero hx hf _

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.cardinalWeight_nonzero
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.physicalWeight_nonzero
