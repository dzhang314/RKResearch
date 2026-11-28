module

public import RKCert.ReviewedNative.DIRK12MidpointMomentBounds
public import RKCert.ReviewedNative.DIRK12MidpointRealRoots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Directed boxes for the named midpoint support moments and the first
unpaid scalar condition. The range check clears all moving denominators. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox

def moment {K : Type*} [Field K] : List K → Nat → K
  | [], j => ((1 / ((j+1 : Nat) : ℚ) : ℚ) : K)
  | r::rs, j => moment rs (j+1)-r*moment rs j

def momentBox : List Box → Nat → Box
  | [], j => ofRat (1 / ((j+1 : Nat) : ℚ))
  | r::rs, j => sub (momentBox rs (j+1)) (mul r (momentBox rs j))

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem moment_sound {R : List K} {L : List Box} (h : List.Forall₂ Encloses L R) (j : Nat) :
    Encloses (momentBox L j) (moment R j) := by
  induction h generalizing j with
  | nil => exact enclose_rat _
  | cons hw hs ih => exact enclose_sub (ih (j+1)) (enclose_mul hw (ih j))

def fixed (x f : K) : List K :=
  let a := ((1/2 : ℚ) : K)
  [0,1,a,1-a*x,1-a*(ratHorner yCoeffs x),1-a*(ratHorner tCoeffs x),1-f]

def fixedBoxes : List Box :=
  let a := ofRat (1/2)
  let b := point 1
  [point 0,b,a,sub b (mul a xBox),
    sub b (mul a (ratHornerBox yCoeffs xBox)),
    sub b (mul a (ratHornerBox tCoeffs xBox)),sub b fBox]

theorem fixed_sound {x f : K} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    List.Forall₂ Encloses fixedBoxes (fixed x f) := by
  have h0 : Encloses (point 0) (0:K) := by simpa only [Rat.cast_zero] using enclose_point (K:=K) 0
  have h1 : Encloses (point 1) (1:K) := by simpa only [Rat.cast_one] using enclose_point (K:=K) 1
  have ha := enclose_rat (K:=K) (1/2)
  exact .cons h0 (.cons h1 (.cons ha (.cons (enclose_sub h1 (enclose_mul ha hx))
    (.cons (enclose_sub h1 (enclose_mul ha (rat_horner_sound yCoeffs hx)))
    (.cons (enclose_sub h1 (enclose_mul ha (rat_horner_sound tCoeffs hx)))
    (.cons (enclose_sub h1 hf) .nil))))))

set_option maxHeartbeats 0
set_option maxRecDepth 16000

theorem checked_moment_bounds (j : Fin 6) :
    (bounds j).lo ≤ (momentBox fixedBoxes j.val).lo ∧
      (momentBox fixedBoxes j.val).hi ≤ (bounds j).hi := by
  fin_cases j <;> decide +kernel

def moments (x f : K) : Fin 6 → K := fun j => moment (fixed x f) j.val

theorem moments_enclosed {x f : K} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    ∀ j, Encloses (bounds j) (moments x f j) := by
  intro j
  have h := moment_sound (fixed_sound hx hf) j.val
  have hb := checked_moment_bounds j
  exact ⟨(Rat.cast_le.mpr hb.1).trans h.1,h.2.trans (Rat.cast_le.mpr hb.2)⟩

end Ordered

section Geometry

variable {K : Type*} [CommRing K]

def lab (n : Fin 6 → K) : K := n 0*n 2
def lbb (n : Fin 6 → K) : K := n 1*n 1
def aa (n : Fin 6 → K) : K := 9*lbb n-4*lab n
def bb (n : Fin 6 → K) : K := 3*lbb n-lab n
def cc (n : Fin 6 → K) : K := 3*lbb n-2*lab n
def ee (n : Fin 6 → K) : K := n 1*n 2
def den (n : Fin 6 → K) : K := aa n*bb n*cc n
def hom (n : Fin 6 → K) : K :=
  -13*(den n*n 5-ee n*(6*bb n*cc n+aa n*bb n)*n 4+
    3*(ee n)^2*(cc n+2*bb n)*n 3-3*(ee n)^3*n 2)

end Geometry

def ABox := sub (mul (point 9) (mul (bounds 1) (bounds 1))) (mul (point 4) (mul (bounds 0) (bounds 2)))
def BBox := sub (mul (point 3) (mul (bounds 1) (bounds 1))) (mul (bounds 0) (bounds 2))
def CBox := sub (mul (point 3) (mul (bounds 1) (bounds 1))) (mul (point 2) (mul (bounds 0) (bounds 2)))
def EBox := mul (bounds 1) (bounds 2)
def ABBox := mul (bounds 0) (bounds 2)
def denBox := mul (mul ABox BBox) CBox
def homBox :=
  mul (point (-13))
    (sub (add (sub (mul denBox (bounds 5))
      (mul (mul EBox (add (mul (mul (point 6) BBox) CBox) (mul ABox BBox))) (bounds 4)))
      (mul (mul (mul (point 3) (power EBox 2)) (add CBox (mul (point 2) BBox))) (bounds 3)))
      (mul (mul (point 3) (power EBox 3)) (bounds 2)))

def starLo : ℚ := 85680969483153 / 10^20
def starHi : ℚ := 85680969483154 / 10^20

theorem box_pivots : 0 < ABox.lo ∧ 0 < BBox.lo ∧ 0 < CBox.lo ∧ 0 < EBox.lo ∧ 0 < ABBox.lo := by
  decide +kernel
theorem box_star_lo : 0 < (sub homBox (mul (point starLo) denBox)).lo := by decide +kernel
theorem box_star_hi : 0 < (sub (mul (point starHi) denBox) homBox).lo := by decide +kernel

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : Fin 6 → K} (h : ∀ j, Encloses (bounds j) (n j))

include h in
theorem pA : Encloses ABox (aa n) := by
  unfold ABox aa lbb lab
  exact enclose_sub (enclose_mul (by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 9)
    (enclose_mul (h 1) (h 1))) (enclose_mul (by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 4)
    (enclose_mul (h 0) (h 2)))

include h in
theorem pB : Encloses BBox (bb n) := by
  unfold BBox bb lbb lab
  exact enclose_sub (enclose_mul (by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 3)
    (enclose_mul (h 1) (h 1))) (enclose_mul (h 0) (h 2))

include h in
theorem pC : Encloses CBox (cc n) := by
  unfold CBox cc lbb lab
  exact enclose_sub (enclose_mul (by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 3)
    (enclose_mul (h 1) (h 1))) (enclose_mul (by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 2)
    (enclose_mul (h 0) (h 2)))

include h in
theorem pE : Encloses EBox (ee n) := enclose_mul (h 1) (h 2)
include h in
theorem pAB : Encloses ABBox (lab n) := enclose_mul (h 0) (h 2)

include h in
theorem pDen : Encloses denBox (den n) :=
  enclose_mul (enclose_mul (pA h) (pB h)) (pC h)

include h in
theorem pHom : Encloses homBox (hom n) := by
  unfold hom homBox
  have m2 : Encloses (point 2) (2:K) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 2
  have m3 : Encloses (point 3) (3:K) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 3
  have m6 : Encloses (point 6) (6:K) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=K) 6
  have m13 : Encloses (point (-13)) (-13:K) := by
    simpa only [Rat.cast_neg,Rat.cast_ofNat] using enclose_point (K:=K) (-13)
  exact enclose_mul m13 (enclose_sub
    (enclose_add
      (enclose_sub (enclose_mul (pDen h) (h 5))
        (enclose_mul (enclose_mul (pE h) (enclose_add
          (enclose_mul (enclose_mul m6 (pB h)) (pC h)) (enclose_mul (pA h) (pB h)))) (h 4)))
      (enclose_mul (enclose_mul (enclose_mul m3 (enclose_pow (pE h) 2))
        (enclose_add (pC h) (enclose_mul m2 (pB h)))) (h 3)))
    (enclose_mul (enclose_mul m3 (enclose_pow (pE h) 3)) (h 2)))

include h in
theorem all_pivots :
    0 < aa n ∧ 0 < bb n ∧ 0 < cc n ∧ 0 < ee n ∧ 0 < lab n :=
  ⟨positive (pA h) box_pivots.1,positive (pB h) box_pivots.2.1,
   positive (pC h) box_pivots.2.2.1,positive (pE h) box_pivots.2.2.2.1,
   positive (pAB h) box_pivots.2.2.2.2⟩

include h in
theorem supportD_pos : 0 < den n := by
  obtain ⟨a,b,c,_,_⟩ := all_pivots h
  exact mul_pos (mul_pos a b) c

include h in
theorem homogeneous_range :
    (starLo:K) < hom n/den n ∧ hom n/den n < (starHi:K) := by
  have g := supportD_pos h
  refine ⟨(lt_div_iff₀ g).mpr ?_, (div_lt_iff₀ g).mpr ?_⟩
  · exact sub_pos.mp (positive (enclose_sub (pHom h)
      (enclose_mul (enclose_point starLo) (pDen h))) box_star_lo)
  · exact sub_pos.mp (positive (enclose_sub
      (enclose_mul (enclose_point starHi) (pDen h)) (pHom h)) box_star_hi)

def S (n : Fin 6 → K) : K := 6*ee n/aa n
def P (n : Fin 6 → K) : K := 3*(ee n)^2/(aa n*bb n)
def U (n : Fin 6 → K) : K := ee n/cc n

def scalarExpression (n : Fin 6 → K) : K :=
  -13*(n 5-(S n+U n)*n 4+(P n+S n*U n)*n 3-P n*U n*n 2)

include h in
theorem scalar_eq :
    scalarExpression n = hom n / den n := by
  obtain ⟨a,b,c,_,_⟩ := all_pivots h
  unfold scalarExpression S U P hom den
  field_simp [a.ne',b.ne',c.ne']
  ring

include h in
theorem discriminant_pos : 0 < (S n)^2-4*P n := by
  obtain ⟨a,b,_,e,ab⟩ := all_pivots h
  have eq : (S n)^2-4*P n = 12*(ee n)^2*lab n/((aa n)^2*bb n) := by
    unfold S P
    field_simp [a.ne',b.ne']
    unfold aa bb
    ring
  rw [eq]
  positivity

theorem midpoint_star_bounds {x f : K} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    (starLo:K) < scalarExpression (moments x f) ∧ scalarExpression (moments x f) < (starHi:K) := by
  rw [scalar_eq (moments_enclosed hx hf)]
  exact homogeneous_range (moments_enclosed hx hf)

end Ordered

theorem exists_real_orientations {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    ∃ d v : ℝ, d ≠ v ∧ d + v = S (moments x f) ∧ d * v = P (moments x f) := by
  let n := moments x f
  let u := √((S n)^2-4*P n)
  have hd := discriminant_pos (moments_enclosed hx hf)
  have hu : 0 < u := Real.sqrt_pos.2 hd
  have hh : u^2 = (S n)^2-4*P n := Real.sq_sqrt hd.le
  refine ⟨(S n+u)/2,(S n-u)/2,?_,by ring,?_⟩
  · intro eq
    linarith
  · nlinarith

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.midpoint_star_bounds
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_real_orientations
