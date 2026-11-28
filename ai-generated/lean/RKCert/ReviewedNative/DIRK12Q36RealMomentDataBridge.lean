module
public import RKCert.ReviewedNative.DIRK12Q36MomentReflect
public import RKCert.ReviewedNative.DIRK12Q36PackedGatesCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKResearch.Certified.DIRK12Q36Moments

open RKResearch.Certified
open IntegerPolyRootReplay IntegerPolyRootReplay.Packing
open DirectedRatBox DIRK12MidpointRealInterval MomentReflect

def denomOK (D : Nat) (l : List ℚ) : Bool := l.all (fun q => decide (q.den ∣ D))

theorem denomOK_correct {D : Nat} {l : List ℚ} (e : denomOK D l=true) :
    ∀ q∈l, q.den ∣ D := fun q h => of_decide_eq_true (List.all_eq_true.mp e q h)

theorem x_clear : Q=clearDen 1 xCoeffs := by decide +kernel
theorem y_clear : Y=clearDen dy yCoeffs := by decide +kernel
theorem t_clear : T=clearDen dt tCoeffs := by decide +kernel
theorem x_ok : denomOK 1 xCoeffs=true := by decide +kernel
theorem y_ok : denomOK dy yCoeffs=true := by decide +kernel
theorem t_ok : denomOK dt tCoeffs=true := by decide +kernel
theorem all_f_clear : fCoeffs.map (clearDen fd)=[F0,F1,F2,[(fd:Int)]] := by decide +kernel
theorem all_f_ok : fCoeffs.all (denomOK fd)=true := by decide +kernel
theorem fdNZ : (fd:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by decide +kernel)
theorem denNZ : (den:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by decide +kernel)

theorem q_at_real_root {x : ℝ} (hx : realX x=0) : eval Q x=0 := by
  rw [x_clear,eval_clearDen 1 _ _ (denomOK_correct x_ok)]
  exact mul_eq_zero_of_right _ hx

theorem horner_scale {K : Type*} [CommRing K] (c : K) (l : List K) (x : K) :
    horner (l.map fun k => c*k) x = c*horner l x := by
  induction l with
  | nil => simp [horner]
  | cons a b ih =>
    simp only [horner,List.map_cons,ih]
    ring

theorem f_at_real_root {x f : ℝ} (hf : realF x f=0) :
    eval F0 x+eval F1 x*f+eval F2 x*f^2+(fd:ℝ)*f^3=0 := by
  have e : fCoeffs.map (fun l => eval (clearDen fd l) x) =
      fCoeffs.map (fun l => (fd:ℝ)*ratHorner l x) := by
    apply List.map_congr_left
    intro l hl
    exact eval_clearDen fd l x (denomOK_correct (List.all_eq_true.mp all_f_ok l hl))
  have h := congrArg (List.map (fun p : ZP => eval p x)) all_f_clear
  rw [List.map_map] at h
  change fCoeffs.map (fun l => eval (clearDen fd l) x) = _ at h
  rw [e] at h
  have h' := congrArg (fun l : List ℝ => horner l f) h
  simp only [List.map_cons,List.map_nil,horner,eval,Int.cast_natCast,mul_zero,add_zero] at h'
  have eqMap : fCoeffs.map (fun l => (fd:ℝ)*ratHorner l x) =
      (fCoeffs.map (fun l => ratHorner l x)).map (fun k => (fd:ℝ)*k) := by
    rw [List.map_map]
    rfl
  have h0 : horner (fCoeffs.map (fun l => (fd:ℝ)*ratHorner l x)) f=0 := by
    rw [eqMap,horner_scale]
    exact mul_eq_zero_of_right _ hf
  rw [h0] at h'
  linear_combination -h'

def rawRoots : Input :=
  [(1,.atom []),(1,.atom [1]),(2,.atom [1]),(2,.atom [2,-1]),
   (2*dy,.minus (.atom [2*(dy:Int)]) (.atom Y)),
   (2*dt,.minus (.atom [2*(dt:Int)]) (.atom T))]

theorem rawRoots_length : rawRoots.length=6 := rfl
theorem native_den : denom rawRoots=den := by decide +kernel

theorem rootFits (x : ℝ) : List.Forall₂
    (fun f r => Packing.read x f.2 = (f.1:ℝ)*r) rawRoots (firstSix x) := by
  have yval := eval_clearDen dy yCoeffs x (denomOK_correct y_ok)
  have tval := eval_clearDen dt tCoeffs x (denomOK_correct t_ok)
  rw [← y_clear] at yval
  rw [← t_clear] at tval
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))
  all_goals
    simp [Packing.read,eval,yval,tval,Nat.cast_mul,Int.cast_mul] <;> ring

def lowAtom (j : Fin 5) : ZP :=
  match j.val with | 0 => nC0 | 1 => nC1 | 2 => nC2 | 3 => nC3 | _ => nC4

def slopeAtom (j : Fin 5) : ZP :=
  match j.val with | 0 => nX0 | 1 => nX1 | 2 => nX2 | 3 => nX3 | _ => nX4

def M0 (j : Fin 5) : Expr :=
  .minus (.atom (lowAtom j))
    (.minus (momentExpr rawRoots (j.val+1)) (momentExpr rawRoots j.val))

def M1 (j : Fin 5) : Expr :=
  .minus (.atom (slopeAtom j)) (momentExpr rawRoots j.val)

def MomentChecks : Prop :=
  (∀ j : Fin 5, Packing.read (base:Int) (M0 j)=0 ∧ bound (M0 j)<base) ∧
  (∀ j : Fin 5, Packing.read (base:Int) (M1 j)=0 ∧ bound (M1 j)<base)

theorem coefficient_eq {m : Expr}
    (hv : Packing.read (base:Int) m=0) (hb : bound m<base) (x : ℝ) :
    Packing.read x m=0 := by
  rw [← data_eval]
  apply eval_zero_at_all_of_packed ((data_bound m).trans_lt hb)
  rwa [data_eval]

theorem real_lin_value (cert : MomentChecks) (x f : ℝ) (j : Fin 5) :
    linEval x f (affine (lowAtom j) (slopeAtom j)) = (den:ℝ)*moment (fixed x f) j.val := by
  have g0 := coefficient_eq (cert.1 j).1 (cert.1 j).2 x
  have g1 := coefficient_eq (cert.2 j).1 (cert.2 j).2 x
  simp only [M0, M1, Packing.read,sub_eq_zero] at g0 g1
  change eval (lowAtom j) x+f*eval (slopeAtom j) x=_
  rw [g0,g1,← native_den]
  exact affine_read (rootFits x) j.val (by rw [rawRoots_length]; omega) f

end RKResearch.Certified.DIRK12Q36Moments
