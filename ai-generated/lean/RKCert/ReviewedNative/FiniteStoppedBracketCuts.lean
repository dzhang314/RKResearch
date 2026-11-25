module

public import RKCert.ReviewedNative.FiniteStoppedBracket
public import RKCert.ReviewedNative.OrderedSampleCutProducts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.FiniteStoppedBracket

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.RightPoleInterpolation RKCert.ReviewedNative.OrderedSampleCuts

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem cut_above (xs : List K) (x : K) (hx : ∀ c∈xs,c<x) :
    0<(cutProduct xs).eval x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [cutProduct_cons, eval_mul, eval_sub, eval_X, eval_C]
      exact mul_pos (sub_pos.mpr (hx a (by simp)))
        (ih (fun c hc=>hx c (List.mem_cons_of_mem _ hc)))

/-- The checked sign cuts may be fitted on an augmented list. Only the true
integration samples need appear to pass the two finite fit conditions. -/
theorem StopSeparator.of_split_cuts {P : K[X]} {t e : K} {xs L R : List K}
    (D : SplitCuts P t xs L R e) (t0 : 0<t) (t1 : t<1)
    (leftMem : ∀ i : Fin 19, intervalPoint 0 t i∈xs)
    (rightMem : ∀ i : Fin 19, intervalPoint t 1 i∈xs) :
    StopSeparator P 0 t 1 (e*(-1:K)^R.length) L R := by
  let σ : K := (-1)^R.length
  have ss : σ*σ=1 := by dsimp only [σ]; rw [←mul_pow]; norm_num
  refine ⟨(fun c hc=>(D.lower c hc).2), (fun c hc=>(D.upper c hc).1), ?_, ?_⟩
  · intro i live
    let x := intervalPoint 0 t i
    have xt : x<t := (intervalPoint_mem t0 i).2
    have rp : 0<(poleProduct R).eval x :=
      poleProduct_pos R x (fun a ha=>xt.trans (D.upper a ha).1)
    change 0<(e*σ)*P.eval x*(cutProduct L).eval x
    apply (mul_pos_iff_of_pos_right rp).mp
    rw [poleProduct_orientation]
    have shape : ((e*σ)*P.eval x*(cutProduct L).eval x)*
        ((-1:K)^R.length*(cutProduct R).eval x) =
        (σ*σ)*(P.eval x*cutValue e L R x) := by dsimp only [σ,cutValue]; ring
    rw [shape,ss,one_mul]
    exact D.fit x (leftMem i) live
  · intro i live
    let x := intervalPoint t 1 i
    have tx : t<x := (intervalPoint_mem t1 i).1
    have lp : 0<(cutProduct L).eval x :=
      cut_above L x (fun a ha=>(D.lower a ha).2.trans tx)
    change 0<((e*σ)*σ)*P.eval x*(cutProduct R).eval x
    apply (mul_pos_iff_of_pos_right lp).mp
    have shape : (((e*σ)*σ)*P.eval x*(cutProduct R).eval x)*(cutProduct L).eval x =
        (σ*σ)*(P.eval x*cutValue e L R x) := by unfold cutValue; ring
    rw [shape,ss,one_mul]
    exact D.fit x (rightMem i) live

/-- When the stop itself is an appended live sign sample, the same
orientation agrees strictly with its evaluated profile. -/
theorem split_cuts_stop_orientation {P : K[X]} {t e : K} {xs L R : List K}
    (D : SplitCuts P t xs L R e) (mem : t∈xs) (live : P.eval t≠0) :
    0<(e*(-1:K)^R.length)*P.eval t := by
  have lp : 0<(cutProduct L).eval t :=
    cut_above L t (fun a ha=>(D.lower a ha).2)
  have rp : 0<(poleProduct R).eval t :=
    poleProduct_pos R t (fun a ha=>(D.upper a ha).1)
  apply (mul_pos_iff_of_pos_right (mul_pos lp rp)).mp
  rw [poleProduct_orientation]
  have sq : (-1:K)^R.length * (-1:K)^R.length = 1 := by
    rw [←mul_pow]
    norm_num
  have shape : ((e*(-1:K)^R.length)*P.eval t)*
      ((cutProduct L).eval t*((-1:K)^R.length*(cutProduct R).eval t)) =
      ((-1:K)^R.length * (-1:K)^R.length)*(P.eval t*cutValue e L R t) := by
    unfold cutValue
    ring
  rw [shape,sq,one_mul]
  exact D.fit t mem live

end
end RKCert.ReviewedNative.FiniteStoppedBracket
