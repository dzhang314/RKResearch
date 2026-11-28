module

public import RKCert.ReviewedNative.DIRK12MidpointReversePhysical
public import RKCert.ReviewedNative.DIRK12MidpointOpeningFifth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual real guards for normalized reverse coefficients and physical
deweighting. Distinctness and signed nonzero weights are inherited from
the same algebraic root boxes, not asserted from numerical computation. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Actual

open RKResearch Graded DIRK12MidpointForward DIRK12MidpointForward.Opening
open DIRK12MidpointRealInterval DirectedRatBox
open scoped BigOperators Matrix

noncomputable def d (x f : ℝ) : ℝ := site x f 7
noncomputable def v (x f : ℝ) : ℝ := site x f 8
noncomputable def u (x f : ℝ) : ℝ := site x f 9
noncomputable def r (x f : ℝ) : ℝ := v x f/d x f
noncomputable def t (x f : ℝ) : ℝ := u x f/d x f

noncomputable def data (x f : ℝ) (h : Fin 6 → ℝ) : Physical.Data ℝ :=
  ⟨d x f,r x f,t x f,h⟩

theorem d_pos {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) : 0 < d x f := by
  exact positive (d_plus_enclose hx hf) (by decide +kernel)

theorem v_pos {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) : 0 < v x f := by
  exact positive (d_minus_enclose hx hf) (by decide +kernel)

theorem u_pos {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) : 0 < u x f := by
  exact positive (u_enclose (moments_enclosed hx hf)) (by decide +kernel)

theorem ratio_bounds {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    (31/100:ℝ)<r x f ∧ r x f < (33/100:ℝ) := by
  have b := between_div (d_minus_enclose hx hf) (d_plus_enclose hx hf) (d_pos hx hf)
    (l:=31/100) (u:=33/100) (by decide +kernel) (by decide +kernel)
  change (31/100:ℝ)<dMinus x f/dPlus x f ∧ dMinus x f/dPlus x f<(33/100:ℝ)
  norm_num at b
  exact b

theorem ratio_guards {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    r x f≠0 ∧ r x f≠1 ∧ r x f≠2 ∧ 2*r x f≠1 ∧
    (r x f)^2-4*r x f+1≠0 ∧ 5*(r x f)^2-14*r x f+5≠0 ∧
    r x f+1≠0 ∧ (r x f)^2-r x f+1≠0 := by
  obtain ⟨lo,hi⟩ := ratio_bounds hx hf
  have a : (r x f)^2 < (33/100:ℝ)^2 := by
    have v0 : 0≤r x f := by linarith
    exact (sq_lt_sq₀ v0 (by norm_num)).2 hi
  have b := sq_nonneg (r x f)
  have c := sq_nonneg (r x f-1/2)
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by nlinarith⟩

theorem state_guards {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    t x f≠0 ∧ t x f≠1 ∧ t x f≠r x f := by
  have dn := (d_pos hx hf).ne'
  have un := (u_pos hx hf).ne'
  refine ⟨div_ne_zero un dn,?_ ,?_⟩
  · intro e
    have R := (div_eq_iff dn).1 e
    have q : (9:Fin 10)=(7:Fin 10) := site_distinct hx hf (by simpa [d,u] using R)
    exact (by decide : (9:Fin 10)≠7) q
  · intro e
    have R := (div_left_inj₀ dn).1 e
    have q : (9:Fin 10)=(8:Fin 10) := site_distinct hx hf R
    exact (by decide : (9:Fin 10)≠8) q

theorem real_geom (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (h : Fin 6 → ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Physical.Geom (realFeed x f alpha mu nu L) (data x f h) := by
  have dn := (d_pos hx hf).ne'
  obtain ⟨r0,r1,r2,_,_,_,_,_⟩ := ratio_guards hx hf
  obtain ⟨t0,t1,tr⟩ := state_guards hx hf
  refine ⟨dn,r0,r1,r2,t0,t1,tr,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    apply real_weight_guard x f alpha mu nu L hx hf
    exact non_ghost_visible j
  · rfl
  · exact real_ghost_weights x f alpha mu nu L
  · intro s
    rw [Feed.clocks_visible]
    fin_cases s
    · change 1-(1-u x f)=d x f*(u x f/d x f)
      rw [←mul_div_assoc,mul_div_cancel_left₀ _ dn]
      ring
    · change 1-(1-d x f)=d x f*1
      ring
    · change 1-(1-v x f)=d x f*(v x f/d x f)
      rw [←mul_div_assoc,mul_div_cancel_left₀ _ dn]
      ring
    · change 1-(1-d x f)=d x f*1
      ring
  · exact literal_terminal_clock x f alpha mu nu L
  · rfl
  · rfl

/-- The installed physical extension of the verified five opening
rows, still parameterized by a normalized grouped profile. -/
noncomputable def installed (x f : ℝ) (h : Fin 6 → ℝ) : Feed ℝ :=
  Physical.feed (fiveFeed x f (fun _ _ => 0)) (data x f h)

theorem installed_geom (x f : ℝ) (h : Fin 6 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Physical.Geom (fiveFeed x f (fun _ _ => 0)) (data x f h) :=
  real_geom x f _ _ _ _ h hx hf

theorem installed_pair (x f : ℝ) (h : Fin 6 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) :
    let P := fiveFeed x f (fun _ _ => 0)
    let D := data x f h
    mat (installed x f h).tableau.transpose (Physical.G P D)=
      (d x f/2) • Physical.G P D+Physical.H P D :=
  Physical.actual_pair_adjoint _ _ (installed_geom x f h hx hf)

end RKResearch.Certified.DIRK12MidpointReverse.Actual

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.ratio_guards
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.installed_geom
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Actual.installed_pair
