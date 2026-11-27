module

public import RKCert.ReviewedNative.DIRKRealRootParameters
public import RKCert.ReviewedNative.PolynomialBracket
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact real specialization of the degree-18 replay data using
strict rational sign changes. No approximation of an algebraic node
enters the proof. -/
namespace RKResearch.Certified.DIRKRealOrderTenRoots
open DIRKRealOrderTenData CubicCubicQuadraticRatReplay
open CubicCubicQuadraticReplay (v2 v3)
open RKCert.ReviewedNative.PolynomialBracket

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem realMap (x : ℚ) : (algebraMap ℚ ℝ) x = (x : ℝ) := rfl

noncomputable def innerCoeffs : List ℝ := [1314/125, -87/125, -4/5, 1]

noncomputable def suffix (x : ℝ) : List ℝ :=
  [-val3 x reductions.middle.1, -val3 x reductions.middle.2.1,
   -val3 x reductions.middle.2.2,1]

theorem inner_eval (x : ℝ) :
    horner innerCoeffs x = x^3 - val3 x reductions.inner := by
  norm_num [innerCoeffs, horner, val3, v3, reductions, realMap, Rat.mkRat_eq_div]
  ring

theorem suffix_eval (x y : ℝ) :
    horner (suffix x) y = y^3 - val9 x y reductions.middle := by
  simp only [suffix,horner,val9,v3,add_zero,mul_zero]
  ring

theorem horner_neg (cs : List ℝ) (x : ℝ) :
    horner (cs.map Neg.neg) x = -(horner cs x) := by
  induction cs with
  | nil => simp [horner]
  | cons a cs ih => simp only [List.map_cons,horner,ih]; ring

theorem exists_inner :
    ∃ x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000),
      x^3=val3 x reductions.inner := by
  obtain ⟨x,hx,hx0⟩ := exists_real_horner_root
    (lo := (-204748/100000 : ℝ)) (hi := (-204747/100000 : ℝ))
    (B:=3) (by norm_num) (by norm_num) (by norm_num) innerCoeffs
    (by norm_num [innerCoeffs,horner]) (by norm_num [innerCoeffs,horner])
  exact ⟨x,hx,sub_eq_zero.mp ((inner_eval x).symm.trans hx0)⟩

def sign_loleft : List ℚ := [(mkRat (-24661656226467189510029791451747) 83838575319835603901109000000000000),(mkRat (28900594885094837514553997) 946882733024025644059584000000),(mkRat (23200734722033924402969309) 402425161535210898725323200000)]

theorem suffix_sign_loleft {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    horner (suffix x) (6377/10000) < 0 := by
  have hL : (204747/100000 : ℝ) ≤ -x := by
    have hh := hx.2
    norm_num at hh ⊢
    linarith
  have hU : -x ≤ (204748/100000 : ℝ) := by
    have hh := hx.1
    norm_num at hh ⊢
    linarith
  have hPos := horner_pos_of_box
    (lo := (204747/100000 : ℚ)) (hi := (204748/100000 : ℚ))
    (x := -x) (by norm_num) (by simpa using hL) (by simpa using hU)
    sign_loleft (by decide +kernel)
  have eq : horner (sign_loleft.map (Rat.castHom ℝ)) (-x) = -(horner (suffix x) (6377/10000)) := by
    norm_num [sign_loleft, suffix, horner, val3, v3, reductions, realMap,
      Rat.mkRat_eq_div]
    ring
  rw [eq] at hPos
  linarith only [hPos]

def sign_lowright : List ℚ := [(mkRat (41183787436701168651356806859) 146717506809712306826940750000000),(mkRat (-384142541978332129586411) 16570447827920448771042720000),(mkRat (-730211081568809667080959) 14084880653732381455386312000)]

theorem suffix_sign_lowright {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    0 < horner (suffix x) (6380/10000) := by
  have hL : (204747/100000 : ℝ) ≤ -x := by
    have hh := hx.2
    norm_num at hh ⊢
    linarith
  have hU : -x ≤ (204748/100000 : ℝ) := by
    have hh := hx.1
    norm_num at hh ⊢
    linarith
  have hPos := horner_pos_of_box
    (lo := (204747/100000 : ℚ)) (hi := (204748/100000 : ℚ))
    (x := -x) (by norm_num) (by simpa using hL) (by simpa using hU)
    sign_lowright (by decide +kernel)
  have eq : horner (sign_lowright.map (Rat.castHom ℝ)) (-x) = (horner (suffix x) (6380/10000)) := by
    norm_num [sign_lowright, suffix, horner, val3, v3, reductions, realMap,
      Rat.mkRat_eq_div]
    ring
  rw [eq] at hPos
  linarith only [hPos]

def sign_midleft : List ℚ := [(mkRat (-7414915689591858211747801125451) 4584922087803509588341898437500000),(mkRat (9451863194103930732997087) 34521766308167601606339000000),(mkRat (14888188255772994227007281) 58687002723884922730776300000)]

theorem suffix_sign_midleft {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    0 < horner (suffix x) (8664/10000) := by
  have hL : (204747/100000 : ℝ) ≤ -x := by
    have hh := hx.2
    norm_num at hh ⊢
    linarith
  have hU : -x ≤ (204748/100000 : ℝ) := by
    have hh := hx.1
    norm_num at hh ⊢
    linarith
  have hPos := horner_pos_of_box
    (lo := (204747/100000 : ℚ)) (hi := (204748/100000 : ℚ))
    (x := -x) (by norm_num) (by simpa using hL) (by simpa using hU)
    sign_midleft (by decide +kernel)
  have eq : horner (sign_midleft.map (Rat.castHom ℝ)) (-x) = (horner (suffix x) (8664/10000)) := by
    norm_num [sign_midleft, suffix, horner, val3, v3, reductions, realMap,
      Rat.mkRat_eq_div]
    ring
  rw [eq] at hPos
  linarith only [hPos]

def sign_midright : List ℚ := [(mkRat (9689304239950247402290500090779) 6113229450404679451122531250000000),(mkRat (-109797664903491111759188261) 414261195698011219276068000000),(mkRat (-86977693047410304422571109) 352122016343309536384657800000)]

theorem suffix_sign_midright {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    horner (suffix x) (8668/10000) < 0 := by
  have hL : (204747/100000 : ℝ) ≤ -x := by
    have hh := hx.2
    norm_num at hh ⊢
    linarith
  have hU : -x ≤ (204748/100000 : ℝ) := by
    have hh := hx.1
    norm_num at hh ⊢
    linarith
  have hPos := horner_pos_of_box
    (lo := (204747/100000 : ℚ)) (hi := (204748/100000 : ℚ))
    (x := -x) (by norm_num) (by simpa using hL) (by simpa using hU)
    sign_midright (by decide +kernel)
  have eq : horner (sign_midright.map (Rat.castHom ℝ)) (-x) = -(horner (suffix x) (8668/10000)) := by
    norm_num [sign_midright, suffix, horner, val3, v3, reductions, realMap,
      Rat.mkRat_eq_div]
    ring
  rw [eq] at hPos
  linarith only [hPos]

theorem exists_suffix_pair {x : ℝ}
    (hx : x ∈ Set.Ioo (-204748/100000 : ℝ) (-204747/100000)) :
    ∃ y z : ℝ, y ∈ Set.Ioo (6377/10000) (6380/10000) ∧
      z ∈ Set.Ioo (8664/10000) (8668/10000) ∧
      horner (suffix x) y=0 ∧ horner (suffix x) z=0 := by
  obtain ⟨y,hy,hy0⟩ := exists_real_horner_root
    (lo := (6377/10000 : ℝ)) (hi := (6380/10000 : ℝ))
    (B:=2) (by norm_num) (by norm_num) (by norm_num) (suffix x)
    (suffix_sign_loleft hx) (suffix_sign_lowright hx)
  obtain ⟨z,hz,hz0⟩ := exists_real_horner_root
    (lo := (8664/10000 : ℝ)) (hi := (8668/10000 : ℝ))
    (B:=2) (by norm_num) (by norm_num) (by norm_num) ((suffix x).map Neg.neg)
    (by rw [horner_neg]; linarith only [suffix_sign_midleft hx])
    (by rw [horner_neg]; linarith only [suffix_sign_midright hx])
  rw [horner_neg,neg_eq_zero] at hz0
  exact ⟨y,z,hy,hz,hy0,hz0⟩

theorem outer_eval (x y z : ℝ) :
    (z-y)*(z^2-val x y z reductions.outer) =
      horner (suffix x) z - horner (suffix x) y := by
  norm_num [val,v2,val9,val3,v3,suffix,horner,reductions,realMap,Rat.mkRat_eq_div]
  ring

theorem exists_roots : ∃ x y z : ℝ, Roots reductions x y z := by
  obtain ⟨x,hx,hx0⟩ := exists_inner
  obtain ⟨y,z,hy,hz,hy0,hz0⟩ := exists_suffix_pair hx
  have hne : z-y ≠ 0 := by
    have hy0 := hy.2
    have hz0 := hz.1
    intro eq
    linarith only [hy0,hz0,eq]
  have h2 := outer_eval x y z
  rw [hy0,hz0,sub_self] at h2
  exact ⟨x,y,z,⟨hx0,sub_eq_zero.mp ((suffix_eval x y).symm.trans hy0),
    sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)⟩⟩

end RKResearch.Certified.DIRKRealOrderTenRoots

#print axioms RKResearch.Certified.DIRKRealOrderTenRoots.exists_roots
