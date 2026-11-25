module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

@[expose] public section

/-! # A strict real cubic bracket without topology

The root is a supremum of the negative sublevel set. The only
regularity used is the elementary real-field difference bound below. -/
namespace RKCert.ReviewedNative.RealCubicOrderBracket

noncomputable section

/-- Ordinary power-basis evaluation; zero cubic coefficient is allowed. -/
def cubic (A B C D x : ℝ) : ℝ := A * x^3 + B * x^2 + C * x + D

private theorem prod_le_four {x y : ℝ}
    (hx : x ≤ 2) (hy0 : 0 ≤ y) (hy : y ≤ 2) : x * y ≤ 4 := by
  calc
    x * y ≤ (2 : ℝ) * 2 := mul_le_mul hx hy hy0 zero_le_two
    _ = 4 := by ring1

private theorem cubic_difference_bound (A B C D : ℝ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |cubic A B C D x - cubic A B C D y| ≤
      (12 * |A| + 4 * |B| + |C| + 1) * |x-y| := by
  let S : ℝ := x^2 + x*y + y^2
  let T : ℝ := x+y
  have xsq : x^2 ≤ 4 := by
    simpa only [pow_two] using (prod_le_four hx2 hx0 hx2)
  have ysq : y^2 ≤ 4 := by
    simpa only [pow_two] using (prod_le_four hy2 hy0 hy2)
  have xy : x*y ≤ 4 := prod_le_four hx2 hy0 hy2
  have s0 : 0 ≤ S :=
    add_nonneg (add_nonneg (sq_nonneg x) (mul_nonneg hx0 hy0)) (sq_nonneg y)
  have s12 : S ≤ 12 := by
    dsimp only [S]
    linarith only [xsq, xy, ysq]
  have t0 : 0 ≤ T := add_nonneg hx0 hy0
  have t4 : T ≤ 4 := by
    dsimp only [T]
    linarith only [hx2, hy2]
  have inner : |A*S+B*T+C| ≤ 12 * |A| + 4 * |B| + |C| + 1 := by
    calc
      |A*S+B*T+C| ≤ |A*S+B*T|+|C| := abs_add_le _ _
      _ ≤ (|A*S|+|B*T|)+|C| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = |A| * S + |B| * T + |C| := by
        simp only [abs_mul, abs_of_nonneg s0, abs_of_nonneg t0]
      _ ≤ |A| * 12 + |B| * 4 + |C| :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left s12 (abs_nonneg A))
            (mul_le_mul_of_nonneg_left t4 (abs_nonneg B))) le_rfl
      _ ≤ 12 * |A| + 4 * |B| + |C| + 1 := by linarith
  have factor :
      cubic A B C D x - cubic A B C D y = (x-y)*(A*S+B*T+C) := by
    dsimp only [cubic, S, T]
    ring1
  rw [factor, abs_mul]
  calc
    |x-y| * |A*S+B*T+C| ≤ |x-y| * (12 * |A| + 4 * |B| + |C| + 1) :=
      mul_le_mul_of_nonneg_left inner (abs_nonneg _)
    _ = _ := mul_comm _ _

private theorem exists_zero_of_order_bound (f : ℝ → ℝ) (M : ℝ) (Mpos : 0 < M)
    {l r : ℝ} (lr : l < r) (fl : f l < 0) (fr : 0 < f r)
    (bound : ∀ {x y : ℝ}, l ≤ x → x ≤ r → l ≤ y → y ≤ r →
      |f x - f y| ≤ M * |x-y|) :
    ∃ z ∈ Set.Ioo l r, f z = 0 := by
  let S : Set ℝ := {x | l ≤ x ∧ x ≤ r ∧ f x ≤ 0}
  have ls : l ∈ S := ⟨le_rfl, lr.le, fl.le⟩
  have sne : S.Nonempty := ⟨l, ls⟩
  have rightBound : ∀ x ∈ S, x ≤ r := by
    intro x hx
    change l ≤ x ∧ x ≤ r ∧ f x ≤ 0 at hx
    exact hx.2.1
  have sba : BddAbove S := ⟨r, by
    intro x hx
    exact rightBound x hx⟩
  let z : ℝ := sSup S
  have lz : l ≤ z := le_csSup sba ls
  have zr : z ≤ r := csSup_le sne rightBound
  have zzero : f z = 0 := by
    rcases lt_trichotomy (f z) 0 with zneg | hzero | zpos
    · exfalso
      have zlt : z < r := by
        apply lt_of_le_of_ne zr
        intro he
        have bad : f r < 0 := by simpa only [he] using zneg
        exact (not_lt_of_ge fr.le) bad
      have twicePos : 0 < (2 : ℝ)*M := mul_pos zero_lt_two Mpos
      let e : ℝ := min (r-z) ((-f z)/(2*M))
      have ep : 0 < e :=
        lt_min (sub_pos.mpr zlt) (div_pos (neg_pos.mpr zneg) twicePos)
      have ebound : e ≤ r-z := min_le_left _ _
      have ecap : e ≤ (-f z)/(2*M) := min_le_right _ _
      have above : l ≤ z+e := by linarith only [lz, ep]
      have below : z+e ≤ r := by linarith only [ebound]
      have halfBound : 2*(M*e) ≤ -f z := by
        calc
          2*(M*e) = e*(2*M) := by ring1
          _ ≤ -f z := (le_div_iff₀ twicePos).mp ecap
      have diff := bound above below lz zr
      rw [show (z+e)-z = e by ring1, abs_of_pos ep] at diff
      have fdiff : f (z+e)-f z ≤ M*e := (le_abs_self _).trans diff
      have fxneg : f (z+e) < 0 := by linarith only [fdiff, halfBound, zneg]
      have inS : z+e ∈ S := ⟨above, below, fxneg.le⟩
      have bad : z+e ≤ z := le_csSup sba inS
      linarith only [bad, ep]
    · exact hzero
    · exfalso
      let e : ℝ := f z / M
      have ep : 0 < e := div_pos zpos Mpos
      have drop : ∀ x ∈ S, x ≤ z-e := by
        intro x hx
        have xdata : l ≤ x ∧ x ≤ r ∧ f x ≤ 0 := hx
        have xz : x ≤ z := le_csSup sba hx
        have diff := bound lz zr xdata.1 xdata.2.1
        rw [abs_of_nonneg (sub_nonneg.mpr xz)] at diff
        have fdiff : f z - f x ≤ M*(z-x) := (le_abs_self _).trans diff
        have low : f z ≤ f z - f x := by linarith only [xdata.2.2]
        have e_le : e ≤ z-x := by
          change f z / M ≤ z-x
          apply (div_le_iff₀ Mpos).mpr
          rw [mul_comm (z-x) M]
          exact low.trans fdiff
        linarith only [e_le]
      have bad : z ≤ z-e := csSup_le sne drop
      linarith only [bad, ep]
  refine ⟨z, ⟨lt_of_le_of_ne lz ?_, lt_of_le_of_ne zr ?_⟩, zzero⟩
  · intro h
    exact fl.ne (by simpa only [← h] using zzero)
  · intro h
    exact fr.ne' (by simpa only [h] using zzero)

/-- A strict sign bracket for a real cubic on a subinterval of `[0,2]`.
Both sign orientations are allowed. The proof uses no topology. -/
theorem exists_strict_root (A B C D : ℝ) {l r : ℝ}
    (l0 : 0 ≤ l) (lr : l < r) (r2 : r ≤ 2)
    (signs : (cubic A B C D l < 0 ∧ 0 < cubic A B C D r) ∨
      (0 < cubic A B C D l ∧ cubic A B C D r < 0)) :
    ∃ z ∈ Set.Ioo l r, cubic A B C D z = 0 := by
  let f := cubic A B C D
  let M : ℝ := 12 * |A| + 4 * |B| + |C| + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith only [abs_nonneg A, abs_nonneg B, abs_nonneg C]
  have fit {x y : ℝ} (hx : l ≤ x) (hx' : x ≤ r) (hy : l ≤ y) (hy' : y ≤ r) :
      |f x - f y| ≤ M * |x-y| :=
    cubic_difference_bound A B C D (l0.trans hx) (hx'.trans r2)
      (l0.trans hy) (hy'.trans r2)
  rcases signs with ⟨fl, fr⟩ | ⟨fl, fr⟩
  · exact exists_zero_of_order_bound f M hM lr fl fr @fit
  · have hfit {x y : ℝ} (hx : l ≤ x) (hx' : x ≤ r) (hy : l ≤ y) (hy' : y ≤ r) :
        |(-f x) - (-f y)| ≤ M * |x-y| := by
      rw [show (-f x)-(-f y) = -(f x-f y) by ring1, abs_neg]
      exact fit hx hx' hy hy'
    obtain ⟨z, hz, hz0⟩ := exists_zero_of_order_bound (fun x : ℝ => -f x)
      M hM lr (neg_lt_zero.mpr fl) (neg_pos.mpr fr) @hfit
    exact ⟨z, hz, by simpa only [f, neg_eq_zero] using hz0⟩

end
end RKCert.ReviewedNative.RealCubicOrderBracket