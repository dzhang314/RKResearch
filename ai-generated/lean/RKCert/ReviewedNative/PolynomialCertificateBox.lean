module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Finite boxes for separately affine tests

The box may have degenerate sides. Positivity at the finite vertex set is
strict everywhere, including all boundary faces. No topology is used. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Function
open scoped BigOperators

variable {K : Type*} [Field K]

def mix (a b t : K) : K := (1 - t) * a + t * b

/-- Affineness on replacing one coordinate, in an interface not requiring
a multivariate polynomial representation or a linearity side condition. -/
def SeparatelyAffine {n : ℕ} (f : (Fin n → K) → K) : Prop :=
  ∀ (x : Fin n → K) (i : Fin n) (a b t : K),
    f (update x i (mix a b t)) = mix (f (update x i a)) (f (update x i b)) t

/-- A predicate preserved by two-point convex combinations. -/
def MixClosed [LinearOrder K] (P : K → Prop) : Prop :=
  ∀ ⦃a b t : K⦄, 0 ≤ t → t ≤ 1 → P a → P b → P (mix a b t)

/-- A Boolean address selects the lower or upper end in each coordinate. -/
def vertex {n : ℕ} (l u : Fin n → K) (address : Fin n → Bool) : Fin n → K :=
  fun i => cond (address i) (u i) (l i)

private theorem vertex_cons {n : ℕ} (l u : Fin (n + 1) → K) (b : Bool)
    (address : Fin n → Bool) :
    vertex l u (Fin.cons b address) =
      Fin.cons (cond b (u 0) (l 0)) (vertex (Fin.tail l) (Fin.tail u) address) := by
  funext i
  cases i using Fin.cases <;> simp [vertex, Fin.tail]

theorem separatelyAffine_cons {n : ℕ} {f : (Fin (n + 1) → K) → K}
    (hf : SeparatelyAffine f) (a : K) :
    SeparatelyAffine (fun y => f (Fin.cons a y)) := by
  intro y i r s t
  simpa only [Fin.cons_update] using hf (Fin.cons a y) i.succ r s t

/-- Basic constructors for coefficient families on parameter boxes. -/
theorem separatelyAffine_const {n : ℕ} (c : K) :
    SeparatelyAffine (fun _ : Fin n → K => c) := by
  intro x i a b t
  unfold mix
  ring

theorem separatelyAffine_coordinate {n : ℕ} (j : Fin n) :
    SeparatelyAffine (fun x : Fin n → K => x j) := by
  intro x i a b t
  by_cases h : j = i
  · subst j
    simp only [update_self]
  · simp only [update_of_ne h, mix]
    ring

theorem SeparatelyAffine.add {n : ℕ} {f g : (Fin n → K) → K}
    (hf : SeparatelyAffine f) (hg : SeparatelyAffine g) :
    SeparatelyAffine (fun x => f x + g x) := by
  intro x i a b t
  change f (update x i (mix a b t)) + g (update x i (mix a b t)) = _
  rw [hf x i a b t, hg x i a b t]
  unfold mix
  ring

theorem SeparatelyAffine.sub {n : ℕ} {f g : (Fin n → K) → K}
    (hf : SeparatelyAffine f) (hg : SeparatelyAffine g) :
    SeparatelyAffine (fun x => f x - g x) := by
  intro x i a b t
  change f (update x i (mix a b t)) - g (update x i (mix a b t)) = _
  rw [hf x i a b t, hg x i a b t]
  unfold mix
  ring

theorem SeparatelyAffine.const_mul {n : ℕ} {f : (Fin n → K) → K}
    (hf : SeparatelyAffine f) (c : K) : SeparatelyAffine (fun x => c * f x) := by
  intro x i a b t
  change c * f (update x i (mix a b t)) = _
  rw [hf x i a b t]
  unfold mix
  ring

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem exists_unit_mix {l u x : K} (hx : x ∈ Set.Icc l u) :
    ∃ t : K, t ∈ Set.Icc 0 1 ∧ x = mix l u t := by
  by_cases e : l = u
  · have hxl : x = l := le_antisymm (by simpa only [← e] using hx.2) hx.1
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa [mix] using hxl⟩
  · have hlu : l < u := lt_of_le_of_ne (hx.1.trans hx.2) e
    have hu : 0 < u - l := sub_pos.mpr hlu
    let t := (x - l) / (u - l)
    have t0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) hu.le
    have t1 : t ≤ 1 := (div_le_iff₀ hu).2 (by simpa using sub_le_sub_right hx.2 l)
    have ht : (u - l) * t = x - l := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hu.ne'
    refine ⟨t, ⟨t0, t1⟩, ?_⟩
    calc
      x = l + (u - l) * t := by rw [ht]; ring
      _ = mix l u t := by unfold mix; ring

theorem mixClosed_lower (c : K) : MixClosed (fun x => c ≤ x) := by
  intro a b t t0 t1 ha hb
  calc
    c = mix c c t := by unfold mix; ring
    _ ≤ mix a b t :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr t1))
        (mul_le_mul_of_nonneg_left hb t0)

theorem mixClosed_upper (c : K) : MixClosed (fun x => x ≤ c) := by
  intro a b t t0 t1 ha hb
  calc
    mix a b t ≤ mix c c t :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr t1))
        (mul_le_mul_of_nonneg_left hb t0)
    _ = c := by unfold mix; ring

theorem mixClosed_strictLower (c : K) : MixClosed (fun x => c < x) := by
  intro a b t t0 t1 ha hb
  by_cases ht : t = 0
  · simpa [mix, ht] using ha
  · have tp : 0 < t := lt_of_le_of_ne t0 (Ne.symm ht)
    calc
      c = mix c c t := by unfold mix; ring
      _ < mix a b t :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr t1))
          (mul_lt_mul_of_pos_left hb tp)

theorem mixClosed_strictUpper (c : K) : MixClosed (fun x => x < c) := by
  intro a b t t0 t1 ha hb
  by_cases ht : t = 0
  · simpa [mix, ht] using ha
  · have tp : 0 < t := lt_of_le_of_ne t0 (Ne.symm ht)
    calc
      mix a b t < mix c c t :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr t1))
          (mul_lt_mul_of_pos_left hb tp)
      _ = c := by unfold mix; ring

theorem mixClosed_Icc (a b : K) : MixClosed (fun x => x ∈ Set.Icc a b) := by
  intro x y t t0 t1 hx hy
  exact ⟨mixClosed_lower a t0 t1 hx.1 hy.1, mixClosed_upper b t0 t1 hx.2 hy.2⟩

/-- A finite box inherits any mixture-closed assertion proved at its
vertices. The proof splits off one coordinate by exact interpolation. -/
theorem box_of_vertices {n : ℕ} {f : (Fin n → K) → K} (hf : SeparatelyAffine f)
    {l u x : Fin n → K} (hx : ∀ i, x i ∈ Set.Icc (l i) (u i))
    {P : K → Prop} (closed : MixClosed P)
    (corners : ∀ address : Fin n → Bool, P (f (vertex l u address))) : P (f x) := by
  induction n with
  | zero =>
      have h : x = vertex l u (fun _ => false) := funext fun i => Fin.elim0 i
      rw [h]
      exact corners _
  | succ n ih =>
      let y := Fin.tail x
      let l₀ := Fin.tail l
      let u₀ := Fin.tail u
      have hy : ∀ j, y j ∈ Set.Icc (l₀ j) (u₀ j) := fun j => hx j.succ
      have hL : P (f (Fin.cons (l 0) y)) := by
        apply ih (separatelyAffine_cons hf (l 0)) hy
        intro address
        simpa [vertex_cons, l₀, u₀] using corners (Fin.cons false address)
      have hU : P (f (Fin.cons (u 0) y)) := by
        apply ih (separatelyAffine_cons hf (u 0)) hy
        intro address
        simpa [vertex_cons, l₀, u₀] using corners (Fin.cons true address)
      obtain ⟨t, ht, ht0⟩ := exists_unit_mix (hx 0)
      have xcons : Fin.cons (mix (l 0) (u 0) t) y = x := by
        rw [← ht0]
        exact Fin.cons_self_tail x
      have hm : f x = mix (f (Fin.cons (l 0) y)) (f (Fin.cons (u 0) y)) t := by
        rw [← xcons]
        simpa only [Fin.update_cons_zero] using hf (Fin.cons (l 0) y) 0 (l 0) (u 0) t
      rw [hm]
      exact closed ht.1 ht.2 hL hU

theorem value_in_Icc_of_vertices {n : ℕ} {f : (Fin n → K) → K}
    (hf : SeparatelyAffine f) {l u x : Fin n → K}
    (hx : ∀ i, x i ∈ Set.Icc (l i) (u i)) {a b : K}
    (corners : ∀ address : Fin n → Bool, f (vertex l u address) ∈ Set.Icc a b) :
    f x ∈ Set.Icc a b :=
  box_of_vertices hf hx (mixClosed_Icc a b) corners

end Ordered

section Product

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The producer used by factored polynomial port tests: only one factor
depends on each variable, and the final functional is linear. -/
theorem separatelyAffine_linearMap_product {n : ℕ} (L : A →ₗ[K] K)
    (base : A) (f : Fin n → K → A)
    (hf : ∀ i a b t, f i (mix a b t) = (1 - t) • f i a + t • f i b) :
    SeparatelyAffine (fun x => L (base * ∏ j, f j (x j))) := by
  classical
  intro x i a b t
  let other := ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j)
  have prod_update (z : K) :
      (∏ j, f j ((update x i z) j)) = f i z * other := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun j => f j ((update x i z) j)) (Finset.mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [prod_update]
  rw [hf i]
  simp only [mix, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul]

end Product

end RKCert.ReviewedNative.PolynomialCertificate
