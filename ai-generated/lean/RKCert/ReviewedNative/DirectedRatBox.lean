module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

@[expose] public section

/-! Outward-rounded rational intervals and Horner evaluation, with a
soundness theorem over any ordered field. The kernel calculations use
rational endpoints with controlled denominators, not floating point. -/
namespace RKResearch.Certified.DirectedRatBox

structure Box where
  lo : ℚ
  hi : ℚ

def scale : ℚ := 10^130

theorem scale_pos : (0:ℚ) < scale := by
  unfold scale
  exact pow_pos (by decide +kernel) _

def down (x : ℚ) : ℚ := (Int.floor (scale*x) : ℚ) / scale
def up (x : ℚ) : ℚ := -down (-x)

theorem down_le (x : ℚ) : down x ≤ x := by
  rw [down, div_le_iff₀ scale_pos, mul_comm x scale]
  exact Int.floor_le _

theorem le_up (x : ℚ) : x ≤ up x := by
  simpa only [up, neg_neg] using neg_le_neg (down_le (-x))

def out (l u : ℚ) : Box := ⟨down l,up u⟩
def point (q : ℚ) : Box := ⟨q,q⟩
def ofRat (q : ℚ) : Box := out q q
def add (U V : Box) : Box := out (U.lo+V.lo) (U.hi+V.hi)
def neg (U : Box) : Box := ⟨-U.hi,-U.lo⟩
def sub (U V : Box) : Box := add U (neg V)
def mul (U V : Box) : Box :=
  out (min (min (U.lo*V.lo) (U.lo*V.hi)) (min (U.hi*V.lo) (U.hi*V.hi)))
      (max (max (U.lo*V.lo) (U.lo*V.hi)) (max (U.hi*V.lo) (U.hi*V.hi)))

def power (U : Box) : Nat → Box
  | 0 => point 1
  | k+1 => mul (power U k) U

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Encloses (U : Box) (x : K) : Prop := (U.lo:K) ≤ x ∧ x ≤ (U.hi:K)

theorem enclose_out {l u : ℚ} {x : K} (h : Encloses ⟨l,u⟩ x) :
    Encloses (out l u) x :=
  ⟨(Rat.cast_le.mpr (down_le l)).trans h.1,h.2.trans (Rat.cast_le.mpr (le_up u))⟩

omit [IsStrictOrderedRing K] in
theorem enclose_point (q : ℚ) : Encloses (point q) (q:K) := ⟨le_rfl,le_rfl⟩

theorem enclose_rat (q : ℚ) : Encloses (ofRat q) (q:K) :=
  enclose_out (enclose_point q)

theorem enclose_add {U V : Box} {x y : K} (hx : Encloses U x) (hy : Encloses V y) :
    Encloses (add U V) (x+y) := by
  apply enclose_out
  change (((U.lo+V.lo:ℚ):K) ≤ x+y) ∧ (x+y ≤ ((U.hi+V.hi:ℚ):K))
  simp only [Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem enclose_neg {U : Box} {x : K} (hx : Encloses U x) :
    Encloses (neg U) (-x) := by
  change (((-U.hi:ℚ):K) ≤ -x) ∧ (-x ≤ ((-U.lo:ℚ):K))
  simp only [Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem enclose_sub {U V : Box} {x y : K} (hx : Encloses U x) (hy : Encloses V y) :
    Encloses (sub U V) (x-y) := by
  rw [sub_eq_add_neg]
  exact enclose_add hx (enclose_neg hy)

theorem corners {a b c d x y : K} (hA : a ≤ x) (hB : x ≤ b) (hC : c ≤ y) (hD : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  let l := min (min (a*c) (a*d)) (min (b*c) (b*d))
  let u := max (max (a*c) (a*d)) (max (b*c) (b*d))
  have la : l ≤ a*c := (min_le_left _ _).trans (min_le_left _ _)
  have lb : l ≤ a*d := (min_le_left _ _).trans (min_le_right _ _)
  have lc : l ≤ b*c := (min_le_right _ _).trans (min_le_left _ _)
  have ld : l ≤ b*d := (min_le_right _ _).trans (min_le_right _ _)
  have ua : a*c ≤ u := (le_max_left _ _).trans (le_max_left _ _)
  have ub : a*d ≤ u := (le_max_right _ _).trans (le_max_left _ _)
  have uc : b*c ≤ u := (le_max_left _ _).trans (le_max_right _ _)
  have ud : b*d ≤ u := (le_max_right _ _).trans (le_max_right _ _)
  change l ≤ x*y ∧ x*y ≤ u
  rcases le_total (0:K) x with hp | hn
  · refine ⟨le_trans ?_ (mul_le_mul_of_nonneg_left hC hp), (mul_le_mul_of_nonneg_left hD hp).trans ?_⟩
    · rcases le_total (0:K) c with cp|cn
      · exact la.trans (mul_le_mul_of_nonneg_right hA cp)
      · exact lc.trans (mul_le_mul_of_nonpos_right hB cn)
    · rcases le_total (0:K) d with dp|dn
      · exact (mul_le_mul_of_nonneg_right hB dp).trans ud
      · exact (mul_le_mul_of_nonpos_right hA dn).trans ub
  · refine ⟨le_trans ?_ (mul_le_mul_of_nonpos_left hD hn), (mul_le_mul_of_nonpos_left hC hn).trans ?_⟩
    · rcases le_total (0:K) d with dp|dn
      · exact lb.trans (mul_le_mul_of_nonneg_right hA dp)
      · exact ld.trans (mul_le_mul_of_nonpos_right hB dn)
    · rcases le_total (0:K) c with cp|cn
      · exact (mul_le_mul_of_nonneg_right hB cp).trans uc
      · exact (mul_le_mul_of_nonpos_right hA cn).trans ua

theorem enclose_mul {U V : Box} {x y : K} (hx : Encloses U x) (hy : Encloses V y) :
    Encloses (mul U V) (x*y) := by
  apply enclose_out
  unfold Encloses
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact corners hx.1 hx.2 hy.1 hy.2

theorem enclose_pow {U : Box} {x : K} (hx : Encloses U x) (n : Nat) :
    Encloses (power U n) (x^n) := by
  induction n with
  | zero => simpa [power] using (enclose_point (K:=K) 1)
  | succ n ih =>
    rw [power,pow_succ]
    exact enclose_mul ih hx

theorem positive {U : Box} {x : K} (hx : Encloses U x) (h : 0 < U.lo) :
    0 < x := (Rat.cast_pos.mpr h).trans_le hx.1

theorem negative {U : Box} {x : K} (hx : Encloses U x) (h : U.hi < 0) :
    x < 0 := hx.2.trans_lt (Rat.cast_lt_zero.mpr h)

end

def horner {K : Type*} [Semiring K] : List K → K → K
  | [], _ => 0
  | a::as, x => a + x*horner as x

def hornerBox : List Box → Box → Box
  | [], _ => point 0
  | a::as, x => add a (mul x (hornerBox as x))

def ratHorner {K : Type*} [Field K] (coeff : List ℚ) (x : K) : K :=
  horner (coeff.map fun q : ℚ => (q:K)) x

def ratHornerBox (coeff : List ℚ) (x : Box) : Box :=
  hornerBox (coeff.map ofRat) x

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem horner_sound {BS : List Box} {cs : List K}
    (h : List.Forall₂ Encloses BS cs) {U : Box} {x : K} (hx : Encloses U x) :
    Encloses (hornerBox BS U) (horner cs x) := by
  induction h with
  | nil => simpa [horner,hornerBox] using (enclose_point (K:=K) 0)
  | cons hi hs ih =>
    exact enclose_add hi (enclose_mul hx ih)

omit [IsStrictOrderedRing K] in
theorem map_sound {L : Type*} {f : L → Box} {g : L → K}
    (e : ∀ t, Encloses (f t) (g t)) (l : List L) :
    List.Forall₂ Encloses (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons t l ih => exact .cons (e t) ih

theorem rat_horner_sound (l : List ℚ) {U : Box} {x : K} (hx : Encloses U x) :
    Encloses (ratHornerBox l U) (ratHorner l x) :=
  horner_sound (map_sound enclose_rat l) hx

end

end RKResearch.Certified.DirectedRatBox
