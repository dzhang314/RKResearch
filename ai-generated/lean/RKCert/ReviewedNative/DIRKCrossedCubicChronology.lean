module

public import RKCert.ReviewedNative.DIRKCrossedCubicPivot
public import RKCert.ReviewedNative.VolterraZeroBridge

@[expose] public section

/-! # Physical chronology of the crossed cubic pivots

The premise `PaidReads` states only the exact cleared literal mixed
reads. Their vanishing for overlapping supports is *proved* by the actual
causal action, while the scalar contradiction is imported separately.
No truncation of a nonzero forward contribution, full-rank weight
matrix, or reflected ordinary Runge–Kutta method is assumed.
-/
namespace RKResearch.Certified.Graded.CrossedCubicChronology
open Lean.Grind
open VolterraZeroBridge

section Ring
variable {K : Type} [CommRing K]

/-- Multiply an actual stage column by a literal clock power. -/
def clockPow (c v : Nat → K) (k : Nat) (i : Nat) : K := c i ^ k * v i

/-- Actual weighted row read, with any zero row coordinates preserved. -/
def observe (l v : Nat → K) (n : Nat) : K :=
  sumBefore (fun j => l j * v j) n

/-- A genuine leaf/primitive word between a fixed row and column. -/
def read (A : Nat → Nat → K) (c l v : Nat → K) (n j k : Nat) : K :=
  observe l (clockPow c (act A (clockPow c v j)) k) n

/-- The three families of evaluated words required at order ten. The
coefficients are cleared row by row, without any division. -/
structure PaidReads (A : Nat → Nat → K) (c l v : Nat → K) (n : Nat)
    (a b d : K) (M : Nat → K) : Prop where
  j0 : ∀ t, t ≤ 2 → 12 * read A c l v n 0 t =
    6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(d*M (t+4))
  j1 : ∀ t, 1 ≤ t → t ≤ 2 → 60 * read A c l v n 1 (t-1) =
    20*(a*M (t+2)) + 15*(b*M (t+3)) + 12*(d*M (t+4))
  j2 : 60 * read A c l v n 2 0 = 15*(a*M 4) + 12*(b*M 5) + 10*(d*M 6)

private theorem sumBefore_all_zero (f : Nat → K) (n : Nat)
    (h : ∀ j, j < n → f j=0) : sumBefore f n=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBefore,ih (fun j h' => h j (by omega)),h n (by omega)]
    grind only

private theorem act_zero_closed (A : Nat → Nat → K) (v : Nat → K) (i r : Nat)
    (hz : ∀ j, j<i → v j=0) (hd : A i i=0) (hr : r≤i) : act A v r=0 := by
  apply sumBefore_all_zero
  intro j hj
  by_cases hj' : j<i
  · rw [hz j hj']; grind only
  · have er : r=i := by omega
    have ej : j=i := by omega
    rw [er,ej,hd]; grind only

/-- If the forward pivot is not earlier than the reverse pivot, every
literal mixed primitive read vanishes by the strict causal cut. -/
theorem read_zero_of_crossed (A : Nat → Nat → K) (c l v : Nat → K)
    (n i r : Nat) (crossed : r≤i) (hd : A i i=0)
    (left : ∀ j, r<j → j<n → l j=0)
    (right : ∀ j, j<i → v j=0) (j k : Nat) :
    read A c l v n j k=0 := by
  apply sumBefore_all_zero
  intro w wn
  change l w * (c w ^ k * act A (clockPow c v j) w)=0
  by_cases ht : r<w
  · rw [left w ht wn]; grind only
  · have hz : act A (clockPow c v j) w=0 := by
      apply act_zero_closed A _ i w _ hd (by omega)
      intro t ht
      rw [clockPow,right t ht]; grind only
    rw [hz]; grind only


private theorem sumBefore_single (f : Nat → K) (n i : Nat) (paid : i<n)
    (h : ∀ j, j<n → j≠i → f j=0) : sumBefore f n=f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBefore]
    by_cases hi : i=n
    · subst i
      rw [sumBefore_all_zero f n (fun j hj => h j (by omega) (by omega))]
      grind only
    · rw [ih (by omega) (fun j hj hn => h j (by omega) hn),
        h n (by omega) (Ne.symm hi)]
      grind only

private theorem act_one_open (A : Nat → Nat → K) (v : Nat → K) (i : Nat)
    (hz : ∀ j, j<i → v j=0) (hd : A (i+1) (i+1)=0) :
    act A v (i+1)=A (i+1) i * v i := by
  apply sumBefore_single _ (i+2) i (by omega)
  intro j hj hji
  by_cases h : j<i
  · rw [hz j h]; grind only
  · have he : j=i+1 := by omega
    rw [he,hd]; grind only

/-- An adjacent pair of explicit support boundaries has just one
possible A-tap between them. -/
theorem read_adjacent (A : Nat → Nat → K) (c l v : Nat → K)
    (n i : Nat) (paid : i+1<n) (hd : A i i=0) (hr : A (i+1) (i+1)=0)
    (left : ∀ j, i+1<j → j<n → l j=0)
    (right : ∀ j, j<i → v j=0) (j k : Nat) :
    read A c l v n j k =
      l (i+1)*(c (i+1)^k*(A (i+1) i*(c i^j*v i))) := by
  let w := clockPow c v j
  have hz : ∀ u, u<i → w u=0 := by
    intro u hu
    simp only [w,clockPow,right u hu,Semiring.mul_zero]
  have he : observe l (clockPow c (act A w) k) n =
      l (i+1) * clockPow c (act A w) k (i+1) := by
    apply sumBefore_single _ n (i+1) paid
    intro z zn he
    by_cases zhi : i+1<z
    · rw [left z zhi zn]; grind only
    · have hh : z≤i := by omega
      rw [clockPow,act_zero_closed A w i z hz hd hh]; grind only
  rw [show read A c l v n j k=observe l (clockPow c (act A w) k) n from rfl,he]
  rw [clockPow,act_one_open A w i hz hr]
  rfl

private theorem tests_of_all_zero (A : Nat → Nat → K) (c l v : Nat → K)
    (n : Nat) (a b d : K) (M : Nat → K) (P : PaidReads A c l v n a b d M)
    (Z : ∀ j k, read A c l v n j k=0) :
    CrossedCubicPivot.Tests a b d M := by
  constructor
  · intro t ht
    have p := P.j0 t ht
    rw [Z] at p
    grind only
  · intro t lo hi
    have p := P.j1 t lo hi
    rw [Z] at p
    grind only
  · have p := P.j2
    rw [Z] at p
    grind only

end Ring

section Field
variable {K : Type} [Field K]

/-- A forward cubic seed and reverse endpoint-factored cubic seed
must leave a strictly nonempty chronological interval for an A-tap.
The endpoints are physical indices, with no synthetic rearrangement. -/
theorem pivots_separate (A : Nat → Nat → K) (c l v : Nat → K)
    (n i r : Nat) (hd : A i i=0)
    (left : ∀ j, r<j → j<n → l j=0)
    (right : ∀ j, j<i → v j=0) (mu : Nat → K)
    (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1))*mu t=1)
    (a b d h f g : K) (front : a≠0 ∨ b≠0 ∨ d≠0) (back : h≠0 ∨ f≠0 ∨ g≠0)
    (P : PaidReads A c l v n a b d (CrossedCubicPivot.moment mu h f g)) :
    i<r := by
  by_cases ht : i<r
  · exact ht
  · have Z := read_zero_of_crossed A c l v n i r (by omega) hd left right
    have contradiction := CrossedCubicPivot.no_crossed mu pay a b d h f g front
      (tests_of_all_zero A c l v n a b d _ P Z)
    rcases back with a | b | c
    · exact False.elim (a contradiction.1)
    · exact False.elim (b contradiction.2.1)
    · exact False.elim (c contradiction.2.2)


/-- Adjacent separated pivots need a live tap and the *same* clock.
Otherwise either the mixed reads or the first Volterra pivot fails. -/
theorem adjacent_tap_and_clock (A : Nat → Nat → K) (c l v : Nat → K)
    (n i : Nat) (paid : i+1<n) (hd : A i i=0) (hr : A (i+1) (i+1)=0)
    (left : ∀ j, i+1<j → j<n → l j=0)
    (right : ∀ j, j<i → v j=0) (live : v i≠0) (kernel : vol A c v (i+1)=0)
    (mu : Nat → K) (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1))*mu t=1)
    (a b d h f g : K) (front : a≠0 ∨ b≠0 ∨ d≠0) (back : h≠0 ∨ f≠0 ∨ g≠0)
    (P : PaidReads A c l v n a b d (CrossedCubicPivot.moment mu h f g)) :
    A (i+1) i ≠ 0 ∧ c (i+1)=c i := by
  have tap : A (i+1) i ≠ 0 := by
    intro ht
    have Z (j k : Nat) : read A c l v n j k=0 := by
      rw [read_adjacent A c l v n i paid hd hr left right,ht]
      grind only
    have contradiction := CrossedCubicPivot.no_crossed mu pay a b d h f g front
      (tests_of_all_zero A c l v n a b d _ P Z)
    rcases back with a | b | c
    · exact a contradiction.1
    · exact b contradiction.2.1
    · exact c contradiction.2.2
  have hk := kernel
  rw [vol_one A c v right,hd,hr] at hk
  have zero : (A (i+1) i * (c (i+1)-c i)) * v i=0 := by grind only
  have mid := (Field.of_mul_eq_zero zero).resolve_right live
  have diff := (Field.of_mul_eq_zero mid).resolve_left tap
  exact ⟨tap,by grind only⟩

end Field
end RKResearch.Certified.Graded.CrossedCubicChronology
