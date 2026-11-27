import Lean

/-!
# Exact moment and scalar gates for the rank-free ERK11 cutoff

Core Lean only. The companion proof supplies the actual rooted
word identities and physical support, and maps the scalar moment
arguments to the visible tail. These lemmas do not assert native
Runge–Kutta rank or a new ordinary stage floor.
-/
namespace RKResearch.ERK11RankFreeCutoffGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

private theorem powNz {a : K} (ha : a ≠ 0) : ∀ n : Nat, a^n ≠ 0
  | 0 => by rw [Semiring.pow_zero]; grind
  | n+1 => by rw [Semiring.pow_succ]; exact nzMul (powNz ha n) ha

private theorem zeroPos (n : Nat) (h : 0 < n) : (0:K)^n=0 := by
  cases n with
  | zero => omega
  | succ n => rw [Semiring.pow_succ,Semiring.mul_zero]

/-- Actual charges after grouping by clock. No positivity of charges is used. -/
def moment (k : Nat) (charge : K → K) : List K → K
  | [] => 0
  | x::xs => charge x*x^k + moment k charge xs

theorem zeroChargeMoment (k : Nat) (charge : K → K) (xs : List K)
    (zero : ∀ x, x∈xs → charge x=0) : moment k charge xs=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := zero x List.mem_cons_self
    have hh := ih (fun y ym => zero y (List.mem_cons_of_mem x ym))
    simp only [moment,hx,hh,Semiring.zero_mul,AddCommMonoid.zero_add]

theorem tiltMoment (p : K) (k : Nat) (charge : K → K) (xs : List K) :
    moment k (fun x => (x-p)*charge x) xs =
      moment (k+1) charge xs - p*moment k charge xs := by
  induction xs with
  | nil => simp only [moment,Semiring.mul_zero,AddCommGroup.sub_self]
  | cons x xs ih =>
    simp only [moment,Semiring.pow_succ,ih]
    grind

theorem removeClockMoment (p : K) (k : Nat) (charge : K → K) (xs : List K) :
    moment k (fun x => (x-p)*charge x) xs =
      moment (k+1) charge (p::xs) - p*moment k charge (p::xs) := by
  rw [tiltMoment]
  simp only [moment,Semiring.pow_succ]
  grind

/-- Consecutive zero moments give an exact Vandermonde elimination.
The start exponent may be zero. At a positive start, the nonzero-clock
premise is recorded as invertibility of the lowest monomial factor. -/
theorem consecutiveVandermonde (k : Nat) (xs : List K) (charge : K → K)
    (distinct : xs.Pairwise (fun a b : K => a ≠ b))
    (powers : ∀ x, x∈xs → x^k ≠ 0)
    (zero : ∀ i : Nat, i<xs.length → moment (k+i) charge xs=0) :
    ∀ x, x∈xs → charge x=0 := by
  induction xs generalizing charge with
  | nil => intro x e; simp at e
  | cons p xs ih =>
    let masked : K → K := fun x => (x-p)*charge x
    have dz : ∀ i : Nat, i<xs.length → moment (k+i) masked xs=0 := by
      intro i hi
      have e1 := zero (i+1) (by simp only [List.length_cons]; omega)
      have e0 := zero i (by simp only [List.length_cons]; omega)
      rw [show k+(i+1)=(k+i)+1 by omega] at e1
      change moment (k+i) (fun x => (x-p)*charge x) xs=0
      rw [removeClockMoment,e1,e0,Semiring.mul_zero,AddCommGroup.sub_self]
    have ds := List.pairwise_cons.mp distinct
    have killed := ih masked ds.2 (fun y ym => powers y (List.mem_cons_of_mem p ym)) dz
    have tail : ∀ x, x∈xs → charge x=0 := by
      intro x xm
      have dn : x-p ≠ 0 := by
        intro e
        exact ds.1 x xm (AddCommGroup.sub_eq_zero_iff.mp e).symm
      exact (Field.of_mul_eq_zero (killed x xm)).resolve_left dn
    have head : charge p=0 := by
      have e := zero 0 (by simp)
      rw [Nat.add_zero,moment,zeroChargeMoment k charge xs tail,Semiring.add_zero] at e
      exact (Field.of_mul_eq_zero e).resolve_right (powers p List.mem_cons_self)
    intro x xm
    rcases List.mem_cons.mp xm with hh | ht
    · exact hh.symm ▸ head
    · exact tail x ht

/-- A pair of future physical coordinates cannot carry an earlier
positive moment after two consecutive later positive zeros, even
when their actual clocks coincide or are endpoints. -/
theorem twoFutureCharges (a b x y : K) (p q : Nat) (qpos : 0<q)
    (h0 : a*x^p + b*y^p=0) (h1 : a*x^(p+1)+b*y^(p+1)=0) :
    a*x^q+b*y^q=0 := by
  by_cases xy : x=y
  · subst y
    by_cases xx : x=0
    · subst x
      rw [zeroPos q qpos,Semiring.mul_zero,Semiring.mul_zero,AddCommMonoid.zero_add]
    · have e : (a+b)*x^p=0 := by grind
      have f := (Field.of_mul_eq_zero e).resolve_right (powNz xx p)
      grind
  · have e : (b*y^p)*(y-x)=0 := by
      have v := congrArg (fun z => x*z) h0
      simp only [Semiring.pow_succ] at h1
      grind
    have ne : y-x ≠ 0 := by
      intro w
      exact xy (AddCommGroup.sub_eq_zero_iff.mp w).symm
    have byp := (Field.of_mul_eq_zero e).resolve_right ne
    have axp : a*x^p=0 := by rw [byp,Semiring.add_zero] at h0; exact h0
    have axq : a*x^q=0 := by
      rcases Field.of_mul_eq_zero axp with az | px
      · simp only [az,Semiring.zero_mul]
      · have xx : x=0 := by
          by_cases xn : x=0
          · exact xn
          · exact False.elim (powNz xn p px)
        rw [xx,zeroPos q qpos,Semiring.mul_zero]
    have byq : b*y^q=0 := by
      rcases Field.of_mul_eq_zero byp with bz | py
      · simp only [bz,Semiring.zero_mul]
      · have yy : y=0 := by
          by_cases yn : y=0
          · exact yn
          · exact False.elim (powNz yn p py)
        rw [yy,zeroPos q qpos,Semiring.mul_zero]
    rw [axq,byq,AddCommMonoid.zero_add]

/-- Paid top-visible clock coefficients force the first response zero
when the final reflected clock is nonzero. -/
theorem topNonendpointFirstZero (y0 y1 y5 W T a d : K)
    (diff : y0 ≠ y1) (late : y5 ≠ 0) (top : T ≠ 0)
    (e0 : y0*W+a*T=0) (e1 : y1*W+d*T=0)
    (w0 : (a*y5)*T=0) (w1 : (d*y5)*T=0) : W=0 := by
  have aa := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero w0).resolve_right top)).resolve_right late
  have dd := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero w1).resolve_right top)).resolve_right late
  have ae : y0*W=0 := by
    simp only [aa,Semiring.zero_mul,Semiring.add_zero] at e0
    exact e0
  have de : y1*W=0 := by
    simp only [dd,Semiring.zero_mul,Semiring.add_zero] at e1
    exact e1
  by_cases R : W=0
  · exact R
  · have ra := (Field.of_mul_eq_zero ae).resolve_right R
    have rb := (Field.of_mul_eq_zero de).resolve_right R
    exact False.elim (diff (ra.trans rb.symm))

/-- A denominator-cleared reweighting cancels the sole nonzero
late coefficient in the chronological Krylov suffix. -/
theorem cancelKrylovRead {n : Nat} (b seed : Fin n → K)
    (pivot : Fin n) (scale : K) (atPivot : seed pivot=-(scale*b pivot))
    (zero : ∀ i, i≠pivot → b i=0 ∧ seed i=0) :
    ∀ i, scale*b i+seed i=0 := by
  intro i
  by_cases e : i=pivot
  · subst i
    rw [atPivot]
    grind
  · obtain ⟨h,q⟩ := zero i e
    rw [h,q,Semiring.mul_zero,AddCommMonoid.zero_add]

end RKResearch.ERK11RankFreeCutoffGate
#print axioms RKResearch.ERK11RankFreeCutoffGate.consecutiveVandermonde
#print axioms RKResearch.ERK11RankFreeCutoffGate.twoFutureCharges
#print axioms RKResearch.ERK11RankFreeCutoffGate.topNonendpointFirstZero
#print axioms RKResearch.ERK11RankFreeCutoffGate.cancelKrylovRead
