module

public import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Kernel certificates for integer polynomials at a known root

Check a polynomial congruence by one packed integer identity and a signed
coefficient bound. Quotient digits are recovered from integer arithmetic;
no external or compiler arithmetic is assumed. The reader accepts any
commutative ring and only asks that the modulus evaluate to zero. -/

namespace RKCert.ReviewedNative.IntegerHornerCertificate

/-- Ascending Horner coefficients. The arithmetic checker is independent
of the ordered-field existence proof and its heavier algebraic imports. -/
def horner {R : Type*} [Semiring R] : List R → R → R
  | [], _ => 0
  | c::cs, x => c+x*horner cs x

def coeval {R : Type*} [CommRing R] (a : List ℤ) (x : R) : R :=
  horner (a.map (Int.castRingHom R)) x

theorem coeval_cons {R : Type*} [CommRing R] (a : ℤ) (as : List ℤ) (x : R) :
    coeval (a::as) x = (a:R) + x*coeval as x := by
  simp only [coeval,List.map_cons,horner]
  rfl

def height : List ℤ → ℕ
  | [] => 0
  | a::as => a.natAbs + height as

private def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a::as, b::bs => (a+b)::addCoeffs as bs

private def smulCoeffs (a : ℤ) (bs : List ℤ) : List ℤ := bs.map (a * ·)

private def mulCoeffs : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a::as, bs => addCoeffs (smulCoeffs a bs) (0::mulCoeffs as bs)

private theorem add_height (as bs : List ℤ) :
    height (addCoeffs as bs) ≤ height as + height bs := by
  induction as generalizing bs with
  | nil => simp [height,addCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [height,addCoeffs]
    | cons b bs =>
      simp only [addCoeffs,height]
      have hk := Int.natAbs_add_le a b
      have hh := ih bs
      omega

private theorem smul_height (a : ℤ) (bs : List ℤ) :
    height (smulCoeffs a bs) = a.natAbs * height bs := by
  unfold smulCoeffs
  induction bs with
  | nil => simp [height]
  | cons b bs ih => simp [height,Int.natAbs_mul,Nat.mul_add,ih]

private theorem mul_height (as bs : List ℤ) :
    height (mulCoeffs as bs) ≤ height as * height bs := by
  induction as with
  | nil => simp [mulCoeffs,height]
  | cons a as ih =>
    have z := add_height (smulCoeffs a bs) (0::mulCoeffs as bs)
    simp only [smul_height,height,Int.natAbs_zero,zero_add] at z
    simp only [mulCoeffs,height,Nat.add_mul]
    exact z.trans (Nat.add_le_add_left ih _)

private theorem neg_height (as : List ℤ) :
    height (as.map Neg.neg) = height as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [height,ih]

private theorem coeval_add {R : Type*} [CommRing R] (x : R) (as bs : List ℤ) :
    coeval (addCoeffs as bs) x = coeval as x + coeval bs x := by
  induction as generalizing bs with
  | nil => simp [addCoeffs,coeval,horner]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs,coeval,horner]
    | cons b bs =>
      simp only [addCoeffs,coeval,horner,List.map_cons,map_add] at ih ⊢
      rw [ih]
      ring

private theorem coeval_smul {R : Type*} [CommRing R] (x : R) (a : ℤ) (bs : List ℤ) :
    coeval (smulCoeffs a bs) x = (a:R) * coeval bs x := by
  induction bs with
  | nil => simp [smulCoeffs,coeval,horner]
  | cons b bs ih =>
    simp only [smulCoeffs,coeval,horner,List.map_cons,map_mul] at ih ⊢
    rw [ih]
    change (a:R)*(b:R) + _ = (a:R)*((b:R)+_)
    ring

private theorem coeval_mul {R : Type*} [CommRing R] (x : R) (as bs : List ℤ) :
    coeval (mulCoeffs as bs) x = coeval as x * coeval bs x := by
  induction as with
  | nil => simp [mulCoeffs,coeval,horner]
  | cons a as ih =>
    rw [mulCoeffs,coeval_add,coeval_smul]
    rw [coeval_cons,coeval_cons,Int.cast_zero,ih,zero_add]
    ring

private theorem coeval_neg {R : Type*} [CommRing R] (x : R) (as : List ℤ) :
    coeval (as.map Neg.neg) x = -coeval as x := by
  induction as with
  | nil => simp [coeval,horner]
  | cons a as ih =>
    simp only [coeval,horner,List.map_cons,map_neg] at ih ⊢
    rw [ih]
    ring

private theorem all_zero_of_packed {base : ℕ} {as : List ℤ}
    (hb : height as < base) (he : horner as (base:ℤ) = 0) :
    ∀ a ∈ as, a = 0 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [height,horner] at hb he
    have hz : a = -((base:ℤ) * horner as (base:ℤ)) := eq_neg_of_add_eq_zero_left he
    have ht : horner as (base:ℤ) = 0 := by
      by_contra hn
      have hr : 0 < (horner as (base:ℤ)).natAbs :=
        Nat.pos_of_ne_zero fun h => hn (Int.natAbs_eq_zero.mp h)
      have hh := congrArg Int.natAbs hz
      simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at hh
      have hw := Nat.le_mul_of_pos_right base hr
      omega
    have ha : a=0 := by simpa only [ht,mul_zero,neg_zero] using hz
    intro b h
    rcases List.mem_cons.mp h with rfl|h
    · exact ha
    · exact ih (by omega) ht b h

private theorem coeval_of_coeffs_zero {R : Type*} [CommRing R] (x : R) {as : List ℤ}
    (h : ∀ c ∈ as, c=0) : coeval as x = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    subst a
    rw [coeval_cons,Int.cast_zero,ht,mul_zero,add_zero]

/-- An unexpanded exact polynomial expression. -/
inductive Expr where
  | atom : List ℤ → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr

namespace Expr

def val {R : Type*} [CommRing R] (x : R) : Expr → R
  | .atom a => coeval a x
  | .add a b => val x a + val x b
  | .neg a => -val x a
  | .mul a b => val x a * val x b

def pack (x : ℤ) : Expr → ℤ
  | .atom a => horner a x
  | .add a b => pack x a + pack x b
  | .neg a => -pack x a
  | .mul a b => pack x a * pack x b

def bound : Expr → ℕ
  | .atom a => height a
  | .add a b => bound a + bound b
  | .neg a => bound a
  | .mul a b => bound a * bound b

def sub (a b : Expr) : Expr := .add a (.neg b)

private def coeffs : Expr → List ℤ
  | .atom a => a
  | .add a b => addCoeffs (coeffs a) (coeffs b)
  | .neg a => (coeffs a).map Neg.neg
  | .mul a b => mulCoeffs (coeffs a) (coeffs b)

private theorem coeffs_val {R : Type*} [CommRing R] (x : R) (a : Expr) :
    coeval (a.coeffs) x = a.val x := by
  induction a with
  | atom a => rfl
  | add a b ha hb => simp only [coeffs,val,coeval_add,ha,hb]
  | neg a ha => simp only [coeffs,val,coeval_neg,ha]
  | mul a b ha hb => simp only [coeffs,val,coeval_mul,ha,hb]

private theorem coeffs_height (e : Expr) : height e.coeffs ≤ e.bound := by
  induction e with
  | atom a => exact le_rfl
  | add a b ha hb => exact (add_height _ _).trans (Nat.add_le_add ha hb)
  | neg a ha => simpa only [coeffs,bound,neg_height] using ha
  | mul a b ha hb => exact (mul_height _ _).trans (Nat.mul_le_mul ha hb)

private theorem coeval_int (as : List ℤ) (x : ℤ) : coeval as x = horner as x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (a:ℤ) + x*coeval as x = a+x*horner as x
    rw [ih]

private theorem pack_eq (x : ℤ) (a : Expr) : a.pack x = a.val x := by
  induction a with
  | atom a => exact (coeval_int a x).symm
  | add a b ha hb => simp only [pack,val,ha,hb]
  | neg a ha => simp only [pack,val,ha]
  | mul a b ha hb => simp only [pack,val,ha,hb]

theorem val_zero_of_pack {R : Type*} [CommRing R] {n : ℕ} {a : Expr}
    (hb : a.bound < n) (h : a.pack (n:ℤ) = 0) (x : R) : a.val x = 0 := by
  rw [pack_eq,←coeffs_val,coeval_int] at h
  rw [←coeffs_val]
  exact coeval_of_coeffs_zero x (all_zero_of_packed (a.coeffs_height.trans_lt hb) h)

end Expr

/-- Decode signed radix digits. No exactness claim is needed for this
candidate generator; both the resulting identity and its bound are checked. -/
def balanced (base : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n+1, z => if z=0 then [] else
      let r := z % base
      let d := if base ≤ 2*r then r-base else r
      d :: balanced base n ((z-d)/base)

/-- Check an explicit polynomial quotient at one integer radix. -/
def checkMod (modulus : List ℤ) (base digits : ℕ) (e : Expr) : Bool :=
  let v := e.pack (base:ℤ)
  let m := horner modulus (base:ℤ)
  let q := balanced (base:ℤ) digits (v/m)
  decide (v = m * horner q (base:ℤ) ∧ e.bound+height modulus * height q < base)

theorem checkMod_sound {R : Type*} [CommRing R] {modulus : List ℤ} {base digits : ℕ}
    {e : Expr} (h : checkMod modulus base digits e=true) {x : R}
    (hx : coeval modulus x = 0) : e.val x = 0 := by
  let q := balanced (base:ℤ) digits (e.pack (base:ℤ)/horner modulus (base:ℤ))
  let diff := e.sub (.mul (.atom modulus) (.atom q))
  have hc : e.pack (base:ℤ) = horner modulus (base:ℤ)*horner q (base:ℤ) ∧
      e.bound + height modulus*height q < base := of_decide_eq_true h
  have hz : diff.val x = 0 := Expr.val_zero_of_pack hc.2
    (by change e.pack (base:ℤ) + -(horner modulus (base:ℤ)*horner q (base:ℤ)) = 0
        rw [hc.1,add_neg_cancel]) x
  change e.val x + -(coeval modulus x * coeval q x) = 0 at hz
  simpa only [hx,zero_mul,neg_zero,add_zero] using hz

/-- A conservative radix for local expression certificates. Failed
candidate recovery cannot cause acceptance. -/
def checkLocal (modulus : List ℤ) (digits : ℕ) (e : Expr) : Bool :=
  checkMod modulus (16*(e.bound+1)*(height modulus+1)^(digits+1)) digits e

theorem checkLocal_sound {R : Type*} [CommRing R] {modulus : List ℤ} {digits : ℕ}
    {e : Expr} (h : checkLocal modulus digits e=true) {x : R}
    (hx : coeval modulus x = 0) : e.val x = 0 := checkMod_sound h hx

end RKCert.ReviewedNative.IntegerHornerCertificate
