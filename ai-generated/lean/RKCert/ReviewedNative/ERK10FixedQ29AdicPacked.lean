module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrigin
public import RKCert.ReviewedNative.IntegerHornerCertificate

@[expose] public section

/-! Reusable guarded congruence receipts: a rational-coordinate formula
is compiled to a common-denominator integer polynomial expression and
checked with a signed packed Horner congruence. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Packed

open scoped Ring BigOperators
open RKCert.ReviewedNative.IntegerHornerCertificate
open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- A numerator polynomial and an integer denominator. We require
guarded invertibility only when evaluating a checked receipt. -/
structure Rep where
  num : List ℤ
  den : ℕ

def Rep.val (a : Rep) (x : R) : R := coeval a.num x * (a.den : R)⁻¹ʳ
def Paid (d : ℕ) : Prop := ¬ 29 ∣ d
instance (d : ℕ) : Decidable (Paid d) := inferInstanceAs (Decidable (¬ 29 ∣ d))

theorem paid_unit (ρ : R →+* F) [IsLocalHom ρ] {d : ℕ} (hd : Paid d) :
    IsUnit (d : R) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rwa [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]

theorem Rep.den_mul_val (a : Rep) (x : R) (ha : IsUnit (a.den:R)) :
    (a.den : R)*a.val x = coeval a.num x := by
  rw [Rep.val, mul_left_comm, Ring.mul_inverse_cancel _ ha, mul_one]

private theorem coeval_nil (x : R) : coeval [] x = 0 := rfl

theorem coeval_eq_jet (a : List ℤ) (x : R) : coeval a x = (intJet x a).1 := by
  induction a with
  | nil => rfl
  | cons a as ih => rw [coeval_cons, intJet, ih]

theorem root_coeval {x : R} (hx : (decic R).eval x = 0) : coeval decicCoeffs x = 0 := by
  rw [coeval_eq_jet]
  simpa only [decic, eval_intPolynomial] using hx

inductive Form where
  | const : ℤ → Form
  | slot : Rep → Form
  | add : Form → Form → Form
  | neg : Form → Form
  | mul : Form → Form → Form

namespace Form

instance : Add Form := ⟨.add⟩
instance : Mul Form := ⟨.mul⟩
instance : Neg Form := ⟨.neg⟩
instance : Sub Form := ⟨fun a b => .add a (.neg b)⟩
instance (n : ℕ) : OfNat Form n := ⟨.const n⟩

def pow (a : Form) : ℕ → Form
  | 0 => .const 1
  | n+1 => .mul (pow a n) a
instance : Pow Form ℕ := ⟨pow⟩

@[simp] def val (x : R) : Form → R
  | .const n => n
  | .slot a => a.val x
  | .add a b => val x a + val x b
  | .neg a => -val x a
  | .mul a b => val x a * val x b

@[simp] theorem val_nat (x : R) (n : ℕ) : val x (OfNat.ofNat n) = (n:R) := by
  simp only [OfNat.ofNat, val, Int.cast_natCast]

@[simp] theorem val_add (x : R) (a b : Form) : val x (a+b) = val x a + val x b := rfl
@[simp] theorem val_sub (x : R) (a b : Form) : val x (a-b) = val x a - val x b := by
  change val x a + -val x b = val x a - val x b
  exact (sub_eq_add_neg _ _).symm
@[simp] theorem val_mul (x : R) (a b : Form) : val x (a*b) = val x a * val x b := rfl
@[simp] theorem val_neg (x : R) (a : Form) : val x (-a) = -val x a := rfl
@[simp] theorem val_pow (x : R) (a : Form) (n : ℕ) : val x (a^n) = (val x a)^n := by
  induction n with
  | zero =>
    change ((1 : ℤ) : R) = (val x a)^0
    rw [Int.cast_one, pow_zero]
  | succ n ih =>
    change val x (a^n)*val x a = _
    rw [ih, pow_succ]

/-- Exact finite sum in the form language. -/
def sumFin : (n : ℕ) → (Fin n → Form) → Form
  | 0, _ => .const 0
  | n+1, f => f 0 + sumFin n (fun i => f i.succ)

@[simp] theorem val_sumFin (x : R) (n : ℕ) (f : Fin n → Form) :
    (sumFin n f).val x = ∑ i : Fin n, (f i).val x := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, ih, Fin.sum_univ_succ]


def degree : Form → ℕ
  | .const _ => 0
  | .slot _ => 1
  | .add a b => max a.degree b.degree
  | .neg a => a.degree
  | .mul a b => a.degree+b.degree

def divisors (D : ℕ) : Form → Bool
  | .const _ => true
  | .slot a => decide (a.den ∣ D)
  | .add a b | .mul a b => divisors D a && divisors D b
  | .neg a => divisors D a

def natAtom (n : ℕ) : Expr := .atom [n]

@[simp] theorem natAtom_val (x : R) (n : ℕ) : (natAtom n).val x = (n:R) := by
  simp only [natAtom, Expr.val, coeval_cons, coeval_nil, mul_zero, add_zero, Int.cast_natCast]

def numerator (D : ℕ) (e : Form) : Expr :=
  match e with
  | .const n => .atom [n]
  | .slot a => .mul (natAtom (D/a.den)) (.atom a.num)
  | .add a b => .add
      (.mul (natAtom (D^(max a.degree b.degree-a.degree))) (numerator D a))
      (.mul (natAtom (D^(max a.degree b.degree-b.degree))) (numerator D b))
  | .neg a => .neg (numerator D a)
  | .mul a b => .mul (numerator D a) (numerator D b)

theorem numerator_sound (ρ : R →+* F) [IsLocalHom ρ]
    {D : ℕ} (hD : Paid D) {e : Form} (he : e.divisors D = true) (x : R) :
    (e.numerator D).val x = (D:R)^e.degree * e.val x := by
  induction e with
  | const a =>
    simp only [numerator, Expr.val, coeval_cons, coeval_nil, mul_zero, add_zero, degree,
      pow_zero, one_mul, val]
  | slot a =>
    have hdiv : a.den ∣ D := of_decide_eq_true he
    have hu : IsUnit (a.den:R) := paid_unit ρ (fun hd => hD (dvd_trans hd hdiv))
    have hscale : ((D/a.den : ℕ):R) * (a.den:R) = (D:R) := by
      rw [←Nat.cast_mul, Nat.div_mul_cancel hdiv]
    simp only [numerator, Expr.val, natAtom_val, degree, pow_one,val]
    rw [←a.den_mul_val x hu, ←mul_assoc, hscale]
  | add a b ha hb =>
    obtain ⟨ha',hb'⟩ := Bool.and_eq_true_iff.mp he
    have hleft : (D:R)^(max a.degree b.degree-a.degree)*(D:R)^a.degree =
        (D:R)^(max a.degree b.degree) := by rw [←pow_add, Nat.sub_add_cancel (le_max_left _ _)]
    have hright : (D:R)^(max a.degree b.degree-b.degree)*(D:R)^b.degree =
        (D:R)^(max a.degree b.degree) := by rw [←pow_add, Nat.sub_add_cancel (le_max_right _ _)]
    simp only [numerator, Expr.val, natAtom_val, Nat.cast_pow, degree,val,
      ha ha', hb hb', ←mul_assoc, hleft, hright, mul_add]
  | neg a ha =>
    simp only [numerator, Expr.val, degree,val, ha he, mul_neg]
  | mul a b ha hb =>
    obtain ⟨ha',hb'⟩ := Bool.and_eq_true_iff.mp he
    simp only [numerator, Expr.val, degree,val, ha ha', hb hb', pow_add]
    ring

def cross (D : ℕ) (e : Form) (a : Rep) : Expr :=
  ((natAtom a.den).mul (e.numerator D)).sub ((natAtom (D^e.degree)).mul (.atom a.num))

def check (D digits : ℕ) (e : Form) (a : Rep) : Bool :=
  decide (Paid D ∧ Paid a.den) &&
    (e.divisors D && checkLocal decicCoeffs digits (cross D e a))

theorem check_sound (ρ : R →+* F) [IsLocalHom ρ] {x : R}
    (hx : (decic R).eval x = 0) {D digits : ℕ} {e : Form} {a : Rep}
    (h : check D digits e a = true) : a.val x = e.val x := by
  obtain ⟨hD,he⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨he,hmod⟩ := Bool.and_eq_true_iff.mp he
  obtain ⟨hD,ha⟩ : Paid D ∧ Paid a.den := of_decide_eq_true hD
  have hu := paid_unit ρ ha
  have hs := checkLocal_sound hmod (root_coeval hx)
  have hn := numerator_sound ρ hD he x
  have hcross : (a.den:R)*((D:R)^e.degree*e.val x)-
       (D:R)^e.degree*coeval a.num x = 0 := by
    simpa only [cross, Expr.sub, Expr.val, natAtom_val, Nat.cast_pow,
      sub_eq_add_neg, hn] using hs
  apply (hu.mul ((paid_unit ρ hD).pow e.degree)).mul_left_cancel
  calc
    _ = (D:R)^e.degree*((a.den:R)*a.val x) := by ring
    _ = (D:R)^e.degree*coeval a.num x := by rw [a.den_mul_val x hu]
    _ = (a.den:R)*((D:R)^e.degree*e.val x) := (sub_eq_zero.mp hcross).symm
    _ = _ := by ring

end Form

theorem inverse_from_product {x y : R} (h : x*y = 1) : x⁻¹ʳ = y := by
  have hu : IsUnit x := IsUnit.of_mul_eq_one y h
  apply hu.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ hu, h]

end
end RKResearch.Certified.ERK10FixedQ29Adic.Packed

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Packed.Form.check_sound
