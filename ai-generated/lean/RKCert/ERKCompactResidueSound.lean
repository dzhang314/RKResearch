module

public import RKCert.ERKCompactResidueCore
public import RKCert.ERKGoodPrimeNat
public import RKCert.ERKGoodPrimePoly
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

@[expose] public section

namespace RKCert.CompactResidue

open Polynomial RKCert.GoodPrimeDense
open scoped BigOperators

private theorem atCoeff_zero (a : List Nat) {i : Nat} (h : a.length ≤ i) :
    atCoeff a i = 0 := by
  simp [atCoeff, List.getElem?_eq_none_iff.mpr h]

private theorem list_range_sum {A : Type*} [AddCommMonoid A] (f : Nat → A) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem convolution_zero (a b : List Nat) {i : Nat} (h : a.length+b.length ≤ i) :
    convolution a b i = 0 := by
  rw [convolution, list_range_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : a.length ≤ j
  · simp [atCoeff_zero a hj]
  · have hh : b.length ≤ i-j := by omega
    simp [atCoeff_zero b hh]

private theorem shift_zero (n : Nat) (q : List Nat) {i : Nat} (h : n+q.length ≤ i) :
    shiftCoeff n q i = 0 := by
  have hi : n ≤ i := by omega
  have hq : q.length ≤ i-n := by omega
  simp [shiftCoeff, hi, atCoeff_zero q hq]

private theorem equalCoeffs_at {p n : Nat} {lhs rhs : Nat → Nat}
    (h : equalCoeffs p n lhs rhs = true) {i : Nat} (hi : i < n) :
    lhs i % p = rhs i % p :=
  of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))

variable (E : Type*) [CommRing E]

noncomputable def polynomial (a : List Nat) : E[X] := decode (fun n : Nat => (n:E)) a

private theorem poly_coeff (a : List Nat) (i : Nat) :
    (polynomial E a).coeff i = (atCoeff a i : E) := by
  simp only [polynomial, decode, coeff_ofCoeffList, List.getD_eq_getElem?_getD,
    atCoeff, List.getElem?_map]
  cases a[i]? <;> simp

private theorem poly_product_coeff (a b : List Nat) (i : Nat) :
    (polynomial E a*polynomial E b).coeff i = (convolution a b i:E) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => (polynomial E a).coeff j * (polynomial E b).coeff k)]
  simp [poly_coeff, convolution, list_range_sum]

private theorem poly_shift_coeff (n : Nat) (a : List Nat) (i : Nat) :
    ((X:E[X])^n*polynomial E a).coeff i = (shiftCoeff n a i:E) := by
  rw [Polynomial.coeff_X_pow_mul']
  by_cases h : n ≤ i <;> simp [h, shiftCoeff, poly_coeff]

theorem eval_poly (a : List Nat) (l : E) :
    (polynomial E a).eval l = GoodPrimeDense.read (fun n : Nat => (n:E)) l a := by
  simp only [polynomial, decode]
  induction a with
  | nil => simp [GoodPrimeDense.read]
  | cons n a ih => simp [Polynomial.ofCoeffList_cons, GoodPrimeDense.read, ih]

variable {E} {p : Nat} [CharP E p]

private theorem cast_eq_of_mod {a b : Nat} (h : a % p = b % p) : (a:E) = (b:E) :=
  (CharP.cast_eq_mod E p a).trans <| (congrArg (fun n : Nat => (n:E)) h).trans <|
    (CharP.cast_eq_mod E p b).symm

theorem add_witness {a b c : List Nat} (h : addCheck p a b c = true) (l : E) :
    GoodPrimeDense.read (fun n : Nat => (n:E)) l a + GoodPrimeDense.read (fun n : Nat => (n:E)) l b =
      GoodPrimeDense.read (fun n : Nat => (n:E)) l c := by
  have hh : polynomial E a+polynomial E b = polynomial E c := by
    ext i
    simp only [Polynomial.coeff_add, poly_coeff, ←Nat.cast_add]
    apply cast_eq_of_mod (p:=p)
    by_cases ih : i < max a.length (max b.length c.length)
    · exact equalCoeffs_at h ih
    · simp only [not_lt, max_le_iff] at ih
      simp [atCoeff_zero a ih.1, atCoeff_zero b ih.2.1, atCoeff_zero c ih.2.2]
  simpa [eval_poly] using congrArg (Polynomial.eval l) hh

theorem neg_witness {a c : List Nat} (h : negCheck p a c = true) (l : E) :
    -GoodPrimeDense.read (fun n : Nat => (n:E)) l a = GoodPrimeDense.read (fun n : Nat => (n:E)) l c := by
  have hh : polynomial E a+polynomial E c = 0 := by
    ext i
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero, poly_coeff, ←Nat.cast_add]
    rw [show (0:E) = ((0:Nat):E) by simp]
    apply cast_eq_of_mod (p:=p)
    by_cases ih : i < max a.length c.length
    · exact equalCoeffs_at h ih
    · simp only [not_lt, max_le_iff] at ih
      simp [atCoeff_zero a ih.1, atCoeff_zero c ih.2]
  have hh' := congrArg (Polynomial.eval l) hh
  simp only [Polynomial.eval_add, eval_poly, Polynomial.eval_zero] at hh'
  exact neg_eq_of_add_eq_zero_left (by simpa [add_comm] using hh')

/-- The checked identity in the formal polynomial ring. No choice of root is used. -/
theorem mul_polynomial_relation {r a b c q : List Nat}
    (h : mulCheck p r a b c q = true) :
    polynomial E a * polynomial E b + polynomial E r * polynomial E q =
      polynomial E c + X^r.length * polynomial E q := by
  ext i
  simp only [Polynomial.coeff_add, poly_product_coeff, poly_coeff, poly_shift_coeff,
    ←Nat.cast_add]
  apply cast_eq_of_mod (p:=p)
  by_cases hi : i < max (a.length+b.length) (max c.length (r.length+q.length))
  · exact equalCoeffs_at h hi
  · simp only [not_lt, max_le_iff] at hi
    simp [convolution_zero a b hi.1, atCoeff_zero c hi.2.1,
      convolution_zero r q hi.2.2, shift_zero r.length q hi.2.2]

/-- A degree-unrestricted coefficient check of an ordinary formal product. -/
theorem mul_polynomial_witness {a b c : List Nat}
    (h : mulCheck p [] a b c [] = true) :
    polynomial E a * polynomial E b = polynomial E c := by
  simpa [polynomial,decode] using (mul_polynomial_relation (E:=E) h)

/-- Checked coefficient identity for a full list product. -/
inductive Product (p : Nat) : List (List Nat) → List Nat → Prop
  | nil : Product p [] [1]
  | cons : Product p b c → mulCheck p [] a c d [] = true → Product p (a::b) d

theorem Product.correct {l : List (List Nat)} {a : List Nat}
    (h : Product p l a) : (l.map (polynomial E)).prod = polynomial E a := by
  induction h with
  | nil => simp [polynomial,decode,Polynomial.ofCoeffList_cons]
  | cons _ mul ih =>
    rw [List.map_cons,List.prod_cons,ih]
    exact mul_polynomial_witness mul

theorem mul_witness {r a b c q : List Nat} (h : mulCheck p r a b c q = true) (l : E)
    (root : GoodPrimeDense.read (fun n : Nat => (n:E)) l r = l^r.length) :
    GoodPrimeDense.read (fun n : Nat => (n:E)) l a * GoodPrimeDense.read (fun n : Nat => (n:E)) l b =
      GoodPrimeDense.read (fun n : Nat => (n:E)) l c := by
  have hb := mul_polynomial_relation (E:=E) h
  have hh := congrArg (Polynomial.eval l) hb
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    eval_poly, root] at hh
  exact add_right_cancel hh

def Term.eval (l : E) : Term → E
  | .raw a => GoodPrimeDense.read (fun n : Nat => (n:E)) l a
  | .add a b => a.eval l + b.eval l
  | .mul a b => a.eval l * b.eval l
  | .neg a => -a.eval l

theorem Value.correct {r : List Nat} {t : Term} {a : List Nat} (h : Value p r t a) (l : E)
    (root : GoodPrimeDense.read (fun n : Nat => (n:E)) l r = l^r.length) :
    t.eval l = GoodPrimeDense.read (fun n : Nat => (n:E)) l a := by
  induction h with
  | raw => rfl
  | add _ _ h ab bb => rw [Term.eval, ab, bb, add_witness h]
  | neg _ h ab => rw [Term.eval, ab, neg_witness h]
  | mul _ _ _ h ab bb => rw [Term.eval, ab, bb, mul_witness h l root]

theorem SameValues.correct {r : List Nat} {aa bb : List Term}
    (h : SameValues p r aa bb) (l : E)
    (root : GoodPrimeDense.read (fun n : Nat => (n:E)) l r = l^r.length) :
    aa.map (Term.eval l) = bb.map (Term.eval l) := by
  induction h with
  | nil => rfl
  | cons h1 h2 hTail ih =>
    simp only [List.map_cons, h1.correct l root, h2.correct l root, ih]

def syntaxOps (p : Nat) : Operations Term :=
  ⟨.raw [], Term.int p, Term.plus, Term.times, Term.opposite, Term.isZero⟩

private theorem Term.eval_isZero (l : E) {a : Term} (h : a.isZero = true) :
    a.eval l = 0 := by
  cases a with
  | raw a => cases a <;> simp [Term.isZero, Term.eval, GoodPrimeDense.read] at h ⊢
  | add | mul | neg => simp [Term.isZero] at h

private theorem Term.eval_isOne (l : E) {a : Term} (h : a.isOne = true) :
    a.eval l = 1 := by
  cases a with
  | raw a =>
    match a with
    | [] | [0] | (_+2) :: [] | _ :: _ :: _ => simp [Term.isOne] at h
    | [1] => simp [Term.eval, GoodPrimeDense.read]
  | add | mul | neg => simp [Term.isOne] at h

theorem syntax_sound (hp : p ≠ 0) (l : E) : Sound (syntaxOps p) (Term.eval l) where
  zero := rfl
  int w := by
    change (if intResidue p w = 0 then Term.raw [] else Term.raw [intResidue p w]).eval l =
      (w:E)
    by_cases h : intResidue p w = 0
    · simpa [h,Term.eval,GoodPrimeDense.read] using (intResidue_cast (R:=E) hp w)
    · simpa [h,Term.eval,GoodPrimeDense.read] using (intResidue_cast (R:=E) hp w)
  add a b := by
    change (a.plus b).eval l = _
    unfold Term.plus
    split
    · rename_i h; simp [Term.eval_isZero l h]
    · split
      · rename_i h; simp [Term.eval_isZero l h]
      · rfl
  mul a b := by
    change (a.times b).eval l = _
    unfold Term.times
    split
    · rename_i h
      rcases Bool.or_eq_true_iff.mp h with h | h <;>
        simp [Term.eval, GoodPrimeDense.read, Term.eval_isZero l h]
    · split
      · rename_i h; simp [Term.eval_isOne l h]
      · split
        · rename_i h; simp [Term.eval_isOne l h]
        · rfl
  neg a := by
    change a.opposite.eval l = _
    unfold Term.opposite
    split
    · rename_i h; simp [Term.eval, GoodPrimeDense.read, Term.eval_isZero l h]
    · rfl
  isZero _ h := Term.eval_isZero l h

end RKCert.CompactResidue
