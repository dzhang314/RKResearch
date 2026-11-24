module

public import RKCert.ERKGoodPrimeSmallNorm
public import Mathlib.Algebra.Polynomial.CoeffList

@[expose] public section

namespace RKCert.GoodPrimeDense
open Polynomial

variable {A R S : Type*} [CommRing R] [CommRing S]
variable {o : Operations A} {f : A→R}

theorem Sound.push (s : Sound o f) (g : R→+*S) : Sound o (g ∘ f) where
  zero := by simp [Function.comp_apply,s.zero]
  int i := by simp [Function.comp_apply,s.int]
  add a b := by simp [Function.comp_apply,s.add]
  mul a b := by simp [Function.comp_apply,s.mul]
  neg a := by simp [Function.comp_apply,s.neg]
  isZero a ha := by simp [Function.comp_apply,s.isZero a ha]

theorem eval₂_ofCoeffList_read (g : R→+*S) (x : S) (p : List R) :
    (ofCoeffList p).eval₂ g x = read g x p := by
  induction p with
  | nil => simp [read]
  | cons a p ih => simp [ofCoeffList_cons,read,ih]

noncomputable def decode (f : A→R) (p : List A) : R[X] :=
  ofCoeffList (p.map f)

theorem decode_eq_read (f : A→R) (p : List A) :
    decode f p = read (C ∘ f) X p := by
  induction p with
  | nil => simp [decode,read]
  | cons a p ih => simp [decode,ofCoeffList_cons,read,←ih,Function.comp_apply]

theorem coeff_decode (s : Sound o f) (p : List A) (i : ℕ) :
    (decode f p).coeff i = f (coeff o p i) := by
  simp only [decode,coeff_ofCoeffList,List.getD_eq_getElem?_getD,coeff,List.getElem?_map]
  cases h : p[i]? <;> simp [s.zero]

theorem decode_plus (s : Sound o f) (p q : List A) :
    decode f (plus o p q) = decode f p + decode f q := by
  rw [decode_eq_read,read_plus (s.push C),←decode_eq_read,←decode_eq_read]

theorem decode_opposite (s : Sound o f) (p : List A) :
    decode f (opposite o p) = -decode f p := by
  rw [decode_eq_read,read_opposite (s.push C),←decode_eq_read]

theorem decode_times (s : Sound o f) (p q : List A) :
    decode f (times o p q) = decode f p * decode f q := by
  rw [decode_eq_read,read_times (s.push C),←decode_eq_read,←decode_eq_read]

theorem decode_timesScalar (s : Sound o f) (a : A) (p : List A) :
    decode f (timesScalar o a p) = C (f a) * decode f p := by
  rw [decode_eq_read,read_timesScalar (s.push C),←decode_eq_read]
  rfl

theorem decode_shift (s : Sound o f) (n : ℕ) (p : List A) :
    decode f (List.replicate n o.zero ++ p) = X^n * decode f p := by
  rw [decode_eq_read]
  induction n with
  | zero => simp [decode_eq_read]
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,read,Function.comp_apply,s.zero,map_zero,zero_add]
    rw [ih,pow_succ',mul_assoc]

end RKCert.GoodPrimeDense
