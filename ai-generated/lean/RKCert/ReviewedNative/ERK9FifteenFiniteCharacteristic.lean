module

public import RKCert.ReviewedNative.ERK9FifteenIdempotentPortfolio
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Ring

@[expose] public section

/-! Finite characteristic supplies the scalar CRT idempotent.
This proof uses only repetition of powers in the finite scalar subring,
not any structural assumption on the ambient coefficient ring. -/

namespace RKResearch.Certified.ERK9FifteenLocalRing
open RKResearch
open scoped Matrix

/-- An element of any finite monoid has an idempotent positive power. -/
theorem finite_idempotent_power {S : Type*} [Monoid S] [Finite S] (a : S) :
    ∃ n : ℕ, 0<n ∧ IsIdempotentElem (a^n) := by
  obtain ⟨i,j,hij,hA⟩ : ∃ i j : ℕ, i<j ∧ a^i=a^j := by
    obtain ⟨i,j,hne,he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a^n)
    rcases lt_or_gt_of_ne hne with hl|hg
    · exact ⟨i,j,hl,he⟩
    · exact ⟨j,i,hg,he.symm⟩
  let k := j-i
  have hk : 0<k := by dsimp [k]; omega
  have shift (l : ℕ) (hl : i≤l) : a^(l+k)=a^l := by
    calc
      _ = a^(j+(l-i)) := by congr 1; dsimp [k]; omega
      _ = a^j*a^(l-i) := by rw [pow_add]
      _ = a^i*a^(l-i) := by rw [hA]
      _ = a^l := by rw [←pow_add]; congr 1; omega
  have shifts (l q : ℕ) (hl : i≤l) : a^(l+k*q)=a^l := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ,←Nat.add_assoc,shift (l+k*q) (by omega),ih]
  let n := (i+1)*k
  have hn : 0<n := Nat.mul_pos (by omega) hk
  have hin : i≤n := by
    have h := Nat.mul_le_mul_left (i+1) (show 1≤k from hk)
    rw [Nat.mul_one] at h
    exact le_trans (by omega) h
  have hh := shifts n (i+1) hin
  have mEq : k*(i+1)=n := Nat.mul_comm .. 
  refine ⟨n,hn,?_⟩
  change a^n*a^n=a^n
  rw [mEq] at hh
  rwa [←pow_add]

variable {R : Type*} [CommRing R] [Nontrivial R]

theorem exists_exact_if_scalar_power_idempotent
    (h9 : IsUnit (Nat.factorial 9:R)) (n : ℕ) (hn : 0<n)
    (hi : IsIdempotentElem ((D₁:R)^n)) :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15→R),
      ERK A ∧ HasOrder 9 A b ∧ ¬ HasOrder 10 A b := by
  let a : R := (D₁:R)
  let b : R := (D₂:R)
  let e : R := a^n
  have he : e*e=e := hi
  have he' : (1-e)*(1-e)=1-e := calc
    _ = 1-2*e+e*e := by ring
    _ = _ := by rw [he]; ring
  have hz : (1-e)*e=0 := by rw [sub_mul,one_mul,he,sub_self]
  obtain ⟨u,hu⟩ := denominator_sum_unit h9
  let k : R := ↑(u⁻¹)
  have hU : ((c₁:R)*a+(c₂:R)*b)*k=1 := by
    change ((c₁:R)*(D₁:R)+(c₂:R)*(D₂:R))*k=1
    rw [← hu]
    exact u.mul_inv
  let r : R := (c₁:R)*k
  let s : R := (c₂:R)*k
  have hrs : r*a+s*b=1 := calc
    _ = ((c₁:R)*a+(c₂:R)*b)*k := by dsimp [r,s]; ring
    _ = _ := hU
  let z : R := (1-e)*r*a
  have hzNil : IsNilpotent z := by
    refine ⟨n,?_⟩
    have h' : (1-e)^n=1-e :=
      (show IsIdempotentElem (1-e) from he').pow_eq (Nat.ne_of_gt hn)
    calc
      z^n = (1-e)^n*r^n*a^n := by simp only [z,mul_pow]
      _ = ((1-e)*e)*r^n := by rw [h']; change (1-e)*r^n*e=_; ring
      _ = 0 := by rw [hz,zero_mul]
  obtain ⟨w,hw⟩ := hzNil.isUnit_one_sub
  let v : R := ↑(w⁻¹)
  have hv : (1-z)*v=1 := by rw [← hw]; exact w.mul_inv
  let d₁ := e*a^(n-1)
  let d₂ := (1-e)*s*v
  have hd₁ : a*d₁=e := calc
    _ = e*a^((n-1)+1) := by simp only [d₁,pow_succ]; ring
    _ = e*e := by rw [Nat.sub_add_cancel (by omega : 1≤n)]
    _ = e := he
  have hz' : (1-e)*z=z := by
    dsimp only [z]
    calc
      _ = (((1-e)*(1-e))*r)*a := by ring
      _ = _ := by rw [he']
  have hs : s*b=1-r*a := eq_sub_of_add_eq (by simpa only [add_comm] using hrs)
  have hs' : (1-e)*s*b=(1-e)*(1-z) := calc
    _ = (1-e)*(s*b) := by ring
    _ = (1-e)-z := by rw [hs]; dsimp [z]; ring
    _ = _ := by rw [mul_sub,mul_one,hz']
  have hd₂ : b*d₂=1-e := calc
    _ = ((1-e)*s*b)*v := by dsimp [d₂]; ring
    _ = _ := by rw [hs',mul_assoc,hv,mul_one]
  have cp₁ : e*d₁=d₁ := by
    dsimp only [d₁]
    rw [←mul_assoc,he]
  have cp₂ : (1-e)*d₂=d₂ := by
    dsimp only [d₂]
    calc
      _ = (((1-e)*(1-e))*s)*v := by ring
      _ = _ := by rw [he']
  exact exists_exact_of_projected_scales h9 he hd₁ hd₂ cp₁ cp₂

theorem exists_exact_finite_characteristic {p : ℕ} [CharP R p] (hp : p≠0)
    (h9 : IsUnit (Nat.factorial 9:R)) :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15→R),
      ERK A ∧ HasOrder 9 A b ∧ ¬ HasOrder 10 A b := by
  let : NeZero p := ⟨hp⟩
  let f : ZMod p →+* R := ZMod.castHom (dvd_refl p) R
  obtain ⟨n,hn,hi⟩ := finite_idempotent_power (D₁:ZMod p)
  change (D₁:ZMod p)^n*(D₁:ZMod p)^n=(D₁:ZMod p)^n at hi
  have H := congrArg f hi
  simp only [map_mul,map_pow,map_intCast] at H
  exact exists_exact_if_scalar_power_idempotent h9 n hn H

end RKResearch.Certified.ERK9FifteenLocalRing

#print axioms RKResearch.Certified.ERK9FifteenLocalRing.exists_exact_finite_characteristic
