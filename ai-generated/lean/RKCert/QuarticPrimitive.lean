module

public import RKCert.StagePrimitives
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

@[expose] public section

/-! # The quartic primitive obstruction for a quadratic head -/
namespace RKCert.Paired
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- If the primitive of Xg is divisible by g with quotient of degree at most
two, then g is a single monomial. In particular the primitive has no
nonzero root. -/
theorem primitive_mul_X_root_free {g h : Polynomial K} (hg : g≠0) (hh : h.natDegree ≤ 2)
    (he : primitive (X*g) = g*h) {u : K} (hu : u≠0) :
    (primitive (X*g)).eval u ≠ 0 := by
  let Q := primitive (X*g)
  let m := g.natTrailingDegree
  have hm : g.coeff m≠0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hg
  have hc (n : ℕ) : Q.coeff (n+2) = g.coeff n / ((n+2:ℕ):K) := by
    dsimp only [Q]
    rw [show n+2=(n+1)+1 by omega,primitive_coeff_succ,Polynomial.coeff_X_mul]
  have hQm : Q.coeff (m+2)≠0 := by rw [hc]; exact div_ne_zero hm (Nat.cast_ne_zero.mpr (by omega))
  have hQ : Q≠0 := by intro h; simp [h] at hQm
  have hhn : h≠0 := by intro h'; apply hQ; simp [Q,he,h']
  have htrail : Q.natTrailingDegree=m+2 := by
    apply (Polynomial.natTrailingDegree_le_of_ne_zero hQm).antisymm
    apply Polynomial.le_natTrailingDegree hQ
    intro n hn
    rcases n with _ | (_ | n)
    · exact primitive_coeff_zero _
    · change (primitive (X*g)).coeff (0+1)=0
      rw [primitive_coeff_succ,Polynomial.coeff_X_mul_zero,zero_div]
    · change Q.coeff (n+2)=0
      rw [hc,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (show n < g.natTrailingDegree by dsimp [m] at hn; omega),zero_div]
  have htr : h.natTrailingDegree=2 := by
    have ht := Polynomial.natTrailingDegree_mul hg hhn
    change Q=g*h at he
    rw [← he,htrail] at ht
    dsimp [m] at ht
    omega
  have hmono : h = C (h.coeff 2) * X^2 := by
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    ext n
    by_cases hn : n=2
    · simp [hn]
    · rw [Polynomial.coeff_monomial_of_ne _ hn]
      by_cases hn' : n<2
      · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rw [htr]; exact hn')
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff (n : ℕ) : g.coeff n / ((n+2:ℕ):K) = g.coeff n * h.coeff 2 := by
    calc
      _ = Q.coeff (n+2) := (hc n).symm
      _ = (g * (C (h.coeff 2) * X^2)).coeff (n+2) := by change Q=g*h at he; rw [he,← hmono]
      _ = _ := by rw [← mul_assoc,Polynomial.coeff_mul_X_pow,Polynomial.coeff_mul_C]
  have huniq (n : ℕ) (hn : g.coeff n≠0) : n=m := by
    have ha : (((n+2:ℕ):K))⁻¹ = h.coeff 2 := by
      apply mul_left_cancel₀ hn
      simpa only [div_eq_mul_inv] using hcoeff n
    have hb : (((m+2:ℕ):K))⁻¹ = h.coeff 2 := by
      apply mul_left_cancel₀ hm
      simpa only [div_eq_mul_inv] using hcoeff m
    have hcast : ((n+2:ℕ):K) = ((m+2:ℕ):K) := inv_injective (ha.trans hb.symm)
    have hn' := Nat.cast_injective hcast
    omega
  have hgmono : g=monomial m (g.coeff m) := by
    ext n
    by_cases hn : n=m
    · simp [hn]
    · rw [Polynomial.coeff_monomial_of_ne _ hn]
      by_contra hz
      exact hn (huniq n hz)
  have hne : h.coeff 2 ≠ 0 := by rw [← htr]; exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hhn
  have hg_u : g.eval u≠0 := by
    rw [hgmono,Polynomial.eval_monomial]
    exact mul_ne_zero hm (pow_ne_zero _ hu)
  have hh_u : h.eval u≠0 := by
    rw [hmono,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    exact mul_ne_zero hne (pow_ne_zero _ hu)
  rw [he,Polynomial.eval_mul]
  exact mul_ne_zero hg_u hh_u

end RKCert.Paired
