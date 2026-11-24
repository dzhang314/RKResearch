module
public import RKCert.EndpointTailMoments
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K : Type*} [Field K] [CharZero K] {m : ℕ}
noncomputable section

/-- Exact degree of the signed closed-grid factor in any characteristic-zero field. -/
theorem closed_lobatto_degree (hm : 0<m) :
    ((X-1)*lobatto (K:=K) m).natDegree=m+1 := by
  have inj : Function.Injective (Int.castRingHom K) := Int.cast_injective
  have nz : (shiftedLegendre m).derivative ≠ 0 :=
    derivative_ne_zero.mpr (by rw [natDegree_shiftedLegendre];omega)
  have nz' : ((shiftedLegendre m).derivative.map (Int.castRingHom K))≠0 :=
    fun e=>nz ((Polynomial.map_injective _ inj) (e.trans (Polynomial.map_zero _).symm))
  have dl : (lobatto (K:=K) m).natDegree=m := by
    rw [lobatto,natDegree_C_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
      natDegree_X_mul nz',natDegree_map_eq_of_injective inj,natDegree_derivative,natDegree_shiftedLegendre]
    omega
  have hn : lobatto (K:=K) m≠0 := fun e=>by rw [e,natDegree_zero] at dl;omega
  rw [show (X-1:K[X])=X-C 1 by simp,natDegree_mul (X_sub_C_ne_zero _) hn,natDegree_X_sub_C,dl]
  omega

/-- Every multiple of the grid polynomial through degree 2m−1 integrates to zero. -/
theorem integral_zero_of_closed_lobatto_dvd
    (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (R : K[X])
    (hd : (X-1)*lobatto m ∣ R) (deg : R.natDegree+1≤2*m) :
    integral R=0 := by
  obtain ⟨T,rfl⟩:=hd
  by_cases ht : T=0
  · simp [ht]
  have hm' : 0<m := by rcases hm with rfl|rfl|rfl|rfl <;>decide
  have degD := closed_lobatto_degree (K:=K) hm'
  have hn : (X-1)*lobatto (K:=K) m≠0 := fun e=>by rw [e,natDegree_zero] at degD;omega
  rw [natDegree_mul hn ht,degD] at deg
  exact closed_lobatto_orthogonal hm T (by omega)

/-- A congruence H₁ ≡ X H₀ modulo the closed grid shifts all paid moments,
up to the sharply truncated degree 2m−1. -/
theorem closed_lobatto_link_moment (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    {H₀ H₁ : K[X]} (h₀ : H₀.natDegree≤m) (h₁ : H₁.natDegree≤m)
    (link : (X-1)*lobatto m ∣ X*H₀-H₁) (k : ℕ) (pay : k+2≤m) :
    tailMoment (k+1) H₀=tailMoment k H₁ := by
  have eqn:=integral_zero_of_closed_lobatto_dvd hm (X^k*(X*H₀-H₁))
    (dvd_mul_of_dvd_right link _) (by
      apply Nat.add_le_add_right (natDegree_mul_le ..) 1 |>.trans
      rw [natDegree_X_pow]
      have a:=natDegree_mul_le (p:=X) (q:=H₀)
      rw [natDegree_X] at a
      have c:=natDegree_sub_le (X*H₀) H₁
      omega)
  rw [show X^k*(X*H₀-H₁)=X^(k+1)*H₀-X^k*H₁ by rw [pow_succ];ring,map_sub,sub_eq_zero] at eqn
  exact eqn

/-- A low-degree polynomial annihilator modulo the grid extends a prefix
of scalar moments through degree m−1. One clean endpoint then kills H.
This is a truncated recurrence, not a root count or a positivity argument. -/
theorem closed_lobatto_small_factor_detect
    (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10) {H Q : K[X]} {q : ℕ}
    (dH : H.natDegree≤m) (endpt : H.eval 0=0 ∨ H.eval 1=0)
    (paid : ∀n : ℕ, n≤q → tailMoment n H=0)
    (nz : Q≠0) (dQ : Q.natDegree≤q+1) (f : (X-1)*lobatto m ∣ Q*H) : H=0 := by
  have all (n : ℕ) (hn : n<m) : tailMoment n H=0 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hp : n≤q
      · exact paid n hp
      let k := n-Q.natDegree
      have ek : k+Q.natDegree=n := by dsimp [k];omega
      have v : tailMoment k (Q*H)=0 :=
        integral_zero_of_closed_lobatto_dvd hm (X^k*(Q*H)) (dvd_mul_of_dvd_right f _) (by
          have a:=natDegree_mul_le (p:=X^k) (q:=Q*H)
          have b:=natDegree_mul_le (p:=Q) (q:=H)
          rw [natDegree_X_pow] at a
          omega)
      rw [tailMoment_mul,Finset.sum_range_succ] at v
      have e : (∑ i ∈ Finset.range Q.natDegree, Q.coeff i * tailMoment (k+i) H)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have ji:=Finset.mem_range.mp hi
        have lt : k+i<n := by omega
        rw [ih _ lt (lt.trans hn),mul_zero]
      rw [e,zero_add,ek] at v
      exact (mul_eq_zero.mp v).resolve_left (leadingCoeff_ne_zero.mpr nz)
  apply endpoint_moment_detect (by rcases hm with rfl|rfl|rfl|rfl <;>decide) H dH endpt
  intro R dR
  have v:=tailMoment_mul 0 R H
  rw [show tailMoment 0 (R*H)=integral (H*R) by simp [tailMoment,mul_comm]] at v
  rw [v]
  apply Finset.sum_eq_zero
  intro i hi
  have lt:=Finset.mem_range.mp hi
  rw [all (0+i) (by omega),mul_zero]

end
end RKCert.Paired.Terminal
