module

public import RKCert.EndpointJacobiTwoRecurrence

@[expose] public section

/-! # Finite paid shifts of exact Jacobi moments

This is a low-moment argument over the field, not a recurrence computed
from approximate quadrature. It gives the high scalar part of three
paid squares and removes it for four paid mixed products.
-/
namespace RKCert.Paired
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def JacobiQuiet (P : K[X]) (d : ℕ) : Prop :=
  ∀ k : ℕ, k≤d → jacobiPair P (X^k)=0

theorem jacobiQuiet_extend {P : K[X]} {d : ℕ} (quiet : JacobiQuiet P d) :
    ∀ Q : K[X],Q.natDegree≤d → jacobiPair P Q=0 := by
  intro Q dQ
  let L := unitIntegral.comp (LinearMap.mulLeft K ((X*(1-X))*P))
  change L Q=0
  rw [Q.as_sum_range,map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul]
  have e : L (X^k)=0 := quiet k (by have := Finset.mem_range.mp hk; omega)
  rw [e,smul_zero]

theorem jacobiQuiet_step {R S G : K[X]} {d : ℕ} (a : K)
    (eq : S=X*R+C a*G) (zero : jacobiPair R 1=0)
    (qS : JacobiQuiet S d) (qG : JacobiQuiet G d) : JacobiQuiet R (d+1) := by
  intro k hk
  cases k with
  | zero => simpa only [pow_zero] using zero
  | succ j =>
    have h := qS j (by omega)
    rw [eq,jacobiPair_add,jacobiPair_C_mul,qG j (by omega),mul_zero,add_zero,jacobiPair_mul_X] at h
    rw [pow_succ']
    exact h

theorem jacobiQuiet_local {R G : K[X]} {d : ℕ} (a t : K)
    (eq : X*R=C a*R+C t*G) (zero : jacobiPair R 1=0)
    (qG : JacobiQuiet G d) : JacobiQuiet R (d+1) := by
  intro k hk
  induction k with
  | zero => simpa only [pow_zero] using zero
  | succ j ih =>
    rw [pow_succ',←jacobiPair_mul_X,eq,jacobiPair_add,jacobiPair_C_mul,jacobiPair_C_mul,
      qG j (by omega),ih (by omega),mul_zero,mul_zero,add_zero]

/-- The three adjacent paid scalar comparisons determine the first
polynomial up to the unique highest remaining basis vector. -/
theorem jacobiQuiet_three {G P₀ P₁ P₂ : K[X]} (a b : K)
    (e₀ : P₁=X*P₀+C a*G) (e₁ : P₂=X*P₁+C b*G)
    (d₀ : P₀.natDegree≤6)
    (q₀ : JacobiQuiet P₀ 3) (q₁ : JacobiQuiet P₁ 3) (q₂ : JacobiQuiet P₂ 3)
    (qG : JacobiQuiet G 5) :
    P₀=C (P₀.coeff 6)*jacobiTwo K 6 := by
  have one : jacobiPair P₀ 1=0 := by simpa only [pow_zero] using q₀ 0 (by decide)
  have two : jacobiPair P₁ 1=0 := by simpa only [pow_zero] using q₁ 0 (by decide)
  have q₁' := jacobiQuiet_step b e₁ two q₂ (fun k hk => qG k (hk.trans (by decide)))
  have q₀' := jacobiQuiet_step a e₀ one q₁' (fun k hk => qG k (hk.trans (by decide)))
  exact jacobiTwo_top_one (by decide : 0<6) d₀ (jacobiQuiet_extend q₀')

/-- Four correctly paid comparisons, with the genuine degree-seven
pencil, make every scalar part disappear. -/
theorem jacobiQuiet_four {G P₀ P₁ P₂ P₃ : K[X]} (a b c : K)
    (e₀ : P₁=X*P₀+C a*G) (e₁ : P₂=X*P₁+C b*G) (e₂ : P₃=X*P₂+C c*G)
    (dG : G.natDegree=7) (d₀ : P₀.natDegree≤6) (d₁ : P₁.natDegree≤6)
    (d₂ : P₂.natDegree≤6) (d₃ : P₃.natDegree≤6)
    (q₀ : JacobiQuiet P₀ 3) (q₁ : JacobiQuiet P₁ 3) (q₂ : JacobiQuiet P₂ 3)
    (q₃ : JacobiQuiet P₃ 3) (qG : JacobiQuiet G 5) :
    P₀=0 ∧ P₁=0 ∧ P₂=0 ∧ P₃=0 := by
  have z₀ : jacobiPair P₀ 1=0 := by simpa only [pow_zero] using q₀ 0 (by decide)
  have z₁ : jacobiPair P₁ 1=0 := by simpa only [pow_zero] using q₁ 0 (by decide)
  have z₂ : jacobiPair P₂ 1=0 := by simpa only [pow_zero] using q₂ 0 (by decide)
  have h₂ := jacobiQuiet_step c e₂ z₂ q₃ (fun k hk => qG k (hk.trans (by decide)))
  have h₁ := jacobiQuiet_step b e₁ z₁ h₂ (fun k hk => qG k (hk.trans (by decide)))
  have h₀ := jacobiQuiet_step a e₀ z₀ h₁ qG
  have p₀ := jacobiPair_detect P₀ d₀ (jacobiQuiet_extend h₀)
  have coal (z : K) (P : K[X]) (d : P.natDegree≤6) (eq : P=C z*G) : P=0 := by
    by_cases e : z=0
    · simp [eq,e]
    · rw [eq,natDegree_C_mul e,dG] at d
      contradiction
  have p₁ := coal a P₁ d₁ (by simpa only [p₀,mul_zero,zero_add] using e₀)
  have p₂ := coal b P₂ d₂ (by simpa only [p₁,mul_zero,zero_add] using e₁)
  have p₃ := coal c P₃ d₃ (by simpa only [p₂,mul_zero,zero_add] using e₂)
  exact ⟨p₀,p₁,p₂,p₃⟩

end
end RKCert.Paired
