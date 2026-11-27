module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! Lift a simple square root across an ideal whose elements are
nilpotent. Newton iteration squares the residual. No completeness,
ordered field, or domain is needed. -/

namespace RKResearch.Certified
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem sqrt_lift_nilpotent_ideal (I : Ideal R)
    (hI : ∀ e ∈ I, IsNilpotent e) (a s₀ : R)
    (he : s₀*s₀-a ∈ I) (u : IsUnit ((2:R)*s₀)) :
    ∃ s : R, s*s=a ∧ s-s₀∈I := by
  have loop : ∀ (n : ℕ) (s : R), (s*s-a)^n=0 → s*s-a∈I →
      IsUnit ((2:R)*s) → ∃ z : R, z*z=a ∧ z-s∈I := by
    intro n
    induction n with
    | zero =>
      intro s hn _ _
      simp at hn
    | succ n ih =>
      intro s hn he hu
      by_cases hz : n=0
      · subst n
        exact ⟨s,sub_eq_zero.mp (by simpa using hn),by simp⟩
      obtain ⟨e,he'⟩ := hu
      let d : R := (↑(e⁻¹):R)
      have hd : ((2:R)*s)*d=1 := by rw [←he']; exact e.mul_inv
      let h : R := (s*s-a)*d
      let t : R := s-h
      have hm : h∈I := by simpa only [h,mul_comm] using I.mul_mem_left d he
      have ht : t-s∈I := by
        have eq : t-s = -h := by dsimp [t]; ring
        exact eq ▸ I.neg_mem hm
      have heq : t*t-a=h^2 := by
        have hg : ((2:R)*s)*h=s*s-a := by
          dsimp [h]
          calc
            _ = ((2:R)*s*d)*(s*s-a) := by ring
            _ = _ := by rw [hd,one_mul]
        calc
          _ = (s*s-a)-((2:R)*s)*h+h^2 := by dsimp [t]; ring
          _ = _ := by rw [hg,sub_self,zero_add]
      have htI : t*t-a∈I := by rw [heq,pow_two]; exact I.mul_mem_left _ hm
      have htU : IsUnit ((2:R)*t) := by
        have heq' : (2:R)*t = (2:R)*s + -((2:R)*h) := by dsimp [t]; ring
        rw [heq']
        exact (hI _ (I.neg_mem (I.mul_mem_left 2 hm))).isUnit_add_left_of_commute
          ⟨e,he'⟩ (Commute.all _ _)
      have hzero : (t*t-a)^n=0 := by
        rw [heq,←pow_mul,show 2*n = (n+1)+(n-1) by omega]
        dsimp [h]
        rw [pow_add,mul_pow,hn,zero_mul,zero_mul]
      obtain ⟨z,hz₁,hz₂⟩ := ih t hzero htI htU
      refine ⟨z,hz₁,?_⟩
      have eq : z-s=(z-t)+(t-s) := by ring
      rw [eq]
      exact I.add_mem hz₂ ht
  obtain ⟨n,hn⟩ := hI _ he
  exact loop n s₀ hn he u

end RKResearch.Certified
