module
public import RKCert.LobattoTailRecurrence

@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {m q r : ℕ} {H H₀ H₁ H₂ : K[X]}

/-- Degree-m trace tail with two clean endpoint rows and a paid prefix
of moments numbered 0 through q inclusive. -/
structure LobattoPaidTail (m q : ℕ) (H : K[X]) : Prop where
  degree : H.natDegree≤m
  atZero : H.eval 0=0
  atOne : H.eval 1=0
  paid : ∀ k : ℕ, k≤q → tailMoment k H=0

namespace LobattoPaidTail

/-- Propagate an entire paid prefix backwards through a multiplication-by-x
congruence, not just its last payment. -/
theorem extend_of_link (h₀ : LobattoPaidTail m q H₀) (h₁ : LobattoPaidTail m r H₁)
    (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (pay : r+2≤m)
    (h : (X-1)*lobatto m ∣ X*H₀-H₁) : LobattoPaidTail m (r+1) H₀ := by
  refine ⟨h₀.degree,h₀.atZero,h₀.atOne,?_⟩
  intro n hn
  cases n with
  | zero => exact h₀.paid 0 (Nat.zero_le _)
  | succ k =>
    exact (closed_lobatto_link_moment hm h₀.degree h₁.degree h k (by omega)).trans (h₁.paid k (by omega))

/-- m−1 paid rows and the two zero endpoints suffice without positivity. -/
theorem eq_zero (h : LobattoPaidTail m q H) (enough : m≤q+2) : H=0 :=
  two_endpoint_moment_detect H h.degree h.atZero h.atOne (fun k hk=>h.paid k (by omega))

/-- A factor of degree q+1 or less suffices for a shorter tail. -/
theorem eq_zero_of_factor (h : LobattoPaidTail m q H) (hm : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    {Q : K[X]} (nz : Q≠0) (deg : Q.natDegree≤q+1) (dvd : (X-1)*lobatto m ∣ Q*H) : H=0 :=
  closed_lobatto_small_factor_detect hm h.degree (Or.inl h.atZero) h.paid nz deg dvd

/-- A vanishing preceding tail propagates forward along the same congruence
by the strict degree gap between a tail and the full closed grid. -/
theorem eq_zero_of_prev (h₁ : LobattoPaidTail m r H₁) (hm : 0<m) (hz : H₀=0)
    (h : (X-1)*lobatto m ∣ X*H₀-H₁) : H₁=0 := by
  have v : (X-1)*lobatto m ∣ H₁ := by simpa only [hz,mul_zero,zero_sub,dvd_neg] using h
  by_contra hn
  have le:=natDegree_le_of_dvd v hn
  rw [closed_lobatto_degree hm] at le
  have:=h₁.degree
  omega

end LobattoPaidTail

/-- The direct p14/p16 one-root cardinal congruence. -/
theorem lobatto_tail_linear (hm : m=7 ∨ m=8)
    (h : LobattoPaidTail m (2*m-11) H) (a : K)
    (link : (X-1)*lobatto m ∣ (X-C a)*H) : H=0 := by
  apply h.eq_zero_of_factor (by rcases hm with h|h;exact Or.inl h;exact Or.inr (Or.inl h)) (X_sub_C_ne_zero a) _ link
  rw [natDegree_X_sub_C]
  omega

/-- Order fourteen: two successive closed-grid congruences force all
three scalar tails to vanish. -/
theorem lobatto7_tail_two_links
    (h₀ : LobattoPaidTail 7 3 H₀) (h₁ : LobattoPaidTail 7 3 H₁)
    (h₂ : LobattoPaidTail 7 3 H₂)
    (a : (X-1)*lobatto 7 ∣ X*H₀-H₁) (b : (X-1)*lobatto 7 ∣ X*H₁-H₂) :
    H₀=0 ∧ H₁=0 ∧ H₂=0 := by
  have z:=((h₀.extend_of_link (h₁.extend_of_link h₂ (Or.inl rfl) (by decide) b)
    (Or.inl rfl) (by decide) a).eq_zero (by decide))
  have z' := h₁.eq_zero_of_prev (by decide) z a
  exact ⟨z,z',h₂.eq_zero_of_prev (by decide) z' b⟩

/-- Order sixteen: a single closed-grid congruence forces both scalar tails to vanish. -/
theorem lobatto8_tail_one_link
    (h₀ : LobattoPaidTail 8 5 H₀) (h₁ : LobattoPaidTail 8 5 H₁)
    (a : (X-1)*lobatto 8 ∣ X*H₀-H₁) : H₀=0 ∧ H₁=0 := by
  have z:=(h₀.extend_of_link h₁ (Or.inr (Or.inl rfl)) (by decide) a).eq_zero (by decide)
  exact ⟨z,h₁.eq_zero_of_prev (by decide) z a⟩

/-- Order sixteen: even a degree-six polynomial factor suffices. In particular
this includes every nonzero cubic in the singleton-cardinal case. -/
theorem lobatto8_tail_short_factor (h : LobattoPaidTail 8 5 H) {Q : K[X]} (nz : Q≠0)
    (deg : Q.natDegree≤6) (dvd : (X-1)*lobatto 8 ∣ Q*H) : H=0 :=
  h.eq_zero_of_factor (Or.inr (Or.inl rfl)) nz deg dvd

end
end RKCert.Paired.Terminal
