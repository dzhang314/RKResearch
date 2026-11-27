module

public import RKCert.ReviewedNative.DIRKOrderTenPaidDAField

@[expose] public section

/-! # Field gates for invisible nonconstant one-clock cubic defects

The companion proof supplies the exact active off-head pair and the
two zero-weight cubic core rows. These field lemmas replay the live
read and chronology cancellations, separately from tableau ranks. -/
namespace RKResearch.Certified.Graded.InvisibleOffSlackField

open Lean.Grind

section
variable {K : Type} [Field K]

private theorem scalar_cancel (a x : K) (ha : a ≠ 0) (h : a*x=0) : x=0 := by
  have ht := congrArg (fun z => a⁻¹*z) h
  rw [←Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul, Semiring.mul_zero] at ht
  exact ht

private theorem two_reads (a b x y : K) (hd : a-b ≠ 0)
    (h0 : x+y=0) (h1 : a*x+b*y=0) : x=0 ∧ y=0 := by
  have hz : (a-b)*x=0 := by grind
  have hx := scalar_cancel (a-b) x hd hz
  exact ⟨hx, by rw [hx,Semiring.add_comm (0:K) y,Semiring.add_zero] at h0; exact h0⟩

/-- A nonzero read on three distinct labels that kills degrees zero
and one has a nonzero value on every label. -/
theorem three_reads_live (a b c x y z : K) (hab : a-b ≠ 0)
    (hac : a-c ≠ 0) (hbc : b-c ≠ 0) (h0 : x+y+z=0)
    (h1 : a*x+b*y+c*z=0) (hn : ¬(x=0 ∧ y=0 ∧ z=0)) :
    x≠0 ∧ y≠0 ∧ z≠0 := by
  refine ⟨?_,?_,?_⟩
  · intro hx
    obtain ⟨hy,hz⟩ := two_reads b c y z hbc (by grind) (by grind)
    exact hn ⟨hx,hy,hz⟩
  · intro hy
    obtain ⟨hx,hz⟩ := two_reads a c x z hac (by grind) (by grind)
    exact hn ⟨hx,hy,hz⟩
  · intro hz
    obtain ⟨hx,hy⟩ := two_reads a b x y hab (by grind) (by grind)
    exact hn ⟨hx,hy,hz⟩

/-- The two physical dirty reads share xi, but the g moment ties them
before the h and Ch moments are taken. The third live aggregate is
the opposite pair's *combined* D read, not either of its taps. -/
theorem invisible_ghosts_and_pair_live
    (ξ ζ χ g₀ g₁ h₁ hζ hχ d₀ d₁ dζ dχ : K)
    (hxz : ξ-ζ ≠ 0) (hxc : ξ-χ ≠ 0) (hzc : ζ-χ ≠ 0)
    (ng₀ : g₀≠0) (ng₁ : g₁≠0) (nh₁ : h₁≠0) (nhζ : hζ≠0) (nhχ : hχ≠0)
    (hg : g₀*d₀+g₁*d₁=0)
    (hh : h₁*d₁+hζ*dζ+hχ*dχ=0)
    (hc : ξ*(h₁*d₁)+ζ*(hζ*dζ)+χ*(hχ*dχ)=0)
    (hn : ¬(d₀=0 ∧ d₁=0 ∧ dζ=0 ∧ dχ=0)) :
    d₀≠0 ∧ d₁≠0 ∧ dζ≠0 ∧ dχ≠0 := by
  have hnon : ¬(h₁*d₁=0 ∧ hζ*dζ=0 ∧ hχ*dχ=0) := by
    rintro ⟨hd₁,hdζ,hdχ⟩
    have t₁ := scalar_cancel h₁ d₁ nh₁ hd₁
    have tζ := scalar_cancel hζ dζ nhζ hdζ
    have tχ := scalar_cancel hχ dχ nhχ hdχ
    have t₀ := scalar_cancel g₀ d₀ ng₀ (by simpa [t₁,Semiring.mul_zero,Semiring.add_zero] using hg)
    exact hn ⟨t₀,t₁,tζ,tχ⟩
  obtain ⟨a,b,c⟩ := three_reads_live ξ ζ χ (h₁*d₁) (hζ*dζ) (hχ*dχ)
    hxz hxc hzc hh hc hnon
  have nz₁ : d₁≠0 := by intro e; exact a (by simp [e,Semiring.mul_zero])
  refine ⟨?_,nz₁,?_,?_⟩
  · intro e
    rw [e, Semiring.mul_zero, Semiring.add_comm (0:K) (g₁*d₁), Semiring.add_zero] at hg
    exact nz₁ (scalar_cancel g₁ d₁ ng₁ hg)
  · intro e
    exact b (by simp [e,Semiring.mul_zero])
  · intro e
    exact c (by simp [e,Semiring.mul_zero])

/-- The genuine latest reflected pivot normalizes both coefficients
of the active pair, even when neither row carries nonzero cubic g. -/
theorem normalize_pair_column (b₀ b₁ G₀ G₁ κ a₀ a₁ : K) (hκ : κ≠0)
    (hb : b₀+b₁=0) (hG : G₀+G₁=0) (hj : G₁=κ*b₁) :
    (G₀*a₀+G₁*a₁)/κ=b₀*a₀+b₁*a₁ := by
  have hi : G₀=κ*b₀ := by grind
  have h : G₀*a₀+G₁*a₁=(b₀*a₀+b₁*a₁)*κ := by rw [hi,hj]; grind
  rw [h,Field.div_eq_mul_inv,Semiring.mul_assoc,Field.mul_inv_cancel hκ,Semiring.mul_one]

/-- An ordinary suffix supported only on U,W cannot carry a nonzero
compensated scalar x from a ghost or the early active pair member. -/
theorem two_regular_columns_kill (V U W x : K)
    (hV : V≠0) (hVU : V-U≠0) (hUW : U/2-W≠0)
    (h : (V^3-V*(V-U)*(V-U/2))*x-(U+W)*(V^2*x)+(U*W)*(V*x)=0) :
    x=0 := by
  have h' : V*((V-U)*((U/2-W)*x))=0 := by
    calc
      _ = (V^3-V*(V-U)*(V-U/2))*x-(U+W)*(V^2*x)+(U*W)*(V*x) := by grind
      _ = 0 := h
  exact scalar_cancel (U/2-W) x hUW (scalar_cancel (V-U) _ hVU (scalar_cancel V _ hV h'))

end
end RKResearch.Certified.Graded.InvisibleOffSlackField
