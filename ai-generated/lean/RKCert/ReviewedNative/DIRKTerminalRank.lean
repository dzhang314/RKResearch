module

public import RKCert.ReviewedNative.DIRKUniform

public section

/-! # One extra unanchored moment earns the physical end coordinate

The first reverse space either has positive rank, or D(1) and D(2) vanish
and its entire orbit avoids the last live coordinate. A certificate that a
live coordinate at clock 1 lies outside the forward space therefore earns
exactly one dimension. The boundary may be anchored by an actual zero row,
or, independently, by one additional paid ordinary probe.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}

/-- A square shifted Cauchy test on differences from the zeroth row
excludes a nonzero common moment with no origin assumption. The top
denominator is exactly 2n. -/
theorem paid_unanchored_constant_cauchy {ι : Type*} [Fintype ι]
    {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder A b p) {n : ℕ} (pay : 2*n ≤ p)
    (a : Fin n → K) (B : K)
    (test : ∀ i : Fin (n+1), (∑ j : Fin n, a j/((i.val+j.val+1:ℕ):K))=B) :
    B=0 := by
  let w : Fin n → K := fun j => a j / ((j.val+1:ℕ):K)
  have nz (k : ℕ) (lk : 0 < k) (uk : k ≤ p) : (k:K) ≠ 0 :=
    (ho.natCast_isUnit lk uk).ne_zero
  have first : (∑ j : Fin n, a j/((j.val+1:ℕ):K))=B := by
    simpa only [Fin.val_zero,zero_add] using test (0 : Fin (n+1))
  have ker (i : Fin n) : (∑ j : Fin n, w j / ((i.val+j.val+2:ℕ):K))=0 := by
    have xi := nz (i.val+1) (by omega) (by have := i.isLt; omega)
    apply mul_left_cancel₀ xi
    rw [mul_zero,Finset.mul_sum]
    have term (j : Fin n) :
        ((i.val+1:ℕ):K) * (w j/((i.val+j.val+2:ℕ):K)) =
          a j/((j.val+1:ℕ):K) - a j/((i.val+j.val+2:ℕ):K) := by
      have h₁ := nz (j.val+1) (by omega) (by have := j.isLt; omega)
      have h₂ := nz (i.val+j.val+2) (by omega) (by have := i.isLt; have := j.isLt; omega)
      dsimp [w]
      field_simp
      push_cast
      ring
    have step : (∑ j : Fin n, a j/((i.val+j.val+2:ℕ):K)) = B := by
      convert test i.succ using 2 with j
      congr 2
      simp only [Fin.val_succ]
      omega
    rw [Finset.sum_congr rfl (fun j _ => term j),Finset.sum_sub_distrib,first,step,sub_self]
  have zero := moments_detect ho (n:=n) (d:=2) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) w ker
  change (∑ j : Fin n, w j) = B at first
  simpa [zero] using first.symm

/-- One additional ordinary moment excludes the terminal coordinate from
the forward midpoint, without requiring *any* row of the tableau to vanish. -/
theorem endpoint_coordinate_out_unanchored {ι : Type*} [Fintype ι]
    {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder A b p) {q : ℕ}
    (pay : 2*q+2 ≤ p) {t : ι} (live : b t ≠ 0) (one : nodes A t = 1) :
    coordinate (K:=K) t ∉ treeSpace A q := by
  classical
  intro ht
  rw [treeSpace_coeff_sup ho (by omega)] at ht
  obtain ⟨v,hv,f,hf,e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨a,rfl⟩ := hv
  apply live
  apply paid_unanchored_constant_cauchy ho (n:=q+1) (by omega) a
  intro i
  have test := congrArg (probe A b i.val) e
  have f0 : probe A b i.val f = 0 := probe_zeroSpace ho (by have := i.isLt; omega) hf
  have ct : probe A b i.val (coordinate t) = b t := by
    change row _ (coordinate t) = b t
    rw [row_coordinate,one,one_pow,mul_one]
  rwa [map_add,f0,add_zero,probe_coeffEval ho (by have := i.isLt; omega),ct] at test

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Generic last-coordinate refund. The outside test is only requested
at the true last active index and only after its node has been forced to 1. -/
theorem dirk_reverse_room_of_endpoint (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} (hn : 1 ≤ n) (pay : q+n+2 ≤ p)
    (out : ∀ t : Fin s, LastActive b t → nodes A t=1 → coordinate (K:=K) t ∉ treeSpace A q) :
    finrank K (treeSpace A q)+n ≤ s := by
  by_cases rb : finrank K (primitiveBack A b 1)=0
  · obtain ⟨h₁,h₂⟩ := dirk_primitiveBack_one_zero rb
    obtain ⟨t,L⟩ := exists_lastActive ho (by omega)
    have node : nodes A t = 1 := (sub_eq_zero.mp (L.dirk_reflected_zero ha h₁ h₂)).symm
    have cut : primitiveBack A b n ≤ zeroAt (annih (treeSpace A q)) t := by
      intro v hv
      exact mem_zeroAt.mpr ⟨primitiveBack_annih ho q n pay hv,
        mem_tailZero.mp (L.dirk_primitiveBack_tail ha h₁ h₂ n hv) t le_rfl⟩
    have inc := Submodule.finrank_mono cut
    have one := finrank_zeroAt_annih (treeSpace A q) t (out t L node)
    have cap := finrank_annih (treeSpace A q)
    rw [Fintype.card_fin] at cap
    have grow := dirk_primitiveBack_rank_gain ha ho (r:=1) (by decide) hn (by omega)
    omega
  · have raw := dirk_reverse_rank_budget ha ho hn pay
    omega

theorem dirk_reverse_room_anchored (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} (hn : 1 ≤ n) (pay : q+n+2 ≤ p) (mid : 2*q+1 ≤ p)
    {o : Fin s} (hr : ∀ j, A o j=0) : finrank K (treeSpace A q)+n ≤ s :=
  dirk_reverse_room_of_endpoint ha ho hn pay
    (fun _ L node => endpoint_coordinate_out_of_zero_row ho mid hr L.live node)

theorem dirk_reverse_room_unanchored (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} (hn : 1 ≤ n) (pay : q+n+2 ≤ p) (mid : 2*q+2 ≤ p) :
    finrank K (treeSpace A q)+n ≤ s :=
  dirk_reverse_room_of_endpoint ha ho hn pay
    (fun _ L node => endpoint_coordinate_out_unanchored ho mid L.live node)

end RKResearch.Certified.Graded.Reverse
