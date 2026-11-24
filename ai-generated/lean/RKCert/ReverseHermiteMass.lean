module
public import RKCert.ReverseHermitePrimitives

@[expose] public section
/-! # Two reverse chronological nodes must detect the physical weight vector -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired RKCert.Endpoint Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem two_failed_of_three_moments (c v : Vec K s) (U : Submodule K (Vec K s))
    (hm : MaskInvariant c U) (hmass : ∀u∈U, ∑i,u i=0)
    (m1 : ∑i,(c i)^1*v i=1/2) (m2 : ∑i,(c i)^2*v i=1/3) (m3 : ∑i,(c i)^3*v i=1/4) :
    2 ≤ (failedNodes c v U s).card := by
  classical
  by_contra! h
  obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega :
    (failedNodes c v U s).card≤1)
  have placed (Q : K[X]) (h0 : Q.eval 0=0) (hA : Q.eval a=0) :
      weightedEval c v Q ∈ U := by
    obtain ⟨w,hw,hh⟩ := exists_masked_prefix_lift c v hm s Q h0 (fun z hz => by
      have := Finset.mem_singleton.mp (ha hz); simpa [this] using hA)
    have he : w=weightedEval c v Q := by
      ext i; simpa only [weightedEval_apply] using hh i i.isLt
    exact he ▸ hw
  have h₂ := hmass _ (placed (X*(X-C a)) (by simp) (by simp))
  have h₃ := hmass _ (placed (X^2*(X-C a)) (by simp) (by simp))
  have k2 : ((∑i, c i^2*v i) - a*(∑i,c i*v i))=0 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    convert h₂ using 1
    apply Finset.sum_congr rfl
    intro i _; simp; ring
  have k3 : ((∑i, c i^3*v i) - a*(∑i,c i^2*v i))=0 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    convert h₃ using 1
    apply Finset.sum_congr rfl
    intro i _; simp; ring
  simp only [pow_one] at m1
  rw [m1,m2] at k2
  rw [m2,m3] at k3
  apply (one_ne_zero : (1:K)≠0)
  linear_combination 36*k3-24*k2

/-- The reflected scalar quadrature gives the same small ordinary power moments. -/
theorem mirror_moments {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (hp : 4≤p) :
    (∑i,(mirror A i)^1*b i)=1/2 ∧ (∑i,(mirror A i)^2*b i)=1/3 ∧
      (∑i,(mirror A i)^3*b i)=1/4 := by
  have sm (k : ℕ) : (∑i,(mirror A i)^k*b i)=row (reflWeight A b k) (1:Vec K s) := by
    simp only [row_apply,Pi.one_apply,mul_one,reflWeight,mirror,reflNode,Pi.sub_apply]
  have h (k : ℕ) (hk:k≤3) : probe A b k (1:Vec K s)=((1:K)+(k:K))⁻¹ := by
    simpa [normTree_leaf,Tree.order] using probe_norm_inv ho .leaf k (by change k+1≤p; omega)
  rw [sm 1,sm 2,sm 3,reflected_1,reflected_2,reflected_3]
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]
  norm_num

end RKCert.Paired.ReverseHull
