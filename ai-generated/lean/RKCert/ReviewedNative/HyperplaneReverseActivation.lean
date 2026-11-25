module

public import RKCert.ReviewedNative.HyperplaneReverseCompression
public import RKCert.ReviewedNative.ReflectedPolynomialBudget
public import RKCert.ReviewedNative.NativePrimitiveMoments
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual quadrature and the physical singleton version of the class obstruction

The reviewed order supplies two different aggregate-output clocks. The only
geometric predicate remaining in a chosen class presentation is exclusion
of a class singleton at a supported reflected-zero class, which is vacuous
for the seven-clock ordinary pure case.
-/
namespace RKResearch.Certified.Graded.HyperplaneTerminal

open RKResearch Reverse Module Polynomial
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s n j p : ℕ}

theorem folded_distinct {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) (pay : 3≤p) (r : Fin s→Fin n)
    (y : Fin n→K) (cy : ∀i,y (r i)=reflectedClock A i) :
    ∃i v, folded r b i≠0 ∧ folded r b v≠0 ∧ y i≠y v := by
  let f := folded r b
  have mass (k : ℕ) (hk : k≤2) :
      ((k+1:ℕ):K)*(∑ h,f h*y h^k)=1 := by
    have h := reflected_power_mass ho k (by omega)
    have fold := folded_pair r b (fun h=>y h^k)
    simp only [row_apply,dotProduct] at fold
    simp_rw [cy] at fold
    change ((k+1:ℕ):K)*(∑ h,folded r b h*y h^k)=1
    rw [fold]
    simpa only [reflectedProbe,row_apply,dotProduct,pow_zero,Pi.one_apply,mul_one] using h
  have m₀ : (∑ h,f h)=1 := by simpa using mass 0 (by decide)
  have ex : ∃i,f i≠0 := by
    by_contra! z
    have bad : (0:K)=1 := by simpa [z] using m₀
    exact zero_ne_one bad
  obtain ⟨i,fi⟩:=ex
  by_contra no
  have same (h : Fin n) (fh : f h≠0) : y h=y i := by
    by_contra bad
    exact no ⟨h,i,fh,fi,bad⟩
  have collapse (k : ℕ) : (∑ h,f h*y h^k)=y i^k := by
    calc
      _ = ∑ h,f h*y i^k := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases z : f h=0
        · simp [z]
        · rw [same h z]
      _ = _ := by rw [←Finset.sum_mul,m₀,one_mul]
  have h₁ := mass 1 (by decide)
  have h₂ := mass 2 (by decide)
  rw [collapse,pow_one] at h₁
  rw [collapse] at h₂
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at h₁ h₂
  apply one_ne_zero (α:=K)
  linear_combination (6*y i+3)*h₁-4*h₂

theorem folded_singleton_impossible {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (e : Fin n→Fin s) (r : Fin s→Fin n)
    (ordered : Monotone e) (earlier : ∀i,e (r i) ≤ i)
    (y : Fin n→K) (cy : ∀i,y (r i)=reflectedClock A i)
    (H : Submodule K (Fin n→K)) (rankH : finrank K H+1=n)
    (before : ∀x∈H, (fun i=>x (r i))∈treeSpace A j)
    (same : ∀v∈treeSpace A (j+1), ∀i,v (e (r i))=v i)
    (pay : j+4≤p)
    (excluded : ∀i,folded r b i≠0 → y i=0 → coordinate (K:=K) i∉H) : False := by
  have room := finrank_annih H
  rw [Fintype.card_fin] at room
  have nonbot : annih H≠⊥ := by
    intro z
    rw [z,finrank_bot] at room
    omega
  obtain ⟨l,lin,ln⟩:=Submodule.exists_mem_ne_zero_of_ne_bot nonbot
  have eq : K ∙ l=annih H := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem ..).mpr lin
    · rw [finrank_span_singleton ln]
      omega
  apply folded_hyperplane_impossible ha ho e r ordered earlier y cy H rankH
    before same l lin ln pay _ (folded_distinct ho (by omega) r y cy)
  intro i live
  by_cases z : y i=0
  · right
    intro nz
    apply excluded i live z
    rw [←annih_annih H]
    apply mem_annih.mpr
    intro v hv
    rw [←eq] at hv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
    simp [nz]
  · exact Or.inl z

/-- In the ordinary degree-seven chart the physical root clock 1 is
forbidden by the existing endpoint Cauchy detector at precisely six tests. -/
theorem seven_paid_not_one {G : K[X]} (degree : G.natDegree=7)
    (origin : G.eval 0=0)
    (tests : ∀i : Fin 6,(primitive (X^i.val*G)).eval 1=0) : G.eval 1≠0 := by
  intro atOne
  obtain ⟨P,hP⟩ := (dvd_iff_isRoot (a:=(1:K))).mpr atOne
  have eq : G=(1-X)*(-P) := by rw [hP]; simp only [C_1]; ring
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at degree; omega
  have pn : -P≠0 := fun z=>gn (by rw [eq,z,mul_zero])
  have fn : (1-X:K[X])≠0 := by
    rw [show (1-X:K[X])=-(X-C 1) by simp]
    exact neg_ne_zero.mpr (X_sub_C_ne_zero _)
  have d₁ : (1-X:K[X]).natDegree=1 := by
    rw [show (1-X:K[X])=-(X-C 1) by simp,natDegree_neg,natDegree_X_sub_C]
  have d := degree
  rw [eq,natDegree_mul fn pn,d₁] at d
  have o : (-P).eval 0=0 := by simpa only [eq,eval_mul,eval_sub,eval_one,eval_X,sub_zero,one_mul] using origin
  exact pn (NativeMoments.endpoint_moments_detect (n:=6) (by omega) o
    (fun i=>by rw [←eq]; exact tests i))

end
end RKResearch.Certified.Graded.HyperplaneTerminal
