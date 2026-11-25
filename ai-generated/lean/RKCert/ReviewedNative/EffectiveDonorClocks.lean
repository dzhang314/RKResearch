module

public import RKCert.ReviewedNative.GradedPrimitives
import RKCert.ReviewedNative.GradedSeparation
import RKCert.NodalPrimitive
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid effective nonzero clock count, without positivity

Grouping takes place in the exact signed moments, not in the tableau.
The omitted support is killed by a monic nodal polynomial, and the
resulting shifted system is the checked native Cauchy kernel.
-/
namespace RKResearch.Certified.Graded.EffectiveDonors

open RKResearch Polynomial RKCert.Endpoint
open scoped BigOperators Classical
noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Signed aggregate weight at one numerical clock. -/
def clockMass (c w : ι→K) (x : K) : K := by
  classical
  exact ∑ i,if c i=x then w i else 0

/-- Only nonzero clocks with a nonzero signed aggregate are effective. -/
def sites (c w : ι→K) : Finset K := by
  classical
  exact (Finset.univ.image c).filter fun x=>x≠0 ∧ clockMass c w x≠0

theorem mem_sites {c w : ι→K} {x : K} :
    x∈sites c w ↔ (∃ i,c i=x) ∧ x≠0 ∧ clockMass c w x≠0 := by
  classical
  simp [sites,Finset.mem_image]

theorem clockMass_scale (c w : ι→K) {a : K} (ha : a≠0) (b y : K) :
    clockMass (fun i=>a*c i) (fun i=>b*w i) (a*y)=b*clockMass c w y := by
  classical
  simp only [clockMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases eq : c i=y
  · simp [eq]
  · have ne : a*c i≠a*y := fun h=>eq (mul_left_cancel₀ ha h)
    simp [eq,ne]

private theorem sum_by_clock (c w : ι→K) (f : K→K) :
    (∑ i,w i*f (c i))=∑ x∈Finset.univ.image c,clockMass c w x*f x := by
  classical
  let S : Finset K := Finset.univ.image c
  calc
    _ = ∑ i : ι, ∑ x∈S, if c i=x then w i*f x else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have mem : c i∈S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rw [Finset.sum_eq_single (c i)]
      · simp
      · intro x _ off
        simp [Ne.symm off]
      · intro off
        exact (off mem).elim
    _ = ∑ x∈S, ∑ i : ι, if c i=x then w i*f x else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [clockMass,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases atX : c i=x <;> simp [atX]

omit [Fintype ι] in
private theorem primitive_shifted_coeffs {P : K[X]} {n : ℕ}
    (pd : P.natDegree<n) (k : ℕ) :
    (primitive (X^(k+1)*P)).eval 1 =
      ∑ j : Fin n,P.coeff j.val/((k+j.val+2:ℕ):K) := by
  conv_lhs => rw [P.as_sum_range' n pd]
  rw [Finset.mul_sum,map_sum,eval_finsetSum,
    Fin.sum_univ_eq_sum_range (fun j=>P.coeff j/((k+j+2:ℕ):K)) n]
  apply Finset.sum_congr rfl
  intro j _
  simp only [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one,
    Nat.cast_add,Nat.cast_one]
  ring

/-- Every finite cover of the effective nonzero clocks of a paid native
quadrature contains at least half as many clocks as its order. -/
theorem cover_card_of_hasOrder {A : Matrix ι ι K} {w : ι→K} {q : ℕ}
    (ho : HasOrder q A w) (D : Finset K)
    (covers : ∀ x, (∃ i,nodes A i=x) → x≠0 → x∉D → clockMass (nodes A) w x=0) :
    q/2≤D.card := by
  classical
  by_contra no
  let n := q/2
  have small : D.card<n := lt_of_not_ge no
  have pay : 2*n≤q := by dsimp [n]; omega
  let N := nodalHull D
  have hn : N.natDegree<n := (natDegree_nodalHull D).trans_lt small
  have nonzero : N≠0 := (monic_nodalHull D).ne_zero
  have zeroProbe (k : ℕ) : probe A w (k+1) (evalNodes A N)=0 := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,mul_assoc]
    rw [sum_by_clock (nodes A) w (fun x=>x^(k+1)*N.eval x)]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases x0 : x=0
    · simp [x0,pow_succ]
    by_cases inside : x∈D
    · have root : N.eval x=0 := nodalHull_eval_of_mem inside
      simp [root]
    · obtain ⟨i,_,cx⟩ := Finset.mem_image.mp hx
      rw [covers x ⟨i,cx⟩ x0 inside,zero_mul]
  have tests (k : Fin n) : (∑ j : Fin n,N.coeff j.val/((k.val+j.val+2:ℕ):K))=0 := by
    have hk := k.isLt
    have paid := probe_evalNodes ho N (k.val+1) (by omega)
    rw [zeroProbe k.val,primitive_shifted_coeffs hn k.val] at paid
    exact paid.symm
  have coeffs := moments_detect ho (n:=n) (d:=2) (by decide) (by omega)
    (fun i j=>by have hi := i.isLt; have hj := j.isLt; omega)
    (fun j=>N.coeff j.val) tests
  apply nonzero
  ext j
  rw [coeff_zero]
  by_cases hj : j<n
  · exact coeffs ⟨j,hj⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem card_of_hasOrder {A : Matrix ι ι K} {w : ι→K} {q : ℕ}
    (ho : HasOrder q A w) : q/2≤(sites (nodes A) w).card := by
  classical
  apply cover_card_of_hasOrder ho
  intro x occupied nonzero outside
  by_contra live
  exact outside (mem_sites.mpr ⟨occupied,nonzero,live⟩)

end
end RKResearch.Certified.Graded.EffectiveDonors
