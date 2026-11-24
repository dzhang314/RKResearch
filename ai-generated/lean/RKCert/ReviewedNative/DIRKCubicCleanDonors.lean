module

public import RKCert.ReviewedNative.DIRKCubicPivots

@[expose] public section

/-! # Bounding the native cubic clean donor cut by exact polynomial tests -/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.Endpoint RKCert.OneEscape Signature
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {w : Fin s → K}

local notation "B" => fold A w

theorem fold_clean_primitive
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    {k : ℕ} (hk : k≤2) {f q : K[X]} (df : f.natDegree≤3+k) (dq : q.natDegree≤k)
    {i : Fin s} (clean : w i=0) :
    mat B (headInput A w f q) i=(primitive f).eval (nodes A i) := by
  obtain ⟨r,_,eq⟩ := headInput_mat (band k (by omega)) (band (k+1) (by omega)) df dq
  rw [fold_mat_headInput,eq,headInput_apply,clean,mul_zero,add_zero]

/-- At a first clean nonzero stage with zero diagonal at least four
different dirty signatures have live taps. Over C(2), a single paid
linear clock input suffices to turn the tap count into a contradiction. -/
theorem first_clean_taps_not_three (ha : A.IsLowerTriangular)
    (c₂ : monomialStageDefect A 1=0)
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    {i : Fin s} (wi : w i=0) (ci : nodes A i≠0)
    (diag0 : B i i=0) (pre : ∀ j < i, w j=0 → nodes A j=0)
    (D : Finset (Fin s)) (small : D.card≤3) (dist : Set.InjOn (nodes A) D)
    (cover : ∀ j < i, w j≠0 → B i j≠0 → j∈D) : False := by
  have lu : (B).IsLowerTriangular := fold_lower ha
  have zd (j : Fin s) (hj : j < i) (wj : w j≠0) : B i j=0 := by
    by_contra nz
    have jm := cover j hj wj nz
    let r : Fin s → K := fun k => if k=j then 1 else 0
    let q := Lagrange.interpolate D (nodes A) r
    have deg : q.natDegree≤2 := by
      by_cases eq : q=0
      · simp [eq]
      have deg := (natDegree_lt_iff_degree_lt eq).mpr (Lagrange.degree_interpolate_lt r dist)
      omega
    let v := headInput A w 0 q
    have evalq (a : Fin s) (am : a∈D) : v a=r a*w a := by
      have e : q.eval (nodes A a)=r a := Lagrange.eval_interpolate_at_node r dist am
      simp [v,e]
    have ox : mat B v i=0 := by
      rw [show v=headInput A w 0 q from rfl,fold_clean_primitive band (k:=2) (by decide)
        (by simp) deg wi,map_zero,eval_zero]
    have eq := mat_single_tap B v i j (fun k ne => by
      rcases lt_trichotomy k i with hki|rfl|hik
      · by_cases w0 : w k=0
        · simp [v,w0]
        by_cases b0 : B i k=0
        · simp [b0]
        · rw [evalq k (cover k hki w0 b0)]
          simp [r,ne]
      · simp [diag0]
      · rw [lu hik,zero_mul])
    rw [ox,evalq j jm] at eq
    simp only [r,ite_true,one_mul] at eq
    exact mul_ne_zero nz wj eq.symm
  have ac : mat B (nodes A) i=0 := by
    rw [mat_apply,Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro j _
    rcases lt_trichotomy j i with low|rfl|high
    · by_cases w0 : w j=0
      · rw [pre j low w0,mul_zero]
      · rw [zd j low w0,zero_mul]
    · rw [diag0,zero_mul]
    · rw [lu high,zero_mul]
  have clock : mat B (nodes A)=mat A (nodes A) :=
    fold_mat (w:=w) (fun j => congrArg Prod.fst (first_signature (nodes A) w j))
  rw [clock] at ac
  have z := congrFun c₂ i
  change (2:K) * (A *ᵥ (nodes A)^1) i - (nodes A i)^2 = 0 at z
  rw [pow_one] at z
  have av : (A *ᵥ nodes A) i=0 := ac
  rw [av,mul_zero,zero_sub,neg_eq_zero] at z
  exact (pow_ne_zero 2 ci) z

/-- An origin-cleared test for two nonzero clocks: its derivative vanishes
at both, its primitive at the earlier one, and the latter primitive does
not vanish. The construction spends degree four, no resultant. -/
theorem two_clock_separating_primitive (u v : K) (vn : v≠0) (sep : v≠u) :
    ∃ f : K[X], f.natDegree≤4 ∧ f.eval 0=0 ∧ f.eval u=0 ∧ f.eval v=0 ∧
      (primitive f).eval u=0 ∧ (primitive f).eval v≠0 := by
  let H : K[X] := X^2*(X-C u)^2
  have Hv : H.eval v≠0 := by
    simp only [H,eval_mul,eval_pow,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (pow_ne_zero _ vn) (pow_ne_zero _ (sub_ne_zero.mpr sep))
  let a := H.derivative.eval v/H.eval v
  let L : K[X] := 1-C a*(X-C v)
  let J := H*L
  let f := J.derivative
  have Hdeg : H.natDegree≤4 := by
    apply natDegree_mul_le.trans
    rw [Polynomial.natDegree_pow,Polynomial.natDegree_pow,natDegree_X,natDegree_X_sub_C]
  have Ldeg : L.natDegree≤1 := by
    have d : (C a*(X-C v)).natDegree≤1 :=
      (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C v).le
    exact (natDegree_sub_le _ _).trans (max_le (by simp) d)
  have Jdeg : J.natDegree≤5 := natDegree_mul_le.trans (by omega)
  have fdeg : f.natDegree≤4 := (natDegree_derivative_le J).trans (by omega)
  have J0 : J.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; simp [J,H]
  have prim : primitive f=J := primitive_derivative J J0
  refine ⟨f,fdeg,?_,?_,?_,?_,?_⟩
  · simp [f,J,H,derivative_mul,derivative_pow]
  · simp [f,J,H,derivative_mul,derivative_pow]
  · have ev : L.eval v=1 := by simp [L]
    have der : L.derivative.eval v= -a := by simp [L,derivative_mul]
    change (H*L).derivative.eval v=0
    rw [derivative_mul,eval_add,eval_mul,eval_mul,ev,der,mul_one,mul_neg,mul_comm (H.eval v) a]
    rw [show a*H.eval v=H.derivative.eval v from div_mul_cancel₀ _ Hv,add_neg_cancel]
  · rw [prim]; simp [J,H]
  · rw [prim]; simpa [J,L] using Hv

end RKResearch.Certified.Graded.HeadFiber
