module

public import RKCert.DirkFiveJets

@[expose] public section

/-! # Genuine ordinary polynomial traces
A polynomial companion is accompanied by a certificate in the actual
same-order tree-difference span. No uniqueness of the polynomial profile is
needed at grades beyond ordinary separation. -/

namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] {s p n m : ℕ}
variable {A : Fin s → Fin s → K} {b v : Vec K s}
variable {P Q : K[X]}

structure OrdinaryTrace (A : Fin s → Fin s → K) (n : ℕ) (v : Vec K s) (P : K[X]) : Prop where
  degree : P.natDegree≤n
  pure : v-evalNodes A P∈zeroSpace A n

namespace OrdinaryTrace

theorem mono (h : OrdinaryTrace A n v P) (hn : n≤m) : OrdinaryTrace A m v P :=
  ⟨h.degree.trans hn,zeroSpace_mono A hn h.pure⟩

theorem scalar (A : Fin s → Fin s → K) (hP : P.natDegree≤n) :
    OrdinaryTrace A n (evalNodes A P) P :=
  ⟨hP,by rw [sub_self]; exact (zeroSpace A n).zero_mem⟩

theorem stage (h : OrdinaryTrace A n v P) : v∈treeSpace A n := by
  have hp := evalNodes_mem_treeSpace A P h.degree
  have hf := zeroSpace_le_treeSpace A n h.pure
  simpa only [sub_add_cancel] using (treeSpace A n).add_mem hf hp

theorem sub_pure (h : OrdinaryTrace A n v P) {w : Vec K s} (hw : w∈zeroSpace A n) :
    OrdinaryTrace A n (v-w) P := by
  refine ⟨h.degree,?_⟩
  convert (zeroSpace A n).sub_mem h.pure hw using 1
  abel

theorem add_pure (h : OrdinaryTrace A n v P) {w : Vec K s} (hw : w∈zeroSpace A n) :
    OrdinaryTrace A n (v+w) P := by
  simpa only [sub_neg_eq_add] using h.sub_pure ((zeroSpace A n).neg_mem hw)

theorem add (h : OrdinaryTrace A n v P) {w : Vec K s} (h' : OrdinaryTrace A n w Q) :
    OrdinaryTrace A n (v+w) (P+Q) := by
  refine ⟨Polynomial.natDegree_add_le_of_degree_le h.degree h'.degree,?_⟩
  convert (zeroSpace A n).add_mem h.pure h'.pure using 1
  ext i
  simp only [Pi.add_apply,Pi.sub_apply,evalNodes_apply,eval_add]
  ring

theorem sub (h : OrdinaryTrace A n v P) {w : Vec K s} (h' : OrdinaryTrace A n w Q) :
    OrdinaryTrace A n (v-w) (P-Q) := by
  refine ⟨(Polynomial.natDegree_sub_le P Q).trans (max_le h.degree h'.degree),?_⟩
  convert (zeroSpace A n).sub_mem h.pure h'.pure using 1
  ext i
  simp only [Pi.sub_apply,evalNodes_apply,eval_sub]
  ring

theorem smul (h : OrdinaryTrace A n v P) (a : K) :
    OrdinaryTrace A n (a • v) (C a*P) := by
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.degree,?_⟩
  convert (zeroSpace A n).smul_mem a h.pure using 1
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,evalNodes_apply,eval_mul,eval_C]
  ring

theorem pure_zero (h : OrdinaryTrace A n v 0) : v∈zeroSpace A n := by
  have e : evalNodes A (0:K[X])=0 := by ext i; simp
  simpa only [e,sub_zero] using h.pure

theorem clock (h : OrdinaryTrace A n v P) :
    OrdinaryTrace A (n+1) (diag (nodes A) v) (X*P) := by
  refine ⟨Polynomial.natDegree_mul_le.trans (by rw [natDegree_X]; have := h.degree; omega),?_⟩
  have hm := diag_zeroSpace A n h.pure
  change diag (nodes A) (v-evalNodes A P) ∈ zeroSpace A (n+1) at hm
  rw [map_sub] at hm
  convert hm using 1
  ext i
  simp [eval_mul]

theorem primitive [CharZero K] (h : OrdinaryTrace A n v P) :
    OrdinaryTrace A (n+1) (mat A v) (formalPrimitive P) := by
  refine ⟨(natDegree_formalPrimitive_le _).trans (Nat.add_le_add_right h.degree 1),?_⟩
  rw [formalPrimitive_eq_treePrimitive]
  have hv := mat_zeroSpace_charZero A n h.pure
  change mat A (v-evalNodes A P)∈zeroSpace A (n+1) at hv
  rw [map_sub] at hv
  have hp := primitive_defect A P h.degree
  convert (zeroSpace A (n+1)).add_mem hv hp using 1
  abel

end OrdinaryTrace

/-- This commutator identity is formal over the coefficient field. -/
theorem primitive_commutation [CharZero K] (P : K[X]) :
    X*formalPrimitive P-formalPrimitive (X*P)-formalPrimitive (formalPrimitive P)=0 := by
  apply eq_of_derivative_and_eval_zero
  · simp only [derivative_sub,derivative_mul,derivative_X,one_mul,
      derivative_formalPrimitive,derivative_zero]
    abel
  · simp

/-- Primitive of a clock-masked polynomial computed at any coefficient,
without an analytic path or sign condition. -/
theorem primitive_eval_power_mul [CharZero K] (P : K[X]) (u : K) (k : ℕ) {d : ℕ}
    (hd : P.natDegree≤d) :
    (formalPrimitive (X^k*P)).eval u =
      ∑ j : Fin (d+1), P.coeff j.val * u^(k+j.val+1) / ((k+j.val+1:ℕ):K) := by
  have hs : X^k*P=∑ j : Fin (d+1), monomial (k+j.val) (P.coeff j.val) := by
    conv_lhs => rw [P.as_sum_range' _ (Nat.lt_succ_of_le hd)]
    rw [Finset.mul_sum,Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [←monomial_one_right_eq_X_pow,monomial_mul_monomial,one_mul]
  rw [hs,formalPrimitive_eq_treePrimitive,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [primitive_monomial,eval_monomial,div_mul_eq_mul_div,mul_comm]

/-- All available shifted primitive tests at any nonzero endpoint detect a
polynomial of the given degree; the inverse is a shifted Hilbert matrix. -/
theorem primitive_shift_detect [CharZero K] (P : K[X]) {d k : ℕ} (hd : P.natDegree≤d)
    (u : K) (hu : u≠0)
    (he : ∀ i : Fin (d+1), (formalPrimitive (X^(k+i.val)*P)).eval u=0) : P=0 := by
  let a : Fin (d+1) → K := fun j => P.coeff j.val*u^j.val
  have det := shifted_hilbert_kernel (k+1) (by omega) a ?_
  · ext j
    by_cases h : j<d+1
    · have e : a ⟨j,h⟩=0 := congrFun det ⟨j,h⟩
      exact (mul_eq_zero.mp e).resolve_right (pow_ne_zero _ hu)
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).trans (coeff_zero _).symm
  · intro i
    have h := he i
    rw [primitive_eval_power_mul P u _ hd] at h
    apply mul_left_cancel₀ (pow_ne_zero (k+i.val+1) hu)
    rw [mul_zero,Finset.mul_sum,←h]
    apply Finset.sum_congr rfl
    intro j _
    have hc : k+i.val+j.val+1 = i.val+j.val+(k+1) := by omega
    have heq : k+i.val+j.val+1 = (k+i.val+1)+j.val := by omega
    rw [mul_div_assoc,←hc,heq,pow_add]
    ring

namespace OrdinaryTrace

theorem probe [CharZero K] (h : OrdinaryTrace A n v P) (ho : HasTreeOrderAtLeast A b p)
    (k : ℕ) (hk : k+n+1≤p) :
    Paired.probe A b k v = (formalPrimitive (X^k*P)).eval 1 := by
  have h0 := probe_zeroSpace ho hk h.pure
  change Paired.probe A b k (v-evalNodes A P)=0 at h0
  rw [map_sub,sub_eq_zero] at h0
  rw [h0,evalNodes_eq_polyEval A P h.degree,probe_polyEval ho hk,
    primitive_eval_power_mul P _ _ h.degree]
  simp only [one_pow,mul_one]

theorem zero_numeric [CharZero K] {d k : ℕ}
    (h : OrdinaryTrace A n (0:Vec K s) (X^k*P)) (hd : P.natDegree≤d)
    (ho : HasTreeOrderAtLeast A b p) (hp : d+n+1≤p) : P=0 := by
  apply primitive_shift_detect P hd 1 one_ne_zero
  intro i
  have ew := h.probe ho i.val (by omega)
  simpa only [map_zero,←mul_assoc,←pow_add,Nat.add_comm i.val k] using ew.symm

end OrdinaryTrace
end RKCert.Paired
