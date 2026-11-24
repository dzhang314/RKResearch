module

public import RKCert.DirkMarkedBudget

@[expose] public section

/-! # Arbitrary paid polynomial primitives on actual reverse rows
The formal primitive is algebraic over a characteristic-zero field.
An integration-by-parts identity is proved as a polynomial identity,
then fed the actual full tree moment equations. No coefficient is divided
by an output weight. -/
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p n : ℕ}
variable {A : Fin s → Fin s → K} {b v w : Vec K s}
variable {P Q F : K[X]}

def pairEval (c b v : Vec K s) : K[X] →ₗ[K] K :=
  (Module.Dual.eval K (Vec K s) v).comp (rowL.comp (weightedEval c b))

omit [CharZero K] in
theorem pairEval_apply (c b v : Vec K s) (Q : K[X]) :
    pairEval c b v Q = row (weightedEval c b Q) v := rfl

omit [CharZero K] in
theorem pairEval_pow (A : Fin s → Fin s → K) (b v : Vec K s) (k : ℕ) :
    pairEval (nodes A) b v (X^k)=probe A b k v := by
  rw [pairEval_apply,probe]
  congr 1
  ext i
  simp [mul_comm]

/-- A polynomial spectator may be paired against any genuine ordinary
trace. The degree bound pays all monomials simultaneously. -/
theorem OrdinaryTrace.pair_polynomial (h : OrdinaryTrace A n v F) (ho : HasTreeOrderAtLeast A b p)
    (Q : K[X]) (hpay : n+Q.natDegree+1≤p) :
    row (weightedEval (nodes A) b Q) v = (formalPrimitive (F*Q)).eval 1 := by
  let L := pairEval (nodes A) b v
  let M := (leval (1:K)).comp (formalPrimitiveLinear.comp (LinearMap.mulLeft K F))
  change L Q=M Q
  conv_lhs => rw [Q.as_sum_range]
  conv_rhs => rw [Q.as_sum_range]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤Q.natDegree := by have := Finset.mem_range.mp hj; omega
  have he : monomial j (Q.coeff j) = Q.coeff j • (X^j:K[X]) := by
    rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial]
  rw [he,map_smul,map_smul]
  congr 1
  change pairEval (nodes A) b v (X^j) = (formalPrimitive (F*X^j)).eval 1
  rw [pairEval_pow,h.probe ho j (by omega),mul_comm]

def reflectPolynomial (P : K[X]) : K[X] := P.comp (1-X)

omit [CharZero K] in
theorem reflectPolynomial_degree (P : K[X]) :
    (reflectPolynomial P).natDegree≤P.natDegree := by
  have hX : (1-X:K[X]).natDegree≤1 := by
    have h := natDegree_sub_le (1:K[X]) X
    simpa only [natDegree_one,natDegree_X,zero_le,max_eq_right] using h
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hX).trans_eq (Nat.mul_one _))

omit [CharZero K] in
theorem weightedEval_reflect (A : Fin s → Fin s → K) (b : Vec K s) (P : K[X]) :
    weightedEval (mirror A) b P=weightedEval (nodes A) b (reflectPolynomial P) := by
  ext i
  simp [reflectPolynomial,Polynomial.eval_comp,mirror,Pi.sub_apply]

/-- Formal integration by parts with the two boundary values already
cancelled: the identity holds over every characteristic-zero field. -/
theorem reflected_primitive_pair (P Q : K[X]) :
    (formalPrimitive (P*reflectPolynomial (formalPrimitive Q))).eval 1 =
      (formalPrimitive (formalPrimitive P*reflectPolynomial Q)).eval 1 := by
  have he : formalPrimitive (P*reflectPolynomial (formalPrimitive Q)) -
      formalPrimitive (formalPrimitive P*reflectPolynomial Q) =
        formalPrimitive P * reflectPolynomial (formalPrimitive Q) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_sub,derivative_formalPrimitive,derivative_formalPrimitive,derivative_mul,
        derivative_formalPrimitive]
      unfold reflectPolynomial
      rw [derivative_comp_one_sub_X,derivative_formalPrimitive]
      ring
    · simp only [eval_sub,formalPrimitive_eval_zero,sub_self,eval_mul,zero_mul]
  have h := congrArg (Polynomial.eval (1:K)) he
  simp only [eval_sub,eval_mul,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,sub_self,
    formalPrimitive_eval_zero,mul_zero] at h
  exact sub_eq_zero.mp h

theorem reflectPolynomial_integral (Q : K[X]) :
    (formalPrimitive (reflectPolynomial Q)).eval 1=(formalPrimitive Q).eval 1 := by
  have he : formalPrimitive (reflectPolynomial Q) =
      C ((formalPrimitive Q).eval 1)-reflectPolynomial (formalPrimitive Q) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive,derivative_sub,derivative_C]
      unfold reflectPolynomial
      rw [derivative_comp_one_sub_X,derivative_formalPrimitive,sub_neg_eq_add,zero_add]
    · simp [reflectPolynomial,eval_comp]
  rw [he,eval_sub,eval_C,reflectPolynomial,eval_comp]
  simp

/-- A reversed primitive defect of any PAID degree annihilates every
ordinary column of complementary grade, not only a monomial or leaf. -/
theorem weighted_reverse_primitive (ho : HasTreeOrderAtLeast A b p) (hd : P.natDegree≤n)
    (hn : n+2≤p) :
    transMat A (weightedEval (mirror A) b P) -
      weightedEval (mirror A) b (formalPrimitive P) ∈ marked A p (n+1) := by
  apply mem_annih.mpr
  intro x hx
  let g := p-1-(n+1)
  change x∈treeSpace A g at hx
  obtain ⟨Q,hQ,hxQ⟩ := exists_poly_zeroSpace_charZero A hx
  have ht : OrdinaryTrace A g x Q := ⟨hQ,hxQ⟩
  have hP' := (reflectPolynomial_degree P).trans hd
  have hJ' := (reflectPolynomial_degree (formalPrimitive P)).trans
    ((natDegree_formalPrimitive_le _).trans (Nat.add_le_add_right hd 1))
  change rowL (transMat A (weightedEval (mirror A) b P) -
    weightedEval (mirror A) b (formalPrimitive P)) x=0
  rw [map_sub,LinearMap.sub_apply,rowL_apply,rowL_apply,row_flip_mat,
    weightedEval_reflect,weightedEval_reflect,
    ht.primitive.pair_polynomial ho _ (by dsimp [g]; omega),
    ht.pair_polynomial ho _ (by dsimp [g]; omega),
    ←reflected_primitive_pair Q P,sub_self]

structure ReverseTrace (A : Fin s → Fin s → K) (b : Vec K s) (p n : ℕ)
    (w : Vec K s) (P : K[X]) : Prop where
  degree : P.natDegree≤n
  pure : w-weightedEval (mirror A) b P∈marked A p n

namespace ReverseTrace

omit [CharZero K] in
theorem mono {m : ℕ} (h : ReverseTrace A b p n w P) (hn : n≤m) : ReverseTrace A b p m w P :=
  ⟨h.degree.trans hn,marked_mono A p hn h.pure⟩

omit [CharZero K] in
theorem sub_pure (h : ReverseTrace A b p n w P) {r : Vec K s} (hr : r∈marked A p n) :
    ReverseTrace A b p n (w-r) P := by
  refine ⟨h.degree,?_⟩
  convert (marked A p n).sub_mem h.pure hr using 1
  abel

omit [CharZero K] in
theorem sub (h : ReverseTrace A b p n w P) {r : Vec K s} (hr : ReverseTrace A b p n r Q) :
    ReverseTrace A b p n (w-r) (P-Q) := by
  refine ⟨(natDegree_sub_le P Q).trans (max_le h.degree hr.degree),?_⟩
  rw [map_sub]
  convert (marked A p n).sub_mem h.pure hr.pure using 1
  abel

omit [CharZero K] in
theorem scalar (A : Fin s → Fin s → K) (b : Vec K s) (hP : P.natDegree≤n) :
    ReverseTrace A b p n (weightedEval (mirror A) b P) P :=
  ⟨hP,by rw [sub_self]; exact (marked A p n).zero_mem⟩

omit [CharZero K] in
theorem pure_zero (h : ReverseTrace A b p n w 0) : w∈marked A p n :=
  by simpa only [map_zero,sub_zero] using h.pure

omit [CharZero K] in
theorem clock (h : ReverseTrace A b p n w P) (hn : n+2≤p) :
    ReverseTrace A b p (n+1) (diag (mirror A) w) (X*P) := by
  have hd := natDegree_mul_le (p:=(X:K[X])) (q:=P)
  rw [natDegree_X] at hd
  have he : weightedEval (mirror A) b (X*P) =
      diag (mirror A) (weightedEval (mirror A) b P) := by
    ext i
    simp [mul_assoc]
  refine ⟨hd.trans (by have := h.degree; omega),?_⟩
  rw [he,←map_sub]
  exact marked_clock hn h.pure

theorem primitive (h : ReverseTrace A b p n w P) (ho : HasTreeOrderAtLeast A b p)
    (hn : n+2≤p) : ReverseTrace A b p (n+1) (transMat A w) (formalPrimitive P) := by
  refine ⟨(natDegree_formalPrimitive_le _).trans (Nat.add_le_add_right h.degree 1),?_⟩
  have hm := marked_mat hn h.pure
  change transMat A (w-weightedEval (mirror A) b P)∈marked A p (n+1) at hm
  rw [map_sub] at hm
  convert (marked A p (n+1)).add_mem hm (weighted_reverse_primitive ho h.degree hn) using 1
  abel

theorem commutator (h : ReverseTrace A b p n w P) (ho : HasTreeOrderAtLeast A b p)
    (hn : n+3≤p) :
    commutatorR (transMat A) (diag (mirror A)) w∈marked A p (n+2) := by
  have hh := (((h.primitive ho (by omega)).clock (by omega)).sub
    ((h.clock (by omega)).primitive ho (by omega))).sub
    ((h.primitive ho (by omega)).primitive ho (by omega))
  rw [primitive_commutation] at hh
  exact hh.pure_zero

theorem weighted_sum (h : ReverseTrace A b p n w P) (ho : HasTreeOrderAtLeast A b p)
    (hn : n+1≤p) :
    row w 1=(formalPrimitive P).eval 1 := by
  have H : OrdinaryTrace A 0 (1:Vec K s) 1 := by
    convert OrdinaryTrace.scalar A (P:=(1:K[X])) (n:=0) (by simp) using 1
    ext i; simp
  have hdiff := leaf_marked_zero h.pure
  change rowL (w-weightedEval (mirror A) b P) 1=0 at hdiff
  rw [map_sub,LinearMap.sub_apply,rowL_apply,rowL_apply,sub_eq_zero,weightedEval_reflect,
    H.pair_polynomial ho _ (by have := reflectPolynomial_degree P; have := h.degree; omega),
    one_mul,reflectPolynomial_integral] at hdiff
  exact hdiff

theorem weighted_moment (h : ReverseTrace A b p n w P) (ho : HasTreeOrderAtLeast A b p)
    (k : ℕ) (hn : k+n+1≤p) :
    row w (fun i => mirror A i^k) = (formalPrimitive (X^k*P)).eval 1 := by
  induction k generalizing n w P with
  | zero => simpa [pow_zero] using h.weighted_sum ho (by omega)
  | succ k ih =>
    have ht := h.clock (by omega)
    have eq : (fun i => mirror A i^(k+1)) = diag (mirror A) (fun i => mirror A i^k) := by
      ext i; simp [pow_succ']
    rw [eq,←row_flip_diag,ih ht (by omega)]
    congr 2
    rw [pow_succ,mul_assoc]

end ReverseTrace
end
end RKCert.Paired
