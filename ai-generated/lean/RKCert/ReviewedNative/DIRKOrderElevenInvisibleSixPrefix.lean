module

public import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank
public import RKCert.ReviewedNative.GradedPrimitives
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Masked forward primitive and polynomial cut for six invisible ghosts -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixPrefix

open RKResearch Polynomial Reverse
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

private theorem primitive_degrees {P : K[X]} (nz : P≠0) :
    (primitive P).natDegree=P.natDegree+1 ∧
      (primitive P).natTrailingDegree=P.natTrailingDegree+1 := by
  have nonzero (i : ℕ) (h : P.coeff i≠0) : (primitive P).coeff (i+1)≠0 := by
    rw [primitive_coeff_succ]
    exact div_ne_zero h (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i))
  refine ⟨le_antisymm (primitive_natDegree_le le_rfl)
    (le_natDegree_of_ne_zero (nonzero _ (leadingCoeff_ne_zero.mpr nz))),?_⟩
  refine le_antisymm (natTrailingDegree_le_of_ne_zero
    (nonzero _ (mt coeff_natTrailingDegree_eq_zero.mp nz))) ?_
  by_contra! low
  have root : (primitive P).coeff (primitive P).natTrailingDegree≠0 :=
    mt coeff_natTrailingDegree_eq_zero.mp
      (fun h => nonzero P.natTrailingDegree (mt coeff_natTrailingDegree_eq_zero.mp nz) (by rw [h,coeff_zero]))
  cases ht : (primitive P).natTrailingDegree with
  | zero => exact root (by rw [ht,primitive_coeff_zero])
  | succ i =>
    rw [ht,primitive_coeff_succ,coeff_eq_zero_of_lt_natTrailingDegree (by omega),zero_div] at root
    exact root rfl

/-- A nonzero polynomial over characteristic zero can divide its
zero-constant primitive against a power weight only if it is a monomial.
No splitting field or ordering is needed. -/
theorem monomial_of_self_primitive_dvd {P : K[X]} (nz : P≠0) (m : ℕ)
    (div : P ∣ primitive (P*X^m)) :
    ∃ a : K, a≠0 ∧ P=C a*X^P.natDegree := by
  obtain ⟨Q,eq⟩ := div
  have pxz : P*X^m≠0 := mul_ne_zero nz (pow_ne_zero _ X_ne_zero)
  obtain ⟨nd,td⟩ := primitive_degrees pxz
  have qz : Q≠0 := by
    intro z
    rw [eq,z,mul_zero,natDegree_zero] at nd
    omega
  rw [eq,natDegree_mul nz qz,natDegree_mul nz (pow_ne_zero _ X_ne_zero),natDegree_X_pow] at nd
  rw [eq,natTrailingDegree_mul nz qz,natTrailingDegree_mul_X_pow nz] at td
  have qnd : Q.natDegree=m+1 := by omega
  have qtd : Q.natTrailingDegree=m+1 := by omega
  let a := Q.coeff (m+1)
  have qmono : Q=C a*X^(m+1) := by
    rw [C_mul_X_pow_eq_monomial]
    ext i
    rcases lt_trichotomy i (m+1) with lo|rfl|hi
    · rw [coeff_eq_zero_of_lt_natTrailingDegree (by omega)]
      simp [coeff_monomial,lo.ne]
    · simp [a]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [coeff_monomial,Ne.symm hi.ne]
  have cc (k : ℕ) (h : P.coeff k≠0) : a=((k+m+1:ℕ):K)⁻¹ := by
    have hE := congrArg (fun T : K[X] => T.coeff (k+m+1)) eq
    change (primitive (P*X^m)).coeff (k+m+1)=(P*Q).coeff (k+m+1) at hE
    rw [primitive_coeff_succ,coeff_mul_X_pow,qmono,mul_comm (C a) (X^(m+1)),
      ←mul_assoc,show k+m+1=k+(m+1) by omega,coeff_mul_C,coeff_mul_X_pow,div_eq_mul_inv] at hE
    exact (mul_left_cancel₀ h hE).symm
  have n0 : P.coeff P.natDegree≠0 := leadingCoeff_ne_zero.mpr nz
  refine ⟨P.coeff P.natDegree,n0,?_⟩
  rw [C_mul_X_pow_eq_monomial]
  ext k
  by_cases he : k=P.natDegree
  · subst k; simp
  · have zero : P.coeff k=0 := by
      by_contra hk
      have e := Nat.cast_injective (R:=K) (inv_injective ((cc k hk).symm.trans (cc _ n0)))
      exact he (by omega)
    simp [zero,coeff_monomial,he]

/-- With distinct anchors zero and x, a primitive of U*X*(X−x)
that vanishes also at x cannot be a multiple of nonzero U. Each
anchor would contribute two degrees to the quotient, which has
degree only three. -/
theorem two_anchor_primitive_not_divisible {U : K[X]} (uz : U≠0) (x : K) (x0 : x≠0)
    (root : (primitive (U*(X*(X-C x)))).IsRoot x) :
    ¬ U ∣ primitive (U*(X*(X-C x))) := by
  classical
  let B : K[X] := X*(X-C x)
  let F := primitive (U*B)
  have Xz : (X : K[X])≠0 := X_ne_zero
  have Bz : B≠0 := mul_ne_zero Xz (X_sub_C_ne_zero x)
  have BF := mul_ne_zero uz Bz
  intro div
  obtain ⟨Q,eq⟩ := div
  change F=U*Q at eq
  obtain ⟨fd,_⟩ := primitive_degrees BF
  have bd : B.natDegree=2 := by
    rw [show B=X*(X-C x) from rfl,natDegree_mul Xz (X_sub_C_ne_zero x),
      natDegree_X,natDegree_X_sub_C]
  have F0 : F≠0 := by
    intro e
    change F.natDegree=_ at fd
    rw [e,natDegree_zero] at fd
    omega
  have Q0 : Q≠0 := by
    intro hz
    apply F0
    rw [eq,hz,mul_zero]
  have qd : Q.natDegree=3 := by
    change F.natDegree=_ at fd
    rw [eq,natDegree_mul uz Q0,natDegree_mul uz Bz,bd] at fd
    omega
  have df : F.derivative=U*B := by
    ext i
    rw [show F=primitive (U*B) from rfl,coeff_derivative,primitive_coeff_succ]
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ ((U*B).coeff i)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i) : ((i+1:ℕ):K)≠0)
  have hf0 : F.IsRoot 0 := by simp [F,IsRoot,←coeff_zero_eq_eval_zero]
  have hfx : F.IsRoot x := root
  have bm0 : B.rootMultiplicity 0=1 := by
    rw [show B=(X-C 0)*(X-C x) by simp [B],
      rootMultiplicity_mul (by simpa [B] using Bz),rootMultiplicity_X_sub_C,rootMultiplicity_X_sub_C]
    simp [Ne.symm x0]
  have bmx : B.rootMultiplicity x=1 := by
    rw [show B=(X-C 0)*(X-C x) by simp [B],
      rootMultiplicity_mul (by simpa [B] using Bz),rootMultiplicity_X_sub_C,rootMultiplicity_X_sub_C]
    simp [x0]
  have mul (y : K) (hr : F.IsRoot y) (bm : B.rootMultiplicity y=1) :
      Q.rootMultiplicity y=2 := by
    have h := derivative_rootMultiplicity_of_root hr
    rw [df,rootMultiplicity_mul BF,bm,eq,rootMultiplicity_mul (mul_ne_zero uz Q0)] at h
    omega
  have div0 : (X-C 0)^2 ∣ Q := (le_rootMultiplicity_iff Q0).mp (by rw [mul 0 hf0 bm0])
  have divx : (X-C x)^2 ∣ Q := (le_rootMultiplicity_iff Q0).mp (by rw [mul x hfx bmx])
  have co : IsCoprime (X-C 0 : K[X]) (X-C x) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    simpa using (neg_ne_zero.mpr x0).isUnit
  have both := co.pow.mul_dvd div0 divx
  have hd := natDegree_le_of_dvd both Q0
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero 0))
      (pow_ne_zero _ (X_sub_C_ne_zero x)),natDegree_pow,natDegree_X_sub_C,natDegree_pow,
      natDegree_X_sub_C,qd] at hd
  omega

omit [CharZero K] in
/-- Causal prefix vanishing drops a degree-bounded ghost-polynomial
relation to actual polynomial divisibility. -/
theorem self_primitive_dvd_of_many_ghosts {P Q : K[X]} (m : ℕ)
    {ι : Type*} [Fintype ι] (clocks : ι→K) (distinct : Function.Injective clocks)
    (dq : Q.natDegree≤m+1) (big : P.natDegree+m+1<Fintype.card ι)
    (hg : ∀ i, (primitive (P*X^m)).eval (clocks i)+P.eval (clocks i)*Q.eval (clocks i)=0) :
    P ∣ primitive (P*X^m) := by
  let T := primitive (P*X^m)+P*Q
  have dB : (P*X^m).natDegree≤P.natDegree+m :=
    natDegree_mul_le.trans (by rw [natDegree_X_pow])
  have dQ : (P*Q).natDegree≤P.natDegree+m+1 :=
    (natDegree_mul_le (p:=P) (q:=Q)).trans (by omega)
  have dT : T.natDegree≤P.natDegree+m+1 := by
    simpa only [max_self] using (natDegree_add_le_of_le (primitive_natDegree_le dB) dQ)
  have ze : T=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero T distinct
    (fun i => by simpa [T] using hg i) (dT.trans_lt big)
  refine ⟨-Q,?_⟩
  rw [mul_neg]
  exact eq_neg_of_add_eq_zero_left ze

/-- Direct actual rooted-budget bridge: subtracting a defect from its
clock representative does not change the scalar primitive profile. -/
theorem masked_primitive_actual {ι : Type*} [Fintype ι]
    {A : Matrix ι ι K} {b : ι → K} {p : ℕ} (ho : HasOrder p A b)
    {g : ι→K} (hg : g∈zeroSpace A 3) (U : K[X]) (du : U.natDegree≤3) (j : ℕ)
    (pay : j+5≤p) :
    mat A ((evalNodes A U - g)*evalNodes A (X^j)) -
        evalNodes A (primitive (U*X^j)) ∈ zeroSpace A (j+4) := by
  have hX : (X^j : K[X]).natDegree≤j := by rw [natDegree_X_pow]
  have UX : (U*X^j).natDegree≤3+j := natDegree_mul_le_of_le du hX
  have prim := primitive_defect A (U*X^j) UX
  have mark := zeroSpace_mul_treeSpace ho (by omega : j+1≤p) hg
    (evalNodes_mem_treeSpace A (X^j) hX)
  have unary := mat_zeroSpace_charZero A (3+j) mark
  have goal := (zeroSpace A (3+j+1)).sub_mem prim unary
  have e : evalNodes A (U*X^j)=evalNodes A U*evalNodes A (X^j) := by
    ext i
    simp
  rw [e] at goal
  rw [show j+4=3+j+1 by omega,sub_mul,map_sub]
  have v :
      mat A (evalNodes A U * evalNodes A (X^j)) -
            mat A (g * evalNodes A (X^j)) - evalNodes A (primitive (U*X^j)) =
      mat A (evalNodes A U * evalNodes A (X^j)) -
            evalNodes A (primitive (U*X^j)) - mat A (g * evalNodes A (X^j)) := by abel
  rwa [v]

/-- The masked profile's two scalar moments cannot be paid by the single
literal clean diagonal when a nonconstant monomial already kills the
origin contribution. -/
theorem single_diagonal_two_powers (x d : K) (j : ℕ) (x0 : x≠0)
    (h0 : d*x^j=x^(j+1)/((j+1:ℕ):K))
    (h1 : d*x^(j+1)=x^(j+2)/((j+2:ℕ):K)) : False := by
  have z1 : ((j+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have z2 : ((j+2:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have t := congrArg (fun a : K => a*x) h0
  change d*x^j*x=(x^(j+1)/((j+1:ℕ):K))*x at t
  rw [mul_assoc,←pow_succ,div_mul_eq_mul_div,←pow_succ,h1] at t
  rw [div_eq_mul_inv,div_eq_mul_inv] at t
  have E := Nat.cast_injective (R:=K) (inv_injective ((mul_left_cancel₀ (pow_ne_zero _ x0) t)))
  omega

omit [CharZero K] in
/-- At six distinct ghost samples a true degree-five terminal head
cannot be covered by a cubic residual; the head coefficient and
the residual polynomial both vanish. -/
theorem no_cubic_cancel_six_ghosts (H Q : K[X]) (hd : H.natDegree=5)
    (qd : Q.natDegree≤3) (a : K)
    (clocks : Fin 6→K) (distinct : Function.Injective clocks)
    (rows : ∀ i, Q.eval (clocks i)=a*H.eval (clocks i)) :
    a=0 ∧ Q=0 := by
  let F := Q-C a*H
  have bc : (C a*H).natDegree≤5 :=
    (natDegree_mul_le (p:=C a) (q:=H)).trans (by rw [natDegree_C,hd,zero_add])
  have deg : F.natDegree≤5 := natDegree_sub_le_of_le (qd.trans (by decide : 3≤5)) bc
  have Fz : F=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero F distinct
    (fun i => by simp [F,rows i]) (by rw [Fintype.card_fin]; omega)
  have hh : Q=C a*H := sub_eq_zero.mp Fz
  by_cases az : a=0
  · exact ⟨az,by simpa [az] using hh⟩
  · rw [hh,natDegree_C_mul az,hd] at qd
    omega

omit [CharZero K] in
/-- Graded product debit underlying the reciprocal clean-head profile:
multiplying a true grade-seven annihilator by a real column of grade
three yields an annihilator of the whole true grade-four space. -/
theorem weighted_mask_annih_four {ι : Type*} [Fintype ι] {A : Matrix ι ι K}
    {G m : ι→K} (hG : G∈annih (treeSpace A 7)) (hm : m∈treeSpace A 3) :
    G*m∈annih (treeSpace A 4) := by
  apply mem_annih.mpr
  intro v hv
  have H := mem_annih.mp hG (m*v) (treeSpace_mul hm hv)
  rw [row_apply,dotProduct] at H ⊢
  simpa only [Pi.mul_apply,mul_assoc] using H

end RKResearch.Certified.Graded.OrderElevenInvisibleSixPrefix
