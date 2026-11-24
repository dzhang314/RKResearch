module
public import RKCert.ERKPhysicalContrasts
public import RKCert.CauchyKernel

@[expose] public section

/-! # Algebraic positive shifted Hilbert forms over ordered fields
The positive pivots of a Cauchy Gram form reduce it to the smaller
Cauchy Gram form by diagonal rescaling. No analytic integral, root
existence, completeness or positive RK output coefficient is assumed. -/
namespace RKCert.OrderedGram
open RKCert.Paired RKCert.Endpoint Polynomial
open scoped Classical
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def cauchyForm {n : ℕ} (x a : Fin n→K) : K :=
  ∑ i, ∑ j, a i*a j/(x i+x j)

private noncomputable def tailWeight {n:ℕ} (x a:Fin (n+1)→K) (i:Fin n) : K :=
  a i.succ/(x 0+x i.succ)

private noncomputable def tailColumn {n:ℕ} (x a:Fin (n+1)→K) (i:Fin n) : K :=
  tailWeight x a i*(x i.succ-x 0)

private theorem cauchy_square_split {n:ℕ} (x a : Fin (n+1)→K) (hx : ∀ i,0<x i) :
    cauchyForm x a=
      (a 0+(x 0+x 0)*(∑ i:Fin n,tailWeight x a i))^2/(x 0+x 0) +
        cauchyForm (fun i:Fin n=>x i.succ) (tailColumn x a) := by
  classical
  let h:=x 0+x 0
  let z:=∑ i:Fin n,tailWeight x a i
  let r (i j:Fin n):K := a i.succ*a j.succ/(x i.succ+x j.succ)
  have nz (i j:Fin (n+1)) : x i+x j≠0 := (add_pos (hx i) (hx j)).ne'
  have zR : (∑ i:Fin n,a 0*a i.succ/(x 0+x i.succ))=a 0*z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold tailWeight
    ring
  have zL : (∑ i:Fin n,a i.succ*a 0/(x i.succ+x 0))=a 0*z := by
    rw [←zR]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm (x i.succ) (x 0),mul_comm (a i.succ) (a 0)]
  have split : cauchyForm x a = a 0*a 0/h+a 0*z+a 0*z+∑ i:Fin n,∑ j:Fin n,r i j := by
    unfold cauchyForm
    simp only [Fin.sum_univ_succ (n:=n),Finset.sum_add_distrib,zR,zL,h,r,add_assoc]
  have pair (i j:Fin n) : r i j=
      (h*tailWeight x a i)*tailWeight x a j+
      tailColumn x a i*tailColumn x a j/(x i.succ+x j.succ) := by
    dsimp [r,h,tailColumn,tailWeight]
    field_simp [nz]
    ring
  have sep : (∑ i:Fin n,∑ j:Fin n,(h*tailWeight x a i)*tailWeight x a j)=h*z*z := by
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
  have blocks : (∑ i:Fin n,∑ j:Fin n,r i j)=h*z*z+
      cauchyForm (fun i:Fin n=>x i.succ) (tailColumn x a) := by
    simp only [pair,Finset.sum_add_distrib,sep,cauchyForm]
  rw [split,blocks]
  change a 0*a 0/h+a 0*z+a 0*z+(h*z*z+cauchyForm _ _)=
    (a 0+h*z)^2/h+cauchyForm _ _
  have hh:h≠0 := nz _ _
  field_simp [hh]
  ring

/-- Exact positivity of the Cauchy Gram matrix on distinct positive arguments. -/
theorem cauchyForm_pos {n:ℕ} (x a:Fin n→K) (hx:∀i,0<x i)
    (inj:Function.Injective x) (ha:a≠0) : 0<cauchyForm x a := by
  induction n with
  | zero =>
    exact (ha (funext (fun i=>Fin.elim0 i))).elim
  | succ n ih =>
    rw [cauchy_square_split x a hx]
    let y : Fin n→K := fun i=>x i.succ
    let b := tailColumn x a
    have hh : 0<x 0+x 0 := add_pos (hx 0) (hx 0)
    by_cases hb:b=0
    · have htail (i:Fin n) : a i.succ=0 := by
        have eq := congrFun hb i
        change a i.succ/(x 0+x i.succ)*(x i.succ-x 0)=0 at eq
        have hn : x i.succ-x 0≠0 := sub_ne_zero.mpr (fun h=>Fin.succ_ne_zero i (inj h))
        exact (div_eq_zero_iff.mp ((mul_eq_zero.mp eq).resolve_right hn)).resolve_right
          (add_pos (hx 0) (hx i.succ)).ne'
      have h0 : a 0≠0 := by
        intro eq
        apply ha
        funext i
        refine Fin.cases eq (fun j=>htail j) i
      have hs : (∑ i:Fin n,tailWeight x a i)=0 := by simp [tailWeight,htail]
      rw [hs,mul_zero,add_zero]
      have eq : cauchyForm y b=0 := by rw [hb];simp [cauchyForm]
      rw [show cauchyForm (fun i:Fin n=>x i.succ) (tailColumn x a)=0 from eq,add_zero]
      exact div_pos (sq_pos_of_ne_zero h0) hh
    · have hp := ih y b (fun i=>hx _) (fun _ _ e=>Fin.succ_injective _ (inj e)) hb
      exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hh.le) hp

section Bilinear
variable {F:Type*} [Field F] [DecidableEq F]

theorem unit_pow_bilinear {n m:ℕ} (a:Fin n→F) (b:Fin m→F) (k:ℕ) :
    (Paired.primitive (X^k*(ofFn n a*ofFn m b))).eval 1=
      ∑ i:Fin n,∑ j:Fin m,a i*b j/((i.val+j.val+k+1:ℕ):F) := by
  classical
  have ex : X^k*(ofFn n a*ofFn m b)=
      ∑ i:Fin n,∑ j:Fin m,monomial (i.val+j.val+k) (a i*b j) := by
    simp only [ofFn_eq_sum_monomial,Finset.sum_mul,Finset.mul_sum,monomial_mul_monomial,
      X_pow_mul_monomial]
    rw [Finset.sum_comm]
  rw [ex,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [primitive_monomial]

end Bilinear

/-- Strict positivity of the exact formal integral of x^k P(x)^2 on [0,1]. -/
theorem pow_square_pos (k:ℕ) (P:K[X]) (hP:P≠0) :
    0<(Paired.primitive (X^k*P^2)).eval 1 := by
  classical
  let a : Fin (P.natDegree+1)→K := fun i=>P.coeff i.val
  have re : ofFn (P.natDegree+1) a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have ha : a≠0 := by
    intro e
    apply hP
    rw [←re,e,map_zero]
  let x : Fin (P.natDegree+1)→K := fun i => (i.val:K)+((k+1:ℕ):K)/2
  have hx (i:Fin (P.natDegree+1)):0<x i :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg i.val) (div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (by norm_num))
  have inj : Function.Injective x := by
    intro i j eq
    have e : (i.val:K)=j.val := add_right_cancel eq
    exact Fin.ext (Nat.cast_injective e)
  have positive := cauchyForm_pos x a hx inj ha
  rw [pow_two,←re,unit_pow_bilinear]
  unfold cauchyForm at positive
  convert positive using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [x]
  push_cast
  ring

end RKCert.OrderedGram

