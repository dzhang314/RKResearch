module

public import RKCert.ERKOrderNineFiveSixFG
public import RKCert.ReverseHermitePrimitives

@[expose] public section

/-! # Two paid reflected primitive steps and the Hankel collision -/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]

/-- The two reflected moments of the next image cannot shift the
nonvanishing Hankel quadrature knot. Only the displayed four scalar
relations are used. -/
theorem reflected_collision_scalar (κ lam η u m₂ m₃ m₄ : K)
    (f₂ : (1+3*κ)*m₃=3*κ*(1-η)*m₂)
    (f₃ : (1+4*κ)*m₄=4*κ*(1-η)*m₃)
    (g₁ : (1+2*lam)*m₃=3*lam*(1-u)*m₂)
    (g₂ : (1+3*lam)*m₄=4*lam*(1-u)*m₃)
    (hne : u≠η) : m₂*m₄-m₃^2=0 := by
  by_contra n
  have kn : κ≠0 := by
    intro e
    simp [e] at f₂ f₃
    exact n (by simp [f₂,f₃])
  have ln : lam≠0 := by
    intro e
    simp [e] at g₁ g₂
    exact n (by simp [g₁,g₂])
  have de : 3*m₂*m₄-4*m₃^2=-12*κ*(m₂*m₄-m₃^2) := by
    linear_combination 3*m₂*f₃-4*m₃*f₂
  have dn : 3*m₂*m₄-4*m₃^2≠0 := by
    rw [de]
    exact mul_ne_zero (mul_ne_zero (by norm_num) kn) n
  let x := κ*lam*(u-η)
  let y := lam-κ+κ*lam
  have e₁ : 3*m₂*x=m₃*y := by
    dsimp [x,y]
    linear_combination κ*g₁-lam*f₂
  have e₂ : 4*m₃*x=m₄*y := by
    dsimp [x,y]
    linear_combination κ*g₂-lam*f₃
  have h := (mul_eq_zero.mp (show (3*m₂*m₄-4*m₃^2)*x=0 by
    linear_combination m₄*e₁-m₃*e₂)).resolve_left dn
  exact (mul_ne_zero (mul_ne_zero kn ln) (sub_ne_zero.mpr hne)) h

variable {s p : ℕ}

omit [CharZero K] in
theorem reflected_weight_clock_shift (A : Fin s→Fin s→K)
    (b f : Vec K s) (k : ℕ) (η : K) :
    row (reflWeight A b k) (diag (nodes A) f-η • f)=
      (1-η)*row (reflWeight A b k) f-row (reflWeight A b (k+1)) f := by
  simp only [reflWeight,reflNode,row_apply,Finset.mul_sum,←Finset.sum_sub_distrib,diag_apply,
    Pi.smul_apply,smul_eq_mul,Pi.sub_apply,pow_succ]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [CharZero K] in
theorem reflect_end_single {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    (end_clock : nodes A (Fin.last s)=1) (k : ℕ) (kn : k≠0) :
    row (reflWeight A b k) (Pi.single (Fin.last s) 1)=0 := by
  rw [row_single_eq_coord]
  simp [reflWeight,reflNode,end_clock,kn]

/-- Actual order-nine tableau version of the two-operator collision.
No assumption is needed on the polynomial representative of f here. -/
theorem reflected_paid_two_step_collision {A : Fin (s+1)→Fin (s+1)→K}
    {b f : Vec K (s+1)} (ho : HasTreeOrderAtLeast A b 9)
    (hf : f∈treeSpace A 4) (end_clock : nodes A (Fin.last s)=1)
    {η u κ lam t t' : K} (hne : u≠η)
    (fA : mat A f=κ • (diag (nodes A) f-η • f)+t • Pi.single (Fin.last s) 1)
    (wA : mat A (diag (nodes A) f-η • f)=
      lam • (diag (nodes A) (diag (nodes A) f-η • f)-u • (diag (nodes A) f-η • f))+
        t' • Pi.single (Fin.last s) 1) :
    row (reflWeight A b 2) f*row (reflWeight A b 4) f-(row (reflWeight A b 3) f)^2=0 := by
  let w := diag (nodes A) f-η • f
  let μ (k : ℕ) := row (reflWeight A b k) f
  let ν (k : ℕ) := row (reflWeight A b k) w
  have hw : w∈treeSpace A 5 := (treeSpace A 5).sub_mem (diag_treeSpace A 4 hf)
    ((treeSpace A 5).smul_mem _ (treeSpace_mono A (by decide) hf))
  have nuEq (j : ℕ) : ν j=(1-η)*μ j-μ (j+1) := reflected_weight_clock_shift A b f j η
  have step1 (j : ℕ) (hj : j≤3) (hj0 : j≠0) :
      μ (j+1)=((j+1:ℕ):K)*κ*ν j := by
    have e := mem_annih.mp (ReverseHull.reflected_annih ho (j:=4) hj (by omega)) f hf
    rw [reflected_apply,fA,map_add,map_smul,map_smul,reflect_end_single end_clock _ hj0,
      smul_zero,add_zero,smul_eq_mul,sub_eq_zero] at e
    simpa [w,μ,ν,mul_assoc] using e.symm
  have step2 (j : ℕ) (hj : j≤2) (hj0 : j≠0) :
      (1+((j+1:ℕ):K)*lam)*ν (j+1)=((j+1:ℕ):K)*lam*(1-u)*ν j := by
    have e := mem_annih.mp (ReverseHull.reflected_annih ho (j:=5) (by omega : j≤3) (by omega)) w hw
    change mat A w=_ at wA
    rw [reflected_apply,wA,map_add,map_smul,map_smul,reflect_end_single end_clock _ hj0,
      smul_zero,add_zero,smul_eq_mul,reflected_weight_clock_shift] at e
    change _ * (lam*((1-u)*ν j-ν (j+1)))-ν (j+1)=0 at e
    linear_combination -e
  have f1 : μ 2=2*κ*ν 1 := by simpa using step1 1 (by decide) (by decide)
  have f2 : μ 3=3*κ*ν 2 := by simpa using step1 2 (by decide) (by decide)
  have f3 : μ 4=4*κ*ν 3 := by simpa using step1 3 (by decide) (by decide)
  have g1 : (1+2*lam)*ν 2=2*lam*(1-u)*ν 1 := by simpa using step2 1 (by decide) (by decide)
  have g2 : (1+3*lam)*ν 3=3*lam*(1-u)*ν 2 := by simpa using step2 2 (by decide) (by decide)
  have f2' : (1+3*κ)*μ 3=3*κ*(1-η)*μ 2 := by
    have e := nuEq 2
    change ν 2=(1-η)*μ 2-μ 3 at e
    linear_combination f2+3*κ*e
  have f3' : (1+4*κ)*μ 4=4*κ*(1-η)*μ 3 := by
    have e := nuEq 3
    change ν 3=(1-η)*μ 3-μ 4 at e
    linear_combination f3+4*κ*e
  have g1' : (1+2*lam)*μ 3=3*lam*(1-u)*μ 2 := by
    linear_combination (1+2*lam)*f2-3*lam*(1-u)*f1+3*κ*g1
  have g2' : (1+3*lam)*μ 4=4*lam*(1-u)*μ 3 := by
    linear_combination (1+3*lam)*f3-4*lam*(1-u)*f2+4*κ*g2
  exact reflected_collision_scalar κ lam η u (μ 2) (μ 3) (μ 4) f2' f3' g1' g2' hne

omit [CharZero K] in
/-- Reflection of the true bush moments, with the discarded defect
certificate explicit. This gives a reusable bridge to the terminal
scalar determinant without any analytic integration. -/
theorem reflected_unit_primitive_of_defect {A : Fin s→Fin s→K} {b f : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {j k : ℕ} (pay : j+k+1≤p)
    (R : K[X]) (dR : R.natDegree≤j) (hf : f-evalNodes A R∈zeroSpace A j) :
    row (reflWeight A b k) f=(primitive ((1-X)^k*R)).eval 1 := by
  let H : K[X] := (1-X)^k
  have hh : (1-X : K[X]).natDegree≤1 := natDegree_sub_le_of_le
    (show (1:K[X]).natDegree≤1 by simp) (show (X:K[X]).natDegree≤1 by simp)
  have dh : H.natDegree≤k := by
    change ((1-X : K[X])^k).natDegree≤k
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le k hh
  have e (v : Vec K s) : row (reflWeight A b k) v=row b (diag (evalNodes A H) v) := by
    simp only [row_apply,diag_apply,evalNodes_apply,reflWeight,reflNode,H,eval_pow,eval_sub,eval_X,eval_one]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have de := defect_polynomial_pair_zero ho (by omega) hf H dh
  rw [map_sub,map_sub,sub_eq_zero] at de
  rw [e,de]
  have vv : diag (evalNodes A H) (evalNodes A R)=evalNodes A (H*R) := by ext i; simp
  rw [vv]
  exact row_polynomial_eq_unit_primitive ho _ (natDegree_mul_le_of_le dh dR) (by omega)

end RKCert.Paired
