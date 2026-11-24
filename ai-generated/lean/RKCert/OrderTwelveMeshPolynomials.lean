module
public import RKCert.OrderTwelveBand
public import RKCert.OrderTwelveDivisors
@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired Polynomial
variable {K:Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem mesh_factor : (mesh6 : K[X]) = X*RKCert.OrderTwelve.dFivePoly := by
  classical
  rw [mesh6,Polynomial.ofFn_eq_sum_monomial]
  norm_num [mesh6Coeffs, Fin.sum_univ_succ, ← Polynomial.C_mul_X_pow_eq_monomial,
    RKCert.OrderTwelve.dFivePoly]
  simp only [Polynomial.C_ofNat]
  ring

omit [CharZero K] in
theorem ghost7_val (x:K) : (ghost7 : K[X]).eval x=RKCert.OrderTwelve.leakSeven x := by
  classical
  rw [ghost7,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum]
  norm_num [ghost7Coeffs, Fin.sum_univ_succ,RKCert.OrderTwelve.leakSeven]
  ring

noncomputable def ghost8Expr : K[X] := 5*X-75*X^2+350*X^3-700*X^4+630*X^5-210*X^6

omit [CharZero K] in
theorem ghost8_expansion : (ghost8:K[X])=ghost8Expr := by
  classical
  rw [ghost8,Polynomial.ofFn_eq_sum_monomial]
  norm_num [ghost8Coeffs, Fin.sum_univ_succ, ← Polynomial.C_mul_X_pow_eq_monomial,ghost8Expr]
  simp only [Polynomial.C_ofNat]
  ring

omit [CharZero K] in
theorem ghost8_zero : (ghost8:K[X]).eval 0=0 := by
  simp [ghost8_expansion,ghost8Expr]

omit [CharZero K] in
theorem ghost8_one : (ghost8:K[X]).eval 1=0 := by
  norm_num [ghost8_expansion,ghost8Expr]

noncomputable def degreeSevenMesh : K[X] := (X-1)*mesh6

omit [CharZero K] in
theorem mesh7_degree_le : (degreeSevenMesh:K[X]).natDegree≤7 := by
  unfold degreeSevenMesh
  exact natDegree_mul_le.trans (Nat.add_le_add (natDegree_sub_le _ _ |>.trans (by simp)) mesh6_natDegree)

omit [CharZero K] in
theorem mesh7_coeff (n:ℕ) :
    (degreeSevenMesh:K[X]).coeff n = (X*(mesh6:K[X])).coeff n-(mesh6:K[X]).coeff n := by
  simp [degreeSevenMesh,sub_mul]

omit [CharZero K] in
theorem mesh7_coeff7 : (degreeSevenMesh:K[X]).coeff 7=132 := by
  rw [mesh7_coeff,Polynomial.coeff_X_mul]
  have he:=mesh6_coeff (K:=K) (6:Fin 7)
  change (mesh6:K[X]).coeff 6=132 at he
  rw [he,Polynomial.coeff_eq_zero_of_natDegree_lt (by have := mesh6_natDegree (K:=K);omega),sub_zero]

omit [CharZero K] in
theorem mesh7_coeff1 : (degreeSevenMesh:K[X]).coeff 1=1 := by
  rw [mesh7_coeff,Polynomial.coeff_X_mul]
  have a:=mesh6_coeff (K:=K) (0:Fin 7)
  have b:=mesh6_coeff (K:=K) (1:Fin 7)
  change (mesh6:K[X]).coeff 0=0 at a
  change (mesh6:K[X]).coeff 1= -1 at b
  rw [a,b];ring

omit [CharZero K] in
theorem mesh7_coeff2 : (degreeSevenMesh:K[X]).coeff 2= -21 := by
  rw [mesh7_coeff,Polynomial.coeff_X_mul]
  have a:=mesh6_coeff (K:=K) (1:Fin 7)
  have b:=mesh6_coeff (K:=K) (2:Fin 7)
  change (mesh6:K[X]).coeff 1= -1 at a
  change (mesh6:K[X]).coeff 2=20 at b
  rw [a,b];ring

theorem ghost8_coprime :
    IsCoprime (RKCert.OrderTwelve.dFivePoly:K[X]) ghost8 := by
  let U : K[X] := 42000*X^5-105000*X^4+90650*X^3-30975*X^2+3345*X-10
  let V : K[X] := 26400*X^4-52800*X^3+35580*X^2-9180*X+709
  have eq : U*RKCert.OrderTwelve.dFivePoly+V*ghost8=C (10:K) := by
    rw [ghost8_expansion]
    simp only [U,V,RKCert.OrderTwelve.dFivePoly,ghost8Expr,Polynomial.C_ofNat]
    ring
  refine ⟨C ((10:K)⁻¹)*U,C ((10:K)⁻¹)*V,?_⟩
  calc
    _ = C ((10:K)⁻¹)*(U*RKCert.OrderTwelve.dFivePoly+V*ghost8) := by ring
    _ = 1 := by rw [eq,←map_mul,inv_mul_cancel₀ (by norm_num),map_one]

theorem ghost8_coprime_smul {a:K} (ha:a≠0) :
    IsCoprime (RKCert.OrderTwelve.dFivePoly:K[X]) (a • ghost8) := by
  obtain ⟨u,v,eq⟩ := ghost8_coprime (K:=K)
  refine ⟨u,v*C a⁻¹,?_⟩
  rw [Polynomial.smul_eq_C_mul, mul_assoc, ←mul_assoc (C a⁻¹),←map_mul,
    inv_mul_cancel₀ ha,map_one,one_mul,eq]

theorem mesh_ghost8_no_common (x:K) (hf:(mesh6:K[X]).eval x=0)
    (hg:(ghost8:K[X]).eval x=0) : x=0 := by
  by_contra hx
  rw [mesh_factor,eval_mul,eval_X] at hf
  have hh := (mul_eq_zero.mp hf).resolve_left hx
  obtain ⟨u,v,h⟩ := ghost8_coprime (K:=K)
  have ht:=congrArg (Polynomial.eval x) h
  rw [eval_add,eval_mul,eval_mul,hh,hg,mul_zero,mul_zero,zero_add,eval_one] at ht
  exact zero_ne_one ht

-- The two candidate H8 components are compared modulo the already-paid
-- degree-seven mesh, not by any order or sign property of the field.
theorem ghost8_shift_scalar (a b:K)
    (h : X*(a • (ghost8:K[X]))-b • ghost8+(35/22*a) • degreeSevenMesh=0) :
    a=0 ∧ b=0 := by
  have h1 := congrArg (fun P:K[X]=>P.coeff 1) h
  have h2 := congrArg (fun P:K[X]=>P.coeff 2) h
  have j0 := ghost8_coeff (K:=K) (0:Fin 7)
  have j1 := ghost8_coeff (K:=K) (1:Fin 7)
  have j2 := ghost8_coeff (K:=K) (2:Fin 7)
  change (ghost8:K[X]).coeff 0=0 at j0
  change (ghost8:K[X]).coeff 1=5 at j1
  change (ghost8:K[X]).coeff 2= -75 at j2
  simp only [coeff_add,coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,coeff_X_mul,coeff_zero,
    mesh7_coeff1,j0,j1] at h1
  simp only [coeff_add,coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,coeff_X_mul,coeff_zero,
    mesh7_coeff2,j1,j2] at h2
  have hA : a=0 := by linear_combination (-33/10:K)*h1-(11/50:K)*h2
  have hB : b=0 := by linear_combination (-1/5:K)*h1+(7/22:K)*hA
  exact ⟨hA,hB⟩

end RKCert.Paired.OrderTwelve

