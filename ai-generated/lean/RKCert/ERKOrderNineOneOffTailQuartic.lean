module

public import RKCert.OrderedBetaHankel
public import RKCert.ERKLowMomentCollision
public import RKCert.ERKOrderNineFiveSixK8Actual

@[expose] public section

/-! # The quartic one-off endpoint tail, conditionally on its physical identities -/
namespace RKCert.Paired.OneOff
open Polynomial RKCert.OrderedGram

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def fibrePoly (t z : K) : K[X] := (X-C t)*(X-C z)

noncomputable def tailPolynomial (d t z : K) : K[X] := X*((X-C d)*fibrePoly t z)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem fibrePoly_monic (t z : K) : (fibrePoly t z).Monic :=
  (monic_X_sub_C t).mul (monic_X_sub_C z)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem fibrePoly_degree (t z : K) : (fibrePoly t z).natDegree=2 := by
  rw [fibrePoly,natDegree_mul (X_sub_C_ne_zero t) (X_sub_C_ne_zero z),
    natDegree_X_sub_C,natDegree_X_sub_C]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem tailPolynomial_degree (d t z : K) : (tailPolynomial d t z).natDegree=4 := by
  have h := (fibrePoly_monic t z).ne_zero
  have ha := X_sub_C_ne_zero d
  rw [tailPolynomial,natDegree_mul X_ne_zero (mul_ne_zero ha h),natDegree_mul ha h,
    natDegree_X,natDegree_X_sub_C,fibrePoly_degree]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem coprime_of_eval_ne_zero (L : K[X]) (r : K) (n : L.eval r≠0) :
    IsCoprime L (X-C r) := by
  let S := L /ₘ (X-C r)
  have e : C (L.eval r)+(X-C r)*S=L := by
    rw [←modByMonic_X_sub_C_eq_C_eval,modByMonic_add_div]
  have es : L-(X-C r)*S=C (L.eval r) := by
    nth_rw 1 [←e]
    ring
  refine ⟨C ((L.eval r)⁻¹), -C ((L.eval r)⁻¹)*S,?_⟩
  calc
    C ((L.eval r)⁻¹)*L+(-C ((L.eval r)⁻¹)*S)*(X-C r) =
        C ((L.eval r)⁻¹)*(L-(X-C r)*S) := by ring
    _ = C ((L.eval r)⁻¹)*C (L.eval r) := by rw [es]
    _ = 1 := by rw [←C_mul,inv_mul_cancel₀ n,C_1]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem beta_lobattoPencil_pair [CharZero K] (l : K) (Q : K[X]) (dQ : Q.natDegree≤2) :
    betaIntegral (lobattoPencil l*Q)=0 := by
  conv_lhs => rw [quadratic_coeff_expand Q dQ]
  simp only [betaIntegral_apply,lobattoPencil,sub_mul,add_mul,mul_add,X_mul_monomial,
    X_pow_mul_monomial,monomial_mul_monomial,map_add,map_sub,eval_sub,
    primitive_monomial,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

theorem four_root_tail_hankel {l d t z : K} (hzt : z≠t)
    (ht : (lobattoPencil l).eval t=0) (hz : (lobattoPencil l).eval z=0)
    (hd : (lobattoPencil l).eval d≠0) (h1 : (lobattoPencil l).eval 1≠0) :
    let U := (X-C d)*fibrePoly t z
    let m (j : ℕ) := betaIntegral ((1-X)^j*U)
    m 1*m 3-(m 2)^2≠0 := by
  let P := lobattoPencil l
  let Q := fibrePoly t z
  let T : K[X] := (1-X)*(X-C d)
  let U := (X-C d)*Q
  let H := Q*T
  have pm : P.Monic := by
    change P.coeff P.natDegree=1
    rw [show P.natDegree=4 from lobattoPencil_natDegree l]
    simp [P,lobattoPencil]
  have cp := isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hzt.symm))
  obtain ⟨L,eq⟩ := cp.mul_dvd (dvd_iff_isRoot.mpr ht) (dvd_iff_isRoot.mpr hz)
  change P=Q*L at eq
  have qm := fibrePoly_monic t z
  have qd := fibrePoly_degree t z
  have lm := qm.of_mul_monic_left (eq ▸ pm)
  have ld : L.natDegree=2 := by
    have h := natDegree_mul qm.ne_zero lm.ne_zero
    change (Q*L).natDegree=Q.natDegree+L.natDegree at h
    rw [←eq,show P.natDegree=4 from lobattoPencil_natDegree l,qd] at h
    omega
  have ld' : L.eval d≠0 := by
    intro e
    apply hd
    change P.eval d=0
    rw [eq,eval_mul,e,mul_zero]
  have l1 : L.eval 1≠0 := by
    intro e
    apply h1
    change P.eval 1=0
    rw [eq,eval_mul,e,mul_zero]
  have cpT : IsCoprime L T := by
    have e : IsCoprime L (1-X:K[X]) := by
      simpa [neg_sub] using (coprime_of_eval_ne_zero L 1 l1).neg_right
    exact e.mul_right (coprime_of_eval_ne_zero L d ld')
  have tdeg : T.natDegree≤2 := by
    change ((1-X)*(X-C d)).natDegree≤2
    have da : (1-X:K[X]).natDegree≤1 := natDegree_sub_le_of_le
      (show (1:K[X]).natDegree≤1 by simp) (show (X:K[X]).natDegree≤1 by simp)
    exact natDegree_mul_le_of_le da (show (X-C d).natDegree≤1 by rw [natDegree_X_sub_C])
  have ob (S : K[X]) (ds : S.natDegree≤2) : betaIntegral ((Q*L)*S)=0 := by
    rw [←eq]
    exact beta_lobattoPencil_pair l S ds
  have D := beta_quartic_complement_hankel qm lm qd ld tdeg cpT ob
  change betaIntegral H*betaIntegral (X^2*H)-(betaIntegral (X*H))^2≠0 at D
  have q1 : (1-X:K[X])^1*U=H := by dsimp [U,H,T]; ring
  have q2 : (1-X:K[X])^2*U=H-X*H := by dsimp [U,H,T]; ring
  have q3 : (1-X:K[X])^3*U=H-(2:K) • (X*H)+X^2*H := by
    rw [←C_mul']
    norm_num [C_ofNat]
    dsimp [U,H,T]
    ring
  change betaIntegral ((1-X)^1*U)*betaIntegral ((1-X)^3*U)-
    (betaIntegral ((1-X)^2*U))^2≠0
  rw [q1,q2,q3,map_add,map_sub,map_sub,map_smul,smul_eq_mul]
  intro e
  apply D
  linear_combination e

variable {A : Fin 12→Fin 12→K} {b f : Vec K 12}

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem one_off_reflected_beta (ho : HasTreeOrderAtLeast A b 9) {d t z : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (j : ℕ) (budget : j≤3) :
    row (reflWeight A b (j+1)) f =
      betaIntegral ((1-X)^j*((X-C d)*fibrePoly t z)) := by
  have he := reflected_unit_primitive_of_defect ho (j:=4) (k:=j+1)
    (by omega) (tailPolynomial d t z) (tailPolynomial_degree d t z).le hf
  rw [he,betaIntegral_apply]
  congr 2
  rw [tailPolynomial,pow_succ]
  ring

/-- If the two exact physical tail actions and the endpoint pencil have
been obtained, the quartic alternative is already impossible. -/
theorem order9_tail_quartic_impossible (ho : HasTreeOrderAtLeast A b 9)
    {d t z l eta u kap lam tau taus : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (end_clock : nodes A (Fin.last 11)=1)
    (hne : u≠eta) (hzt : z≠t)
    (ht : (lobattoPencil l).eval t=0) (hz : (lobattoPencil l).eval z=0)
    (hd : (lobattoPencil l).eval d≠0) (h1 : (lobattoPencil l).eval 1≠0)
    (fA : mat A f=kap • (diag (nodes A) f-eta • f)+tau • Pi.single (Fin.last 11) 1)
    (vA : let v := diag (nodes A) f-eta • f
      mat A v=lam • (diag (nodes A) v-u • v)+taus • Pi.single (Fin.last 11) 1) :
    False := by
  have fm : f∈treeSpace A 4 := by
    simpa only [sub_add_cancel] using (treeSpace A 4).add_mem (zeroSpace_le_treeSpace A 4 hf)
      (evalNodes_mem_treeSpace A _ (tailPolynomial_degree d t z).le)
  have C := reflected_paid_two_step_collision ho fm end_clock hne fA vA
  rw [one_off_reflected_beta ho hf 1 (by decide),one_off_reflected_beta ho hf 2 (by decide),
    one_off_reflected_beta ho hf 3 (by decide)] at C
  exact (four_root_tail_hankel hzt ht hz hd h1) C

end RKCert.Paired.OneOff
