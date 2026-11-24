module

public import RKCert.ERKOrderNineOneOffTailQuartic
public import RKCert.ERKOrderNineFiveSixWeights

@[expose] public section

/-! # The cubic one-off endpoint tail -/
namespace RKCert.Paired.OneOff

open Polynomial RKCert.OrderedGram

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The one remaining factor of the cubic supplies a genuine nonzero
mass, directly by orthogonality and beta positivity. -/
theorem cubic_tail_mass {d t z : K} (hzt : z≠t)
    (ht : (lobattoCubic : K[X]).eval t=0) (hz : (lobattoCubic : K[X]).eval z=0)
    (hd : (lobattoCubic : K[X]).eval d≠0) (h1 : (lobattoCubic : K[X]).eval 1≠0) :
    ∃ r mass : K, r≠1 ∧ mass≠0 ∧ ∀ j : ℕ, j≤2 →
      betaIntegral ((1-X)^j*((X-C d)*fibrePoly t z))=(1-r)^j*mass := by
  let Q := fibrePoly t z
  let P : K[X] := lobattoCubic
  have pm : P.Monic := by
    change P.coeff P.natDegree=1
    rw [show P.natDegree=3 from lobattoCubic_degree]
    simp [P,lobattoCubic]
  have cp := isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hzt.symm))
  obtain ⟨L,eq⟩ := cp.mul_dvd (dvd_iff_isRoot.mpr ht) (dvd_iff_isRoot.mpr hz)
  change P=Q*L at eq
  have qm := fibrePoly_monic t z
  have qd := fibrePoly_degree t z
  have lm := qm.of_mul_monic_left (eq ▸ pm)
  have ld : L.natDegree=1 := by
    have h := natDegree_mul qm.ne_zero lm.ne_zero
    change (Q*L).natDegree=Q.natDegree+L.natDegree at h
    rw [←eq,show P.natDegree=3 from lobattoCubic_degree,qd] at h
    omega
  let r := -L.coeff 0
  have le : L=X-C r := by rw [lm.eq_X_add_C ld]; simp [r,sub_eq_add_neg]
  rw [le] at eq
  have rn {x : K} (hx : P.eval x≠0) : x≠r := by
    intro e
    apply hx
    rw [e,eq,eval_mul,eval_sub,eval_X,eval_C,sub_self,mul_zero]
  have orth (U : K[X]) (hd : U.natDegree≤2) : betaIntegral (P*U)=0 := by
    rw [betaIntegral_apply,←mul_assoc]
    exact beta_lobattoCubic_pair U hd
  have prod (S : K[X]) (ds : S.natDegree≤3) :
      betaIntegral (S*Q)=S.eval r*betaIntegral Q := by
    let D := S /ₘ (X-C r)
    have ed : C (S.eval r)+(X-C r)*D=S := by
      rw [←modByMonic_X_sub_C_eq_C_eval,modByMonic_add_div]
    have dd : D.natDegree≤2 := by
      have h := natDegree_divByMonic S (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at h
      change D.natDegree=S.natDegree-1 at h
      omega
    have e : S*Q=(S.eval r) • Q+P*D := by
      rw [←C_mul',eq]
      conv_lhs => rw [←ed]
      ring
    rw [e,map_add,map_smul,smul_eq_mul,orth D dd,add_zero]
  have qn : betaIntegral Q≠0 := by
    intro q0
    have h := beta_square_pos Q qm.ne_zero
    rw [pow_two,prod Q (qd ▸ (by decide : 2≤3)),q0,mul_zero] at h
    exact (lt_irrefl (0:K) h)
  refine ⟨r,(r-d)*betaIntegral Q,(rn h1).symm,
    mul_ne_zero (sub_ne_zero.mpr (rn hd).symm) qn,?_⟩
  intro j hj
  let S : K[X] := (1-X)^j*(X-C d)
  have Yd : (1-X:K[X]).natDegree≤1 :=
    natDegree_sub_le_of_le (show (1:K[X]).natDegree≤1 by simp) (show (X:K[X]).natDegree≤1 by simp)
  have sd : S.natDegree≤3 := by
    have ef := natDegree_mul_le_of_le (natDegree_pow_le_of_le j Yd)
      (show (X-C d).natDegree≤1 by simp)
    change S.natDegree≤j*1+1 at ef
    omega
  have h := prod S sd
  simp only [S,eval_mul,eval_pow,eval_sub,eval_one,eval_X,eval_C] at h
  rw [←mul_assoc]
  calc
    betaIntegral ((1-X)^j*(X-C d)*fibrePoly t z) =
        (1-r)^j*(r-d)*betaIntegral Q := h
    _ = (1-r)^j*((r-d)*betaIntegral Q) := by ring

variable {A : Fin 12 → Fin 12 → K} {b f : Vec K 12}

theorem reflected_first_tail_relation (ho : HasTreeOrderAtLeast A b 9)
    (fm : f∈treeSpace A 4) (end_clock : nodes A (Fin.last 11)=1)
    {eta kap tau : K}
    (fA : mat A f=kap • (diag (nodes A) f-eta • f)+tau • Pi.single (Fin.last 11) 1)
    (j : ℕ) (j0 : j≠0) (j3 : j≤3) :
    (1+((j+1:ℕ):K)*kap)*row (reflWeight A b (j+1)) f =
      ((j+1:ℕ):K)*kap*(1-eta)*row (reflWeight A b j) f := by
  have e := mem_annih.mp (ReverseHull.reflected_annih ho (j:=4) j3 (by omega)) f fm
  rw [reflected_apply,fA,map_add,map_smul,map_smul,reflect_end_single end_clock _ j0,
    smul_zero,add_zero,smul_eq_mul,reflected_weight_clock_shift] at e
  linear_combination -e

/-- The cubic terminal alternative is impossible as soon as the first
physical tail identity has been obtained. The second action is unneeded. -/
theorem order9_tail_cubic_impossible (ho : HasTreeOrderAtLeast A b 9)
    {d t z eta kap tau : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (end_clock : nodes A (Fin.last 11)=1) (hzt : z≠t)
    (ht : (lobattoCubic : K[X]).eval t=0) (hz : (lobattoCubic : K[X]).eval z=0)
    (hd : (lobattoCubic : K[X]).eval d≠0) (h1 : (lobattoCubic : K[X]).eval 1≠0)
    (fA : mat A f=kap • (diag (nodes A) f-eta • f)+tau • Pi.single (Fin.last 11) 1) :
    False := by
  have fm : f∈treeSpace A 4 := by
    simpa only [sub_add_cancel] using (treeSpace A 4).add_mem (zeroSpace_le_treeSpace A 4 hf)
      (evalNodes_mem_treeSpace A _ (tailPolynomial_degree d t z).le)
  obtain ⟨r,m,rn,mn,mass⟩ := cubic_tail_mass hzt ht hz hd h1
  have moments (j : ℕ) (h : j≤2) :
      row (reflWeight A b (j+1)) f=(1-r)^j*m :=
    (one_off_reflected_beta ho hf j (by omega)).trans (mass j h)
  have e1 := reflected_first_tail_relation ho fm end_clock fA 1 (by decide) (by decide)
  have e2 := reflected_first_tail_relation ho fm end_clock fA 2 (by decide) (by decide)
  rw [moments 0 (by decide),moments 1 (by decide)] at e1
  rw [moments 1 (by decide),moments 2 (by decide)] at e2
  norm_num at e1 e2
  have s1 : (1+2*kap)*(1-r)=2*kap*(1-eta) := by
    apply mul_right_cancel₀ mn
    linear_combination e1
  have s2 : (1+3*kap)*(1-r)=3*kap*(1-eta) := by
    apply mul_right_cancel₀ (mul_ne_zero (sub_ne_zero.mpr rn.symm) mn)
    linear_combination e2
  exact rn (by linear_combination -3*s1+2*s2)

end RKCert.Paired.OneOff
