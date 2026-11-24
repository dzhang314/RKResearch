module

public import RKCert.OrderedBetaMoment
public import RKCert.ERKLowEndpointCore

@[expose] public section

/-! # Nondegenerate beta Hankel form without splitting a quartic

A pair of known linear factors can be removed algebraically. Strict
positivity is used only on a polynomial square, not on output weights
or on any roots of the complementary quadratic. -/
namespace RKCert.OrderedGram
open Polynomial RKCert.Paired

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem affine_decomp (P : K[X]) (dP : P.natDegree≤1) :
    P=C (P.coeff 0)+C (P.coeff 1)*X := by
  conv_lhs => rw [quadratic_coeff_expand P (by omega)]
  have z : P.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [z,C_mul_X_eq_monomial]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem beta_affine (P : K[X]) (a b : K) :
    betaIntegral (P*(C a+C b*X))=a*betaIntegral P+b*betaIntegral (X*P) := by
  have e : P*(C a+C b*X)=a • P+b • (X*P) := by
    rw [←C_mul',←C_mul']
    ring
  rw [e,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]

/-- Let the exact beta functional annihilate the paid grades of a
monic quartic Q*L. The quadratic complementary factor L need not split.
A degree-two endpoint factor T coprime to L yields nonzero Hankel
determinant for the two-dimensional residual moment form. -/
theorem beta_quartic_complement_hankel {Q L T : K[X]}
    (qm : Q.Monic) (lm : L.Monic) (qd : Q.natDegree=2) (ld : L.natDegree=2)
    (td : T.natDegree≤2) (cp : IsCoprime L T)
    (orth : ∀ S : K[X], S.natDegree≤2 → betaIntegral ((Q*L)*S)=0) :
    let H := Q*T
    betaIntegral H*betaIntegral (X^2*H)-(betaIntegral (X*H))^2 ≠0 := by
  let P := Q*L
  let H := Q*T
  let m₀ := betaIntegral H
  let m₁ := betaIntegral (X*H)
  let m₂ := betaIntegral (X^2*H)
  change m₀*m₂-m₁^2≠0
  intro det
  obtain ⟨a,b,nz,e₀,e₁⟩ :
      ∃ a b : K, (a≠0 ∨ b≠0) ∧ a*m₀+b*m₁=0 ∧ a*m₁+b*m₂=0 := by
    by_cases mz : m₀=0
    · have z : m₁^2=0 := by simpa only [mz,zero_mul,zero_sub,neg_eq_zero] using det
      have z₁ : m₁=0 := by by_contra h; exact pow_ne_zero 2 h z
      exact ⟨1,0,Or.inl one_ne_zero,by simp [mz],by simp [z₁]⟩
    · exact ⟨-m₁,m₀,Or.inr mz,by ring,by linear_combination det⟩
  let f : K[X] := C a+C b*X
  have fn : f≠0 := by
    intro e
    have ea : a=0 := by simpa [f] using congrArg (fun P : K[X] => P.coeff 0) e
    have eb : b=0 := by simpa [f,C_mul_X_eq_monomial] using congrArg (fun P : K[X] => P.coeff 1) e
    exact nz.elim (fun h=>h ea) (fun h=>h eb)
  have fd : f.natDegree≤1 := by
    change (C a+C b*X).natDegree≤1
    have da : (C a).natDegree≤1 := by simp
    have db : (C b*X).natDegree≤1 :=
      natDegree_mul_le_of_le (show (C b).natDegree≤0 by simp) (show (X:K[X]).natDegree≤1 by simp)
    simpa only [max_self] using natDegree_add_le_of_le da db
  have b₀ : betaIntegral (H*f)=0 := by
    exact (beta_affine H a b).trans e₀
  have b₁ : betaIntegral (X*(H*f))=0 := by
    rw [←mul_assoc]
    rw [show (X*H)*f=(X*H)*(C a+C b*X) from rfl,beta_affine]
    change a*m₁+b*betaIntegral (X*(X*H))=0
    rwa [←mul_assoc,←pow_two]
  have linvan (U : K[X]) (dU : U.natDegree≤1) :
      betaIntegral ((H*f)*U)=0 := by
    rw [affine_decomp U dU,beta_affine,b₀,b₁]
    ring
  let W := (H*f) %ₘ P
  let B := (H*f) /ₘ P
  have pm : P.Monic := qm.mul lm
  have pd : P.natDegree=4 := by rw [natDegree_mul qm.ne_zero lm.ne_zero,qd,ld]
  have pn1 : P≠1 := by intro eq; simp [eq] at pd
  have ln1 : L≠1 := by intro eq; simp [eq] at ld
  have WD : W.natDegree≤3 := by
    have d := natDegree_modByMonic_lt (H*f) pm pn1
    change W.natDegree< P.natDegree at d
    omega
  have BD : B.natDegree≤1 := by
    have e := natDegree_divByMonic (H*f) pm
    have hf : (H*f).natDegree≤5 :=
      natDegree_mul_le_of_le (natDegree_mul_le_of_le qd.le td) fd
    change B.natDegree=(H*f).natDegree-P.natDegree at e
    omega
  have sew : W+P*B=H*f := modByMonic_add_div (H*f) P
  have dvd : Q∣W := by
    change Q∣(H*f) %ₘ P
    rw [modByMonic_eq_sub_mul_div]
    apply dvd_sub
    · exact (dvd_mul_right Q T).trans (dvd_mul_right H f)
    · exact (dvd_mul_right Q L).trans (dvd_mul_right P (H*f /ₘ P))
  obtain ⟨V,eqW⟩ := dvd
  have VD : V.natDegree≤1 := by
    by_cases vn : V=0
    · simp [vn]
    · have e := natDegree_mul qm.ne_zero vn
      rw [←eqW,qd] at e
      omega
  let U := W %ₘ L
  let D := W /ₘ L
  have UD : U.natDegree≤1 := by
    have e := natDegree_modByMonic_lt W lm ln1
    change U.natDegree<L.natDegree at e
    omega
  have DD : D.natDegree≤1 := by
    have e := natDegree_divByMonic W lm
    change D.natDegree=W.natDegree-L.natDegree at e
    omega
  have WU : betaIntegral (W*U)=0 := by
    have e := linvan U UD
    have ph : (H*f)*U=W*U+P*(B*U) := by rw [←sew]; ring
    rw [ph,map_add,orth _ (natDegree_mul_le_of_le BD UD),add_zero] at e
    exact e
  have Wsq : betaIntegral (W^2)=0 := by
    have eq : W^2=W*U+P*(V*D) := by
      calc
        W^2 = W*(U+L*D) := by rw [modByMonic_add_div]; ring
        _ = W*U+P*(V*D) := by rw [eqW]; dsimp [P]; ring
    rw [eq,map_add,WU,orth _ (natDegree_mul_le_of_le VD DD),add_zero]
  have wz : W=0 := by
    by_contra nn
    exact (beta_square_pos W nn).ne' Wsq
  have fdiv : L∣f := by
    apply cp.dvd_of_dvd_mul_left
    apply (mul_dvd_mul_iff_left qm.ne_zero).mp
    have h := (modByMonic_eq_zero_iff_dvd pm).mp wz
    simpa only [P,H,mul_assoc] using h
  have le := natDegree_le_of_dvd fdiv fn
  omega

end RKCert.OrderedGram
