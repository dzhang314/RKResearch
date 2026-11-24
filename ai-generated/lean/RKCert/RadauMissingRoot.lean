module

public import RKCert.RadauLeftGram
public import RKCert.Dirk15NonC2ReverseOrbit

@[expose] public section

/-! # Missing true Radau ports force actual profile roots
No algebraic closure is needed for this step. The unnormalized cardinal
numerator is the genuine quotient by a single requested fixed-grid root.
Its integral is nonzero by the full paid Hilbert tests, without positivity. -/
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def unitIntegral : K[X] →ₗ[K] K := (leval 1).comp formalPrimitiveLinear

theorem unitIntegral_apply (P : K[X]) : unitIntegral P=(formalPrimitive P).eval 1 := rfl

def leftRadauGrid : K[X] := X*radauLeft7

def IsLeftRadauPort (x : K) : Prop := x=0 ∨ (radauLeft7 : K[X]).eval x=0

theorem leftRadauGrid_ne : (leftRadauGrid : K[X])≠0 := by
  intro h
  have e := (mul_eq_zero.mp (show X*(radauLeft7:K[X])=0 from h)).resolve_left X_ne_zero
  have H := radauLeft7_reproduces (1:K[X]) (by simp)
  have hz : formalPrimitive (0:K[X])=0 := formalPrimitiveLinear.map_zero
  simp [e,hz] at H

omit [CharZero K] in
theorem IsLeftRadauPort.grid_zero {x : K} (h : IsLeftRadauPort x) :
    (leftRadauGrid : K[X]).eval x=0 := by
  rcases h with e|e <;> simp [leftRadauGrid,e]

omit [CharZero K] in
theorem leftRadauGrid_degree_le : (leftRadauGrid : K[X]).natDegree≤8 := by
  have e := natDegree_mul_le (p:=(X:K[X])) (q:=(radauLeft7:K[X]))
  have h := radauLeft7_degree_le (K:=K)
  rw [natDegree_X] at e
  change (X*(radauLeft7:K[X])).natDegree≤8
  omega

theorem leftRadauGrid_quiet {P : K[X]} (hP : P.natDegree≤6) :
    unitIntegral ((leftRadauGrid : K[X])*P)=0 := by
  have b := natDegree_mul_le (p:=(X:K[X])) (q:=P)
  rw [natDegree_X] at b
  have e := radauLeft7_reproduces (X*P) (by omega)
  have eq : (leftRadauGrid : K[X])*P=(X*P)*radauLeft7 := by unfold leftRadauGrid; ac_rfl
  rw [unitIntegral_apply,eq,e]
  simp

/-- A root is removed by exact divisibility, with no assumption about a
complete set of roots in the coefficient field. -/
theorem radau_cardinal_numerator {a : K} (ha : IsLeftRadauPort a) :
    ∃ H : K[X], H.natDegree≤7 ∧ H≠0 ∧ (leftRadauGrid : K[X])=(X-C a)*H := by
  obtain ⟨H,e⟩ := dvd_iff_isRoot.mpr (show (leftRadauGrid : K[X]).IsRoot a from ha.grid_zero)
  have hH : H≠0 := fun hh => leftRadauGrid_ne (by rw [e,hh,mul_zero])
  have d := leftRadauGrid_degree_le (K:=K)
  rw [e,natDegree_mul (monic_X_sub_C a).ne_zero hH,natDegree_X_sub_C] at d
  exact ⟨H,by omega,hH,e⟩

/-- Exact radial quadrature at one chosen root: no need for the other
roots to be contained in the field, or for their individual weights. -/
theorem radau_cardinal_pair {a : K} {H Q : K[X]}
    (h : (leftRadauGrid : K[X])=(X-C a)*H) (dQ : Q.natDegree≤7) :
    unitIntegral (Q*H)=Q.eval a*unitIntegral H := by
  let R := Q-C (Q.eval a)
  have hR : R.IsRoot a := by simp [IsRoot.def,R]
  obtain ⟨W,e⟩ := dvd_iff_isRoot.mpr hR
  have dW : W.natDegree≤6 := by
    by_cases hW : W=0
    · simp [hW]
    · have hRdeg := natDegree_sub_le Q (C (Q.eval a))
      rw [natDegree_C,max_eq_left (Nat.zero_le _)] at hRdeg
      change R.natDegree≤_ at hRdeg
      rw [e,natDegree_mul (monic_X_sub_C a).ne_zero hW,natDegree_X_sub_C] at hRdeg
      omega
  have poly : Q*H-Q.eval a • H=(leftRadauGrid : K[X])*W := by
    calc
      Q*H-Q.eval a • H = R*H := by
        change Q*H-Q.eval a • H=(Q-C (Q.eval a))*H
        rw [smul_eq_C_mul,sub_mul]
      _ = (leftRadauGrid : K[X])*W := by rw [e,h]; ac_rfl
  have E := congrArg (unitIntegral (K:=K)) poly
  rw [map_sub,map_smul,smul_eq_mul,leftRadauGrid_quiet dW,sub_eq_zero] at E
  exact E

theorem radau_cardinal_integral_ne {a : K} {H : K[X]}
    (h : (leftRadauGrid : K[X])=(X-C a)*H) (dH : H.natDegree≤7) (hH : H≠0) :
    unitIntegral H≠0 := by
  intro e
  apply hH
  apply primitive_shift_detect H dH 1 one_ne_zero (k:=0)
  intro i
  have eq := radau_cardinal_pair (Q:=(X:K[X])^i.val) h
    (by rw [natDegree_X_pow]; have := i.isLt; omega)
  simpa only [e,mul_zero,unitIntegral_apply,zero_add] using eq

variable {s p n : ℕ} {A : Fin s→Fin s→K} {b θ : Vec K s} {P : K[X]}

namespace ReverseTrace
theorem pair_polynomial_radau (h : ReverseTrace A b p n θ P) (ho : HasTreeOrderAtLeast A b p)
    (Q : K[X]) (hp : n+Q.natDegree+1≤p) :
    row θ (weightedEval (mirror A) (1:Vec K s) Q)=unitIntegral (Q*P) := by
  let L := (row θ).comp (weightedEval (mirror A) (1:Vec K s))
  let R := unitIntegral.comp (LinearMap.mulLeft K P)
  have hR : R Q=unitIntegral (Q*P) := by
    change unitIntegral (P*Q)=unitIntegral (Q*P)
    rw [mul_comm]
  rw [←hR]
  change L Q=R Q
  conv_lhs => rw [Q.as_sum_range]
  conv_rhs => rw [Q.as_sum_range]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have d := Finset.mem_range.mp hj
  have e : monomial j (Q.coeff j)=Q.coeff j • (X^j : K[X]) := by
    rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial]
  rw [e,map_smul,map_smul]
  congr 1
  change row θ (weightedEval (mirror A) (1:Vec K s) (X^j))=unitIntegral (P*X^j)
  have e : weightedEval (mirror A) (1:Vec K s) (X^j)=fun i => mirror A i^j := by
    ext i
    simp
  rw [e,unitIntegral_apply,mul_comm]
  exact h.weighted_moment ho j (by omega)

/-- The actual masked contrast cannot carry a nonzero profile on any
unrepresented fixed Radau port. -/
theorem missing_radau_port (h : ReverseTrace A b p n θ P) (ho : HasTreeOrderAtLeast A b p)
    (cap : n+8≤p) (dP : P.natDegree≤7) {a : K} (ha : IsLeftRadauPort a)
    (support : ∀ i, θ i≠0 → IsLeftRadauPort (mirror A i) ∧ mirror A i≠a) :
    P.eval a=0 := by
  obtain ⟨H,dH,hH,hD⟩ := radau_cardinal_numerator ha
  have hProd := radau_cardinal_pair (Q:=P) hD dP
  have hz : row θ (weightedEval (mirror A) (1:Vec K s) H)=0 := by
    rw [row_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : θ i=0
    · simp [hi]
    · obtain ⟨hr,hne⟩ := support i hi
      have e := hr.grid_zero
      rw [hD,eval_mul,eval_sub,eval_X,eval_C] at e
      have hHi := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne)
      simp [hHi]
  rw [h.pair_polynomial_radau ho H (by omega),mul_comm H P,hProd] at hz
  exact (mul_eq_zero.mp hz).resolve_right (radau_cardinal_integral_ne hD dH hH)

end ReverseTrace
end
end RKCert.Paired
