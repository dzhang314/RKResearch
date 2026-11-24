module

public import RKCert.DirkOneEndpointHilbert
public import RKCert.RadauMissingRoot

@[expose] public section

/-! # A two-shift moment argument for the scalar parts of the paid squares

No Jacobi recurrence or choice of nodal coordinates is required.
The fixed degree-seven correction is already invisible to the relevant
weighted moments, so two genuine shift comparisons pay the missing tests.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 700000 in
theorem paid_three_scalar_parts_zero (G : K[X]) (dG : G.natDegree=7)
    (gtest : ∀ Q : K[X],Q.natDegree≤6 → unitIntegral ((1-X)*G*Q)=0)
    (H : Fin 3→K[X]) (dH : ∀ i,(H i).natDegree≤6)
    (htest : ∀ i (Q : K[X]),Q.natDegree≤4 → unitIntegral ((1-X)*H i*Q)=0)
    (step : ∀ i : Fin 2,∃ a : K,X*H i.castSucc-H i.succ=C a*G) :
    ∀ i,H i=0 := by
  have advance (i : Fin 2) (Q : K[X]) (dQ : Q.natDegree≤6)
      (hz : unitIntegral ((1-X)*H i.succ*Q)=0) :
      unitIntegral ((1-X)*H i.castSucc*(X*Q))=0 := by
    obtain ⟨a,he⟩ := step i
    have eq : X*H i.castSucc=H i.succ+C a*G := by linear_combination he
    calc
      _ = unitIntegral ((1-X)*(X*H i.castSucc)*Q) := by congr 1; ring
      _ = unitIntegral ((1-X)*H i.succ*Q+a • ((1-X)*G*Q)) := by
        rw [eq,smul_eq_C_mul]
        congr 1
        ring
      _ = 0 := by rw [map_add,map_smul,hz,gtest Q dQ,smul_zero,zero_add]
  have fifth : unitIntegral ((1-X)*H 0*X^5)=0 := by
    have h : ((X:K[X])^4).natDegree≤4 := by rw [natDegree_X_pow]
    have e := advance 0 (X^4) (h.trans (by decide)) (htest 1 _ h)
    simpa only [pow_succ',Fin.castSucc_zero,Fin.succ_zero_eq_one] using e
  have sixth : unitIntegral ((1-X)*H 0*X^6)=0 := by
    have h : ((X:K[X])^4).natDegree≤4 := by rw [natDegree_X_pow]
    have e := advance 1 (X^4) (h.trans (by decide)) (htest 2 _ h)
    have e₁ : unitIntegral ((1-X)*H 1*X^5)=0 := by
      change unitIntegral ((1-X)*H 1*(X*X^4))=0 at e
      rw [show X*(X:K[X])^4=X^5 by ring] at e
      exact e
    have d5 : ((X:K[X])^5).natDegree≤6 := by rw [natDegree_X_pow]; decide
    have q := advance 0 (X^5) d5 e₁
    simpa only [pow_succ',Fin.castSucc_zero] using q
  have hzero : H 0=0 := by
    apply two_end_weight_primitive_detect (H 0) (k:=0) (d:=6) (dH 0)
    intro i
    change unitIntegral (X^(0+i.val)*((1-X)*H 0))=0
    rw [zero_add,mul_comm]
    by_cases h : i.val≤4
    · exact htest _ _ (by rw [natDegree_X_pow]; exact h)
    · have e : i.val=5 ∨ i.val=6 := by have := i.isLt; omega
      rcases e with e | e
      · rw [e]; exact fifth
      · rw [e]; exact sixth
  have next (i : Fin 2) (z : H i.castSucc=0) : H i.succ=0 := by
    obtain ⟨a,h⟩ := step i
    rw [z,mul_zero,zero_sub] at h
    have az : a=0 := by
      by_contra hn
      have d := congrArg natDegree h
      rw [natDegree_neg,natDegree_C_mul hn,dG] at d
      have b := dH i.succ
      omega
    rw [az,map_zero,zero_mul,neg_eq_zero] at h
    exact h
  have h₁ : H 1=0 := next 0 hzero
  have h₂ : H 2=0 := next 1 h₁
  intro i
  fin_cases i <;> assumption

end
end RKCert.Paired
