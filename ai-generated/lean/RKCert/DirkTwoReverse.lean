module
public import RKCert.DirkReversePivot
public import RKCert.DirkReflected16
public import RKCert.ERKPhysicalContrasts
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ} {A:Fin (s+1)→Fin (s+1)→K}
variable {b v:Vec K (s+1)}
noncomputable section

/-- The full family of first- and second-vertex primitive moments paid for
by a physical reverse pencil. Both actual rows and both diagonal refunds
are constructed from the original tableau. -/
theorem native_two_reverse (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:2≤j) (hi:j+4≤m) {P:K[X]} (hP:P≠0) {θ:Vec K (s+1)}
    (h:ReverseTrace A b (2*m) j θ P) (active:∀i,θ i≠0 → b i≠0 ∧ tau A b i=0) :
    ∃i l:Fin (s+1), let u:=mirror A i; let v:=mirror A l
      b i≠0 ∧ tau A b i=0 ∧ b l≠0 ∧ tau A b l=0 ∧
      u≠0 ∧ v≠0 ∧ v≠u ∧ A i i=0 ∧ A l l=0 ∧
      (∀ k:ℕ,j+k+2≤m → (formalPrimitive (X^(k+1)*P)).eval u=0) ∧
      (∀ k:ℕ,j+k+3≤m →
        (formalPrimitive (X^(k+2)*P)).eval v=u*(formalPrimitive (X^(k+1)*P)).eval v) := by
  let y:=mirror A
  let w:=diag y θ
  have h1:ReverseTrace A b (2*m) (j+1) w (X*P) := h.clock (by omega)
  have fact₁ (i:Fin (s+1)) (hh:w i≠0): y i≠0 ∧ θ i≠0 := mul_ne_zero_iff.mp hh
  have ac₁ (i:Fin (s+1)) (hh:w i≠0) := active i (fact₁ i hh).2
  obtain ⟨i,wi,bi,τi,di,p1⟩:=physical_reverse_pivot hm ha ho he non (by omega) (by omega) h1
    ac₁ (mul_ne_zero X_ne_zero hP)
  let u:=y i
  let z:=diag y w-u • w
  let Q:=X*(X*P)-u • (X*P)
  have hq:Q=(X-C u)*(X*P) := by simp only [Q,Polynomial.smul_eq_C_mul,sub_mul]
  have h2:ReverseTrace A b (2*m) (j+1+1) z Q := rev_shift h1 u (by omega)
  have fact₂ (l:Fin (s+1)) (hh:z l≠0) : y l≠u ∧ w l≠0 := by
    have hze:z l=(y l-u)*w l := by simp [z,diag_apply,sub_mul]
    rw [hze] at hh
    exact ⟨sub_ne_zero.mp (mul_ne_zero_iff.mp hh).1,(mul_ne_zero_iff.mp hh).2⟩
  obtain ⟨l,zl,bl,τl,dl,p2⟩:=physical_reverse_pivot hm ha ho he non (by omega) (by omega) h2
    (fun l h => ac₁ l (fact₂ l h).2) (by rw [hq]; exact mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero X_ne_zero hP))
  refine ⟨i,l,bi,τi,bl,τl,(fact₁ i wi).1,(fact₁ l (fact₂ l zl).2).1,(fact₂ l zl).1,di,dl,?_,?_⟩
  · intro k hk
    have H:=p1 k (by omega)
    rwa [←mul_assoc,←pow_succ] at H
  · intro k hk
    have H:=p2 k (by omega)
    have e:X^k*Q=X^(k+2)*P-u • (X^(k+1)*P) := by
      dsimp [Q]
      rw [Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul]
      ring
    rw [e,formalPrimitive_eq_treePrimitive,map_sub,map_smul,eval_sub,eval_smul,sub_eq_zero] at H
    simpa only [formalPrimitive_eq_treePrimitive,smul_eq_mul] using H

/-- Genuine weighted scalar contrast for any ordinary defect in the
nonlocal range. Its support is in the paid b-active/τ-zero physical port. -/
theorem port_contrast (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:3≤j) (hi:j+3≤m) (hv:v∈zeroSpace A j) :
    ∃ Q:Polynomial K, Q.natDegree≤j ∧
    (∀i,tau A b i≠0 → v i=Q.eval (mirror A i)) ∧
    (∀i,tau A b i=0 → b i*v i=0) ∧
    ∃θ:Vec K (s+1),ReverseTrace A b (2*m) j θ Q ∧ (∀i,θ i≠0 → b i≠0 ∧ tau A b i=0) := by
  obtain ⟨Q,L,qdeg,_,hq,hl⟩:=defect_ports hm ha ho he non lo hi hv
  have hd:Q.natDegree≤j := by
    by_cases h:Q=0
    · simp [h]
    · have h':Q.natDegree<j+1 := (Polynomial.natDegree_lt_iff_degree_lt h).mpr qdeg
      omega
  refine ⟨Q,hd,hq,fun i hz => by rw [hl i,hz,mul_zero],?_,?_ ,?_⟩
  · exact weightedEval (mirror A) b Q-b*v
  · exact (ReverseTrace.scalar A b hd).sub_pure (weights_mul_zeroSpace ho (by omega) hv)
  · intro i hh
    refine ⟨?_,?_⟩
    · by_contra hz
      simp [weightedEval_apply,hz] at hh
    · by_contra hn
      simp [weightedEval_apply,hq i hn,mul_comm] at hh

end
end RKCert.Paired.Terminal
