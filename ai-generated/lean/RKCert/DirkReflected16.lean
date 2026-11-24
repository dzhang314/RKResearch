module
public import RKCert.DirkFixedEvenBoundary
public import RKCert.NativeInterface
public import RKCert.EndpointPhysical
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The exact common normalization of our forward native degree-eight
cardinal numerator and the published reflected quartic knot polynomial. -/
theorem reflected_lobatto8 (x:K) :
    (lobatto 8).eval x=72*Endpoint.lobatto9 (1-x) := by
  have h:lobatto (K:=K) 8=X*Endpoint.nativeDerivative 8 := by
    rw [lobatto,show (-1:K)^8=1 by norm_num,map_one,one_mul]
    rfl
  rw [h,eval_mul,eval_X,← Endpoint.jacDerivative7_native]
  dsimp [Endpoint.jacDerivative7, Endpoint.lobatto9]
  ring

/-- For the actual 21-row order-16 boundary, a 3+2 primitive quartic at
any two distinct nonzero reflected clocks of clean physical rows is zero.
The fixed clock equations are deduced from order, not assumed. -/
theorem order16_boundary_clean_quartic {A:Fin 21→Fin 21→K} {b:Vec K 21}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 16) :
    ∃t:Fin 21, nodes A t=1 ∧ b t*72=1 ∧
    ∀ i j:Fin 21, i≠t → j≠t →
      (∀f∈zeroSpace A 7, f i=0) → (∀f∈zeroSpace A 7, f j=0) →
      ∀u v:K, u=1-nodes A i → v=1-nodes A j → u≠0 → v≠0 → v≠u →
      ∀ c:Fin 5→K, RKCert.EndpointPhysical.tests c u v 3 → c=0 := by
  obtain ⟨t,ht,_,_,wt,roots⟩ := fixed_even_boundary (s:=20) (m:=8) (Or.inr (Or.inl rfl))
    ha ho (by decide)
  refine ⟨t,ht,by simpa using wt,?_⟩
  intro i j hit hjt hi hj u v hui hvj hu hv hvu c hc
  have z₁:Endpoint.lobatto9 u=0 := by
    rw [hui]
    exact (mul_eq_zero.mp ((reflected_lobatto8 (nodes A i)).symm.trans
      (roots i hit hi))).resolve_left (by norm_num)
  have z₂:Endpoint.lobatto9 v=0 := by
    rw [hvj]
    exact (mul_eq_zero.mp ((reflected_lobatto8 (nodes A j)).symm.trans
      (roots j hjt hj))).resolve_left (by norm_num)
  have rr:v/u≠1 := fun h => hvu ((div_eq_one_iff_eq hu).mp h)
  apply (RKCert.EndpointPhysical.rescale_eq_zero_iff c hu).mp
  apply Endpoint.lobatto9_quartic_gate _ (v/u) u (div_ne_zero hv hu) rr
    (RKCert.EndpointPhysical.normalize hu hc) z₁
  simpa only [div_mul_cancel₀ v hu] using z₂

end RKCert.Paired.Terminal
