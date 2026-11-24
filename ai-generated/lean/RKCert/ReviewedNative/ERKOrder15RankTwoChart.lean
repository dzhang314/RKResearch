module

public import RKCert.ReviewedNative.ERKOrder15LargeKnots
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts

@[expose] public section

/-! # A large order-fifteen head violates the two actual primitive windows -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s a r : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

/-- The simultaneous physical factor and the two paid knots on its
complement, before invoking the reviewed scalar cubic elimination. -/
theorem Order15PaidStaircase.large_head_complementary_knots (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15) (large : 3≤r) :
    ∃ (v : Fin (s+1)→K) (P Q : K[X]) (i t : Fin (s+1)),
      Order15PaidStaircase A b a G r U v ∧ P≠0 ∧ P.natDegree≤3 ∧ G=P*Q ∧
      Q.natDegree=r+2 ∧ P.natDegree+r+1=a ∧ PhysicalHeadKnots A U v G P i t ∧
      Q.eval (nodes A i)=0 ∧ Q.eval (nodes A t)=0 := by
  obtain ⟨v,P,Q,T,dis,pn,pd,eq,qd,ad,repr⟩ := S.large_head_factor ha ho large
  obtain ⟨i,t,B⟩ := physical_head_knots_three_two (T.large_head_knot ha ho large dis repr pn pd)
  exact ⟨v,P,Q,i,t,T,pn,pd,eq,qd,ad,B,B.complementary_roots eq⟩

/-- Every native characteristic-zero order-fifteen paid staircase has
head length exactly two. No ordered-field positivity was needed. -/
theorem Order15PaidStaircase.head_eq_two (S : Order15PaidStaircase A b a G r U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15) : r=2 := by
  have lower := S.headLength
  by_contra h
  obtain ⟨_,P,_,i,t,_,pn,pd,_,_,_,B,_⟩ := S.large_head_complementary_knots ha ho (by omega)
  exact pn (RKCert.EndpointPhysical.cubic_eq_zero_of_primitives pd B.firstNonzero B.secondNonzero B.different
    ⟨B.firstTest,B.secondTest⟩)

/-- The width-22 native chart is already restricted to r=2. This
is not yet a contradiction or a claim about the final stage bound. -/
theorem order15_rank_two_staircase (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15)
    (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]) (U : Submodule K (Fin (s+1)→K)) (w : Fin (s+1)→K),
      Order15PaidStaircase A b a G 2 U w := by
  obtain ⟨a,G,r,U,w,S⟩ := order15_physical_staircase ha ho cap
  exact ⟨a,G,U,w,S.head_eq_two ha ho ▸ S⟩

end RKResearch.Certified.Graded
