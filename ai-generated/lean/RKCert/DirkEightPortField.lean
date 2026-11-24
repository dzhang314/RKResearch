module
public import RKCert.DirkPaidPorts
public import RKCert.DirkRefundedTwoPivots
@[expose] public section
namespace RKCert.EndpointPhysical
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K]

/-- Exact field requirement for a free, unweighted quartic with two
noncoincident, nonzero physical 3+2 ports. -/
def NoExceptionalRatio (K:Type*) [Field K]:Prop:=∀ t:K, 15*t^2-24*t+10≠0

theorem noExceptionalRatio_iff :NoExceptionalRatio K ↔ ¬∃x:K,x^2= -6:=by
  constructor
  · rintro h ⟨x,sq⟩
    apply h ((x+12)/15)
    linear_combination sq/15
  · intro no t ht
    apply no
    exact ⟨15*t-12,by linear_combination 15*ht⟩

theorem noExceptionalRatio_ordered {R:Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]:
    NoExceptionalRatio R:=by
  rw [noExceptionalRatio_iff]
  rintro ⟨x,h⟩; nlinarith [sq_nonneg x]

/-- On arbitrary characteristic-zero fields the polynomial itself vanishes,
or the *actual* ratio of the two physical chronological pivots is exceptional. -/
theorem quartic_physical_alternative (P:K[X]) (dp:P.natDegree≤4) {u v:K} (hu:u≠0) (hv:v≠0) (different:v≠u)
    (first:∀k:Fin 3,(Paired.primitive (X^(k.val+1)*P)).eval u=0)
    (next:∀k:Fin 2,(Paired.primitive (X^(k.val+1)*((X-C u)*P))).eval v=0):
    P=0 ∨ 15*(v/u)^2-24*(v/u)+10=0:=by
  let c:Fin 5→K:=fun i=>P.coeff i.val
  have eqn (t:K) (k:ℕ):(Paired.primitive (X^k*P)).eval t=moment c t k:=by
    rw [←formalPrimitive_eq_treePrimitive,Paired.primitive_eval_power_mul P t k dp]
    apply Finset.sum_congr rfl;intro i _;simp only [c,Nat.add_comm k i.val]
  have one(k:Fin 3):moment c u (k.val+1)=0:=(eqn u _).symm.trans (first k)
  have two(k:Fin 2):moment c v (k.val+2)-u*moment c v (k.val+1)=0:=by
    have h:=next k
    have e:X^(k.val+1)*((X-C u)*P)=X^(k.val+2)*P-u • (X^(k.val+1)*P):=by
      rw [show k.val+2=(k.val+1)+1 by omega,pow_succ,Polynomial.smul_eq_C_mul];ring
    rw [e,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,eqn,eqn] at h;exact h
  rcases quartic_three_two _ (v/u) (div_ne_zero hv hu) (fun eqn=>different ((div_eq_one_iff_eq hu).mp eqn))
    (normalize (c:=c) (d:=3) hu ⟨one,two 0,two 1⟩) with van|bad
  · left
    have cc:=(rescale_eq_zero_iff c hu).mp van
    ext j
    by_cases small:j<5
    · simpa [c] using congrFun cc (⟨j,small⟩:Fin 5)
    · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (by omega:P.natDegree<j)]
  · exact Or.inr bad
end RKCert.EndpointPhysical

namespace RKCert.Paired.Terminal.PaidReverseBand
open Module Polynomial RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {s p H:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b v:Vec K (s+1)}
/-- Over fields without sqrt(-6), including every ordered field, the
full genuine quartic is invisible at a horizon one grade earlier. -/
theorem quartic_jointly_hidden_eight (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (field:NoExceptionalRatio K) (eight:8≤H) (hv:v∈zeroSpace A 4) (vt:v (Fin.last s)=0):
    b*v=0 ∧ tau A b*v=0:=by
  obtain ⟨Q,dq,fit,off,θ,tr,ac⟩:=D.port_contrast ha ho (by decide) (by omega) hv vt
  have zero:Q=0:=by
    by_contra nz
    obtain ⟨i,l,_,_,_,_,un,vn,vu,first,second⟩:=D.two_paid_ports ha ho (by decide) (by omega) tr nz ac
    exact field _ ((quartic_physical_alternative Q dq un vn vu
      (fun k=>first k.val (by have:=k.isLt;omega)) (fun k=>second k.val (by have:=k.isLt;omega))).resolve_left nz)
  have on(i:Fin (s+1)) (hh:tau A b i≠0):v i=0:=by simpa [zero] using fit i hh
  constructor <;> ext i
  · by_cases hh:tau A b i=0
    · exact off i hh
    · simp [on i hh]
  · by_cases hh:tau A b i=0
    · simp [hh]
    · simp [on i hh]
end RKCert.Paired.Terminal.PaidReverseBand
