module
public import RKCert.DirkMidpointProducts
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m q r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

omit [CharZero K] in
theorem chain_length_le {a b:ℕ} (le:a≤b) :
    chain (diag (nodes A)) U w a ≤ chain (diag (nodes A)) U w b := by
  obtain ⟨u,k⟩:=(chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) b).mp le_rfl
  exact (chain_le_iff a).mpr ⟨u,fun i hi=>k i (hi.trans_le le)⟩

omit [CharZero K] in
/-- Charge exactly the polynomial degree for multiplying an actual
clock-orbit vector. This remains valid after the midpoint. -/
theorem orbit_mul_polynomial (inv:U.map (diag (nodes A))≤U) {n:ℕ} (pos:0<n)
    {v:Vec K (s+1)} (hv:v∈chain (diag (nodes A)) U w n) (Q:K[X]) :
    weightedEval (nodes A) v Q∈chain (diag (nodes A)) U w (n+Q.natDegree) := by
  have power(i:ℕ):(diag (nodes A)^i) v ∈chain (diag (nodes A)) U w (n+i) := by
    induction i with
    | zero=>simpa using hv
    | succ i ih=>
      rw [show n+(i+1)=(n+i)+1 by omega,←chain_sup_map inv (by omega),pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact (le_sup_right : (chain (diag (nodes A)) U w (n+i)).map (diag (nodes A))≤ _) ⟨_,ih,rfl⟩
  have poly := congrArg (weightedEval (nodes A) v) Q.as_sum_range
  rw [map_sum] at poly
  rw [poly]
  apply Submodule.sum_mem
  intro i hi
  have deg:=Finset.mem_range.mp hi
  have eqn:weightedEval (nodes A) v (monomial i (Q.coeff i))= Q.coeff i • ((diag (nodes A)^i) v) :=by
    ext l
    simp only [weightedEval_apply,eval_monomial,Pi.smul_apply,smul_eq_mul,Clock.pow_diag_apply]
    ring
  rw [eqn]
  exact (chain_length_le (by omega:n+i≤n+Q.natDegree)) ((chain _ _ _ _).smul_mem _ (power i))

/-- On the genuine equality head chart, any scalar polynomial of degree
at most q which is numerically pure *in the head orbit* is divisible by
the full closed Lobatto grid. No splitting or polynomial interpolation
of unknown coordinates is assumed. -/
theorem grid_dvd_of_pure_polynomial (h:MidpointHead A m U w r)
    (fix:m=7 ∨ m=8 ∨ m=9 ∨ m=10) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (low:m+1≤q) (high:q+3≤2*m)
    {H:K[X]} (deg:H.natDegree≤q)
    (pure:evalNodes A H∈chain (diag (nodes A)) U w (r+(q-5))) : (X-1)*lobatto m ∣ H := by
  classical
  have seven:7≤m:=by rcases fix with rfl|rfl|rfl|rfl <;>decide
  let D:K[X]:=(X-1)*lobatto m
  have dd:D.natDegree=m+1:=closed_lobatto_degree (by omega)
  let N:=r+(q-5)
  let O:=chain (diag (nodes A)) U w N
  let V:=H/D
  let R:=H%D
  have remdeg:R.natDegree≤m:=by
    have hh:=Polynomial.natDegree_mod_lt H (show D.natDegree≠0 by omega)
    change R.natDegree<D.natDegree at hh
    omega
  have rep:D*V+R=H:=EuclideanDomain.div_add_mod _ _
  have orig:=closed_grid_paid_on_coordinates fix ha ho he
  rw [h.band m (by omega) le_rfl,chain_sup_map h.invariant (by have:=h.positive;omega)] at orig
  have p0:evalNodes A (D*V)∈O :=by
    by_cases vv:V=0
    · rw [vv,mul_zero,show evalNodes A (0:K[X])=0 from by ext i;simp]
      exact O.zero_mem
    have dn:D≠0:=fun e=>by rw [e,natDegree_zero] at dd;omega
    have dv:D.natDegree+V.natDegree≤q:=by
      rw [←natDegree_mul dn vv,show D*V=H-R from eq_sub_of_add_eq rep]
      exact (natDegree_sub_le _ _).trans (max_le deg (by omega))
    have coin:evalNodes A (D*V)=weightedEval (nodes A) (evalNodes A D) V:=by ext i;simp [mul_comm]
    rw [coin]
    exact (chain_length_le (by dsimp [N];omega:r+(m-5)+1+V.natDegree≤N))
      (orbit_mul_polynomial h.invariant (by omega) orig V)
  have rem:evalNodes A R∈O:=by
    have eqn:evalNodes A R=evalNodes A H-evalNodes A (D*V):=by
      rw [←rep];ext i;simp
    rw [eqn];exact O.sub_mem pure p0
  obtain ⟨u,hu,Q,dQ,eqn⟩:=Clock.exists_head_poly (O.neg_mem rem)
  have pN:0<N:=by dsimp [N];have:=h.positive;omega
  have dn: Q.natDegree<N:=by
    by_cases zz:Q=0
    · simp [zz,pN]
    · exact (natDegree_lt_iff_degree_lt zz).mpr dQ
  have zr:=h.physical_relation_trivial fix ha ho he (q:=q) (by omega) high remdeg dn hu
    (fun i=>by have e:=eqn i;change -R.eval (nodes A i)=_ at e;linear_combination -e)
  exact ⟨V,by rw [←rep,zr.1,add_zero]⟩

end
end RKCert.Paired.Terminal.MidpointHead

