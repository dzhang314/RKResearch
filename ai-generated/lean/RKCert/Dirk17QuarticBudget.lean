module
public import RKCert.Dirk17ActualGrid
public import RKCert.DirkEightCoreCap
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Polynomial RKCert.Endpoint RKCert.EndpointPhysical RKCert.Paired.Terminal RKCert.RadauEight
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 4000
/-- Two physically located nonzero Jacobi-8 knots exclude both genuinely
complex exceptional ratios, so the non-C(2) branch needs no ordering. -/
theorem fixed_quartic (P:K[X]) (dp:P.natDegree≤4) {u v:K} (hu:u≠0) (hv:v≠0) (different:v≠u)
    (ru:rightWeight8 u=0) (rv:rightWeight8 v=0)
    (first:∀k:Fin 3,(primitive (X^(k.val+1)*P)).eval u=0)
    (next:∀k:Fin 2,(primitive (X^(k.val+1)*((X-C u)*P))).eval v=0):P=0:=by
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
  have hscaled:=normalize (c:=c) (d:=3) hu ⟨one,two 0,two 1⟩
  have vu:v/u*u=v:=by field_simp
  have van:=RKCert.Endpoint.rightWeight8_quartic_gate _ (v/u) u (div_ne_zero hv hu)
    (fun eqn=>different ((div_eq_one_iff_eq hu).mp eqn)) hscaled ru (by rw [vu];exact rv)
  have cc:=(rescale_eq_zero_iff c hu).mp van
  ext j
  by_cases small:j<5
  · simpa [c] using congrFun cc (⟨j,small⟩:Fin 5)
  · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (by omega:P.natDegree<j)]

theorem fixed_quartic_joint (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Unanchored A b):
    zeroSpace A 4≤jointWithOrigin A b 1:=by
  intro v hv
  obtain ⟨Q,dq,fit,off,θ,tr,ac⟩:=h.D.port_contrast ha ho (by decide) (by decide) hv (h.clean _ (zeroSpace_mono A (by decide) hv))
  have van:Q=0:=by
    by_contra nz
    obtain ⟨i,l,bi,ti,bl,tl,un,vn,vu,first,second⟩:=h.D.two_paid_ports ha ho (by decide) (by decide) tr nz ac
    have ri:=unanchored_grid ha ho h i bi ti
    have rl:=unanchored_grid ha ho h l bl tl
    rw [grid_native] at ri rl
    apply nz
    exact fixed_quartic Q dq un vn vu ((mul_eq_zero.mp ri).resolve_left un) ((mul_eq_zero.mp rl).resolve_left vn)
      (fun k=>first k.val (by have:=k.isLt;omega)) (fun k=>second k.val (by have:=k.isLt;omega))
  have hit(i:Fin 23) (ti:tau A b i≠0):v i=0:=by simpa [van] using fit i ti
  apply jointWithOrigin_iff.mpr
  refine ⟨⟨?_,?_⟩,by omega⟩ <;> ext i
  · by_cases t:tau A b i=0
    · exact off i t
    · simp [hit i t]
  · by_cases t:tau A b i=0
    · simp [t]
    · simp [hit i t]

theorem unanchored_clean_five (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17)
    (non:q₂ (mat A) (nodes A) 1≠0) (h:Unanchored A b):(cleanSites A b).card≤5:=by
  classical
  have paid:=signed_cubic_sharp_physical ha ho h.D (j:=7) (by decide) (by decide)
  change 15≤(Finset.univ.filter (fun i=>tau A b i≠0)).card at paid
  have top:=clean_active_plus_joint (A:=A) (b:=b) 1
  have low:=dirk_forward_rank_three_nonzero ha ho (by decide) non
  have fourth:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by decide)
  have sub:=Submodule.finrank_mono (fixed_quartic_joint ha ho h)
  have small:(cleanSites A b).card≤(cleanActive A b).card:=Finset.card_image_le
  have l4 : 3≤finrank K (zeroSpace A 4) := by omega
  have joint : 3≤finrank K (jointWithOrigin A b 1) := l4.trans sub
  omega
end
end RKCert.Paired.Seventeen
