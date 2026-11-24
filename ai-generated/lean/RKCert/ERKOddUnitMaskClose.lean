module
public import RKCert.ERKOddLocalHeadTrace

@[expose] public section
/-! # Four clean physical clocks turn a normalized head into actual primitive ports -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h W:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

set_option maxHeartbeats 4000000 in
theorem LocalLinearBand.no_four_clean_contrast (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (hh:h∈zeroSpace A 5)(T:LocalHeadContrast A b τ h W U Q)
    (w4:(headSites (mirror A) W).card=4)
    (cover:∀i:Fin 26,¬Clock.Live (reverseHidden b τ U) i→h i≠Q.eval (mirror A i)→
      mirror A i∈headSites (mirror A) W∧∀v∈zeroSpace A 9,v i=0):False:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let G:=reverseHidden b τ U
  let c:=nodes A
  let y:=mirror A
  have Gi:G.map (diag c)≤G:=B.hidden_invariant
  have Gf:G≤zeroSpace A 8:=B.hidden_pure ho
  let P:=reflectPolynomial Q
  have pd:P.natDegree≤5:=(reflectPolynomial_degree Q).trans T.degree
  have pn:P≠0:=by
    intro z
    have h:=reflect_involution_polynomial Q
    change reflectPolynomial P=Q at h
    rw [z,reflectPolynomial,zero_comp] at h
    exact T.nonzero h.symm
  have pe(i:Fin 26):P.eval (c i)=Q.eval (y i):=eval_reflect_nodes Q i
  obtain ⟨e,eG,e_at⟩:=core_indicator (reverse_hidden_mul (b:=b) (τ:=τ) (U:=U))
  have ind(i:Fin 26):e i=(if Clock.Live G i then 1 else 0):=e_at i
  let k:=weightedEval c e P-h*e
  have kG:k∈G:=by
    apply G.sub_mem _ (B.multiplies_hidden T.preserved e eG)
    have eq:weightedEval c e P=(fun i=>P.eval (c i)*e i):=by ext i;exact weightedEval_apply _ _ _ _
    rw [eq]
    exact Clock.poly_preserves Gi P e eG
  let θ:=evalNodes A P-h-k
  have θval(i:Fin 26):θ i=(1-e i)*(Q.eval (y i)-h i):=by
    simp only [θ,k,Pi.sub_apply,Pi.mul_apply,evalNodes_apply,weightedEval_apply,show nodes A i=c i from rfl,pe]
    ring
  have on(i:Fin 26)(wi:W i≠0):θ i≠0:=by
    obtain ⟨h0,n,g⟩:=T.contrastValue i wi
    rw [θval,ind,ite_eq_right g,sub_zero,one_mul,h0,sub_zero]
    exact n
  have shape(i:Fin 26)(ti:θ i≠0):
      y i∈headSites y W∧∀v∈zeroSpace A 9,v i=0:=by
    have d:¬Clock.Live G i:=fun g=>ti (by rw [θval,ind,ite_eq_left g,sub_self,zero_mul])
    have q:h i≠Q.eval (y i):=fun p=>ti (by rw [θval,p,sub_self,mul_zero])
    exact cover i d q
  have sitesY:headSites y θ=headSites y W:=by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
      exact (shape i (Finset.mem_filter.mp hi).2).1
    · intro a ha
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
      exact headSites_mem i (on i (Finset.mem_filter.mp hi).2)
  have sites:(headSites c θ).card=4:=by
    have e:headSites c θ=(headSites y θ).image (fun x=>1-x):=by
      change (activeRows θ).image c=((activeRows θ).image y).image (fun x=>1-x)
      rw [Finset.image_image]
      congr 1;funext i;change nodes A i=1-(1-nodes A i);ring
    rw [e,Finset.card_image_of_injective _ (by intro a b e;linear_combination -e),sitesY,w4]
  have origin(t0:θ 0=0):P.eval 0=0:=by
    have c0:c 0=0:=Finset.sum_eq_zero fun l _=>ha 0 l (Fin.zero_le l)
    have h0:=origin_zeroSpace A ha 5 hh
    have k0:=origin_zeroSpace A ha 8 (Gf kG)
    change h 0=0 at h0
    change k 0=0 at k0
    change P.eval (c 0)-h 0-k 0=0 at t0
    rwa [c0,h0,k0,sub_zero,sub_zero] at t0
  have moments(R:K[X])(p:R.natDegree≤11):
      (∑i,weightedEval c W R i)=(Paired.primitive (R*P)).eval 1:=by
    let E:=reflectPolynomial R
    have d:E.natDegree≤11:=(reflectPolynomial_degree R).trans p
    have h:=T.moments E d
    have eq:(∑i,weightedEval c W R i)=∑i,weightedEval y W E i:=by
      apply Finset.sum_congr rfl;intro i _;simp [c,y,E,eval_mirror_twice]
    have eq':(E*Q).comp (1-X)=R*P:=by
      rw [mul_comp,show E.comp (1-X)=R from reflect_involution_polynomial R]
      rfl
    rw [eq,h,←eq']
    exact (RKCert.OrderedGram.moment_reflect _).symm
  have clean(i:Fin 26)(ti:θ i≠0)(f:Vec K 26)(fm:f∈zeroSpace A 9):f i=0:=
    (shape i ti).2 f fm
  have ports:TrueUnitFourBlockPorts A W θ P:=by
    refine ⟨pn,pd,sites,on,origin,moments,?_⟩
    intro R dR i ti
    have deg:(R*P).natDegree≤8:=natDegree_mul_le.trans (by omega)
    have pf:=clean i ti _ (primitive_defect A (R*P) deg)
    have fn:weightedEval c h R∈zeroSpace A 8:=by
      have eq:weightedEval c h R=h*evalNodes A R:=by
        ext l;simp only [weightedEval_apply,Pi.mul_apply,evalNodes_apply,c];exact mul_comm _ _
      rw [eq]
      exact zeroSpace_mul_treeSpace ho (m:=5) (n:=3) (by decide) hh (evalNodes_mem_treeSpace _ _ dR)
    have kf:weightedEval c k R∈zeroSpace A 8:=by
      have eq:weightedEval c k R=(fun i=>R.eval (c i)*k i):=by ext i;exact weightedEval_apply _ _ _ _
      rw [eq]
      exact Gf (Clock.poly_preserves Gi R k kG)
    have h1:=clean i ti _ (mat_zeroSpace_charZero A 8 fn)
    have h2:=clean i ti _ (mat_zeroSpace_charZero A 8 kf)
    have e:weightedEval c θ R=evalNodes A (R*P)-weightedEval c h R-weightedEval c k R:=by
      ext l;simp only [θ,weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,c];ring
    rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,h1,h2,sub_zero,sub_zero]
    exact sub_eq_zero.mp pf
  exact ports.impossible ha
end
end RKCert.Paired.ReverseHull

