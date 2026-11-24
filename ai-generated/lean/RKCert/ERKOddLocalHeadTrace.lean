module
public import RKCert.ERKOddLocalRank
public import RKCert.ERKOddMaskBlocks
public import RKCert.ERKOddBroadScalar

@[expose] public section
/-! # The common localized actual forward-head contrast
Clear only the genuine forward mask algebra, which is an actual array
subspace. The early adjoint base correction is retained in every moment. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

theorem LocalLinearBand.multiplies_hidden (_B:LocalLinearBand A b r U τ)
    {f:Vec K 26}(closed:∀v∈U,f*v∈U):
    ∀z∈reverseHidden b τ U,f*z∈reverseHidden b τ U:=by
  intro z hz
  obtain ⟨a,bz,cu⟩:=mem_reverseHidden.mp hz
  apply mem_reverseHidden.mpr
  refine ⟨?_,?_,?_⟩
  · rw [show τ*(f*z)=f*(τ*z) by ring,a,mul_zero]
  · rw [show b*(f*z)=f*(b*z) by ring]
    exact closed _ bz
  · intro v hv
    rw [mul_assoc]
    exact closed _ (cu _ hv)

structure LocalHeadContrast (A:Fin 26→Fin 26→K)(b τ h W:Vec K 26)
    (U:Submodule K (Vec K 26))(Q:K[X]):Prop where
  degree:Q.natDegree≤5
  nonzero:Q≠0
  preserved:∀v∈U,h*v∈U
  headValue:∀i,τ i≠0→h i=Q.eval (mirror A i) ∧ ¬Clock.Live (reverseHidden b τ U) i
  contrastValue:∀i,W i≠0→h i=0 ∧ Q.eval (mirror A i)≠0 ∧ ¬Clock.Live (reverseHidden b τ U) i
  moments:∀R:K[X],R.natDegree≤11→(∑i,weightedEval (mirror A) W R i)=(Paired.primitive (R*Q)).eval 1

theorem LocalLinearBand.native_head_contrast_per_stage (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){h:Vec K 26}
    (hh:h∈zeroSpace A 5)(out:h∉reverseHidden b τ U):
    ∃W:Vec K 26,∃Q:K[X],LocalHeadContrast A b τ h W U Q ∧
      (∀i,W i=if (¬Clock.Live (reverseHidden b τ U) i) ∧ h i=0
        then Q.eval (mirror A i)*b i else 0):=by
  classical
  let y:=mirror A
  let G:=reverseHidden b τ U
  have r0:1≤r∧r≤2:=by rcases B.short with z|z <;> omega
  obtain ⟨Q,qD,fit⟩:=B.head_trace ho hh (by omega)
  have qn:Q≠0:=by
    intro h0
    have z:τ*h=0:=by rw [←fit,h0,map_zero]
    exact out (B.hidden_of_zero_profile ho (by omega) hh z)
  obtain ⟨u,hu,P,pD,rep⟩:=B.weight_trace ho hh (by decide)
  have dP:P.natDegree+r≤4:=by
    rcases pD with z|p
    · rw [z,natDegree_zero];omega
    · omega
  have pres:∀v∈U,h*v∈U:=fun v hv=>B.mul_base ho (by omega) hh hv
  obtain ⟨u',u'U,eQ⟩:=B.local_contrast_clean Q P hu pres fit rep
  obtain ⟨e,eG,e_at⟩:=core_indicator (reverse_hidden_mul (τ:=τ) (b:=b) (U:=U))
  let W0:=localContrast A b h Q
  let W:=W0-e*W0
  have eB:b*e∈U:=(mem_reverseHidden.mp eG).2.1
  have invh:U.map (diag h)≤U:=by rintro _ ⟨v,hv,rfl⟩;exact pres v hv
  have remove:e*W0∈U:=by
    let φ(a t:K):K:=if t=0 then Q.eval a else 0
    have eq:e*W0=(fun i=>φ (y i) (h i)*(b*e) i):=by
      ext i
      simp only [Pi.mul_apply,W0,localContrast_apply,φ,y]
      split <;> ring
    rw [eq]
    exact joint_selector_mem B.clock invh eB φ
  have repW:W=weightedEval y b Q-weightedEval y τ P-(u'+e*W0):=by
    calc
      W=W0-e*W0:=rfl
      _=(weightedEval y b Q-weightedEval y τ P-u')-e*W0:=by rw [show W0=localContrast A b h Q from rfl,eQ]
      _=_:=by abel
  refine ⟨W,Q,⟨⟨qD,qn,pres,?_,?_,?_⟩,?_⟩⟩
  · intro i ti
    have q:=congrFun fit i
    simp only [weightedEval_apply,Pi.mul_apply] at q
    rw [mul_comm (Q.eval _) (τ i)] at q
    refine ⟨(mul_left_cancel₀ ti q).symm,?_⟩
    rintro ⟨g,hg,gi⟩
    have e:=congrFun (mem_reverseHidden.mp hg).1 i
    exact mul_ne_zero ti gi e
  · intro i nz
    have off:¬Clock.Live G i:=by
      intro live
      have ep:e i=1:=by
        have z:=e_at i
        change e i=(if Clock.Live G i then 1 else 0) at z
        rwa [ite_eq_left live] at z
      apply nz
      simp [W,ep]
    have ep:e i=0:=by
      have z:=e_at i
      change e i=(if Clock.Live G i then 1 else 0) at z
      rwa [ite_eq_right off] at z
    have Wn:W0 i≠0:=by simpa [W,ep] using nz
    have z:h i=0:=by by_contra x;apply Wn;change localContrast A b h Q i=0;rw [localContrast_apply,ite_eq_right x]
    have q:Q.eval (y i)≠0:=by
      change localContrast A b h Q i≠0 at Wn
      rw [localContrast_apply,ite_eq_left z] at Wn
      exact (mul_ne_zero_iff.mp Wn).1
    exact ⟨z,q,off⟩
  · intro R rd
    exact B.local_contrast_moments ho Q P R (U.add_mem u'U remove) repW (by omega) (by omega) (by omega)
  · intro i
    have e':e i=(if Clock.Live G i then 1 else 0):=e_at i
    change W0 i-e i*W0 i=(if (¬Clock.Live G i)∧h i=0 then Q.eval (y i)*b i else 0)
    rw [e']
    by_cases g:Clock.Live G i
    · simp [g]
    rw [ite_eq_right g,zero_mul,sub_zero,show W0 i=localContrast A b h Q i from rfl,localContrast_apply]
    simp [g,y]

theorem LocalLinearBand.native_head_contrast (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){h:Vec K 26}
    (hh:h∈zeroSpace A 5)(out:h∉reverseHidden b τ U):
    ∃W:Vec K 26,∃Q:K[X],LocalHeadContrast A b τ h W U Q:=by
  obtain ⟨W,Q,T,_⟩:=B.native_head_contrast_per_stage ho hh out
  exact ⟨W,Q,T⟩

theorem four_sites_of_unit_contrast (Y W:Vec K 26)(Q:K[X])(dq:Q.natDegree≤5)(qn:Q≠0)
    (mom:∀R:K[X],R.natDegree≤11→(∑i,weightedEval Y W R i)=(Paired.primitive (R*Q)).eval 1):
    4≤(headSites Y W).card:=by
  classical
  let F:=headSites Y W
  by_contra! few
  change F.card<4 at few
  let N:K[X]:=Lagrange.nodal F id
  have nd:N.natDegree=F.card:=Lagrange.natDegree_nodal
  let R:=N^2*Q
  have rd:R.natDegree≤11:=by
    have z:=natDegree_mul_le (p:=N^2) (q:=Q)
    rw [natDegree_pow,nd] at z
    change R.natDegree≤_ at z;omega
  have zero:(∑i,weightedEval Y W R i)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    rw [weightedEval_apply]
    by_cases wi:W i=0
    · rw [wi,mul_zero]
    · have e:N.eval (Y i)=0:=Lagrange.eval_nodal_at_node (v:=id) (headSites_mem _ wi)
      simp [R,e]
  have eq:=mom R rd
  rw [zero,show R*Q=(N*Q)^2 by dsimp only [R];ring] at eq
  have pos:=RKCert.OrderedGram.pow_square_pos 0 (N*Q) (mul_ne_zero Lagrange.nodal_ne_zero qn)
  rw [pow_zero,one_mul] at pos
  exact pos.ne' eq.symm
end
end RKCert.Paired.ReverseHull

