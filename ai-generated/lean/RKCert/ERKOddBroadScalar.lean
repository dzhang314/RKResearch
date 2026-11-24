module
public import RKCert.ERKOddBroadPorts
public import RKCert.DirkQuintic43
public import RKCert.ERKOddFixedRadauTable

@[expose] public section
/-! # Exact unit-weight four-port contradiction over an ordered field
The proof depends only on true native port data, not on the origin (wide
or sparse) of the physical contrast. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Paired.ERKEvenHidden
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b W θ:Vec K 26}{P:K[X]}
noncomputable section

/-- The scalar proof also allows inactive signed weights on physically
nonzero feed rows. The stage chronology is read from the true source θ,
not from which of those rows happens to carry a nonzero scalar mass. -/
structure TrueUnitFourBlockPorts (A:Fin 26→Fin 26→K) (W θ:Vec K 26) (P:K[X]):Prop where
  nonzero:P≠0
  degree:P.natDegree≤5
  sites:(headSites (nodes A) θ).card=4
  support:∀i,W i≠0→θ i≠0
  initial:θ 0=0→P.eval 0=0
  moments:∀R:K[X],R.natDegree≤11→
    (∑i,weightedEval (nodes A) W R i)=(Paired.primitive (R*P)).eval 1
  primitive:∀R:K[X],R.natDegree≤3→∀i,θ i≠0→
    mat A (weightedEval (nodes A) θ R) i=(Paired.primitive (R*P)).eval (nodes A i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem TrueUnitFourPorts.to_block (B:TrueUnitFourPorts A W θ P):TrueUnitFourBlockPorts A W θ P:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  have eq(i:Fin 26):θ i≠0↔W i≠0:=
    ⟨fun h w=>h (B.off i w),fun h=>(B.on i h).2⟩
  have e:headSites (nodes A) θ=headSites (nodes A) W:=by
    change (activeRows θ).image (nodes A)=(activeRows W).image (nodes A)
    congr 1
    ext i
    rw [mem_activeRows,mem_activeRows,eq]
  exact ⟨B.nonzero,B.degree,(congrArg Finset.card e).trans B.sites,fun i h=>(eq i).mpr h,
    fun h=>B.initial (not_ne_iff.mp (fun w=>((eq 0).mpr w) h)),B.moments,
    fun R d i h=>B.primitive R d i ((eq i).mp h)⟩

omit [IsStrictOrderedRing K] in
private theorem unit_zero_filter (B:TrueUnitFourBlockPorts A W θ P)(ha:StrictLower A)
    {i:Fin 26}(wi:θ i≠0) (R:K[X])(deg:R.natDegree≤3)
    (stop:∀k:Fin 26,k < i → θ k≠0 → R.eval (nodes A k)=0):
    (Paired.primitive (R*P)).eval (nodes A i)=0:=by
  rw [←B.primitive R deg i wi]
  have e:mat A (weightedEval (nodes A) θ R) i=mat A 0 i:=by
    apply strictlyCausal_mat ha
    intro k kl
    rw [weightedEval_apply,Pi.zero_apply]
    by_cases wk:θ k=0
    · rw [wk,mul_zero]
    · rw [stop k kl wk,zero_mul]
  rw [e,map_zero,Pi.zero_apply]

set_option maxHeartbeats 2600000 in
theorem TrueUnitFourBlockPorts.impossible (B:TrueUnitFourBlockPorts A W θ P)(ha:StrictLower A):False:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let c:=nodes A
  let D:=activeRows θ
  let S:=headSites c θ
  have sc:S.card=4:=B.sites
  by_cases origin:(0:K)∈S
  · let T:=S.erase 0
    have tc:T.card=3:=by rw [Finset.card_erase_of_mem origin,sc]
    let N:K[X]:=Lagrange.nodal T id
    have nd:N.natDegree=3:=Lagrange.natDegree_nodal.trans tc
    have Nne:N≠0:=Lagrange.nodal_ne_zero
    have N0(a:K)(ha:a∈T):N.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
    let M:=X*(P*N)
    have md:M.natDegree≤9:=by
      have t:=natDegree_mul_le (p:=X) (q:=P*N)
      have r:=natDegree_mul_le (p:=P) (q:=N)
      have l:=B.degree
      rw [natDegree_X] at t
      change M.natDegree≤_ at t;omega
    have M0:M.coeff 0=0:=by simp [M]
    have pay(k:Fin 8):scalarMoment M k.val=0:=by
      let H:K[X]:=X^k.val*(X*N)
      have hd:H.natDegree≤11:=by
        have t:=natDegree_mul_le (p:=X^k.val) (q:=X*N)
        have r:=natDegree_mul_le (p:=X) (q:=N)
        rw [natDegree_X_pow] at t
        rw [natDegree_X] at r
        change H.natDegree≤_ at t
        have e:=k.isLt
        omega
      have h:=B.moments H hd
      have b:(∑i,weightedEval c W H i)=0:=by
        apply Finset.sum_eq_zero
        intro i _
        rw [weightedEval_apply]
        by_cases w:W i=0
        · rw [w,mul_zero]
        · by_cases z:c i=0
          · simp [H,z]
          · have e:c i∈T:=Finset.mem_erase.mpr ⟨z,headSites_mem (c:=c) i (B.support i w)⟩
            simp [H,N0 _ e]
      rw [b,show H*P=X^k.val*M by dsimp only [H,M];ring] at h
      exact h.symm
    obtain ⟨l,z⟩:=meshFull8_decode M md M0 pay
    have ln:l≠0:=by
      intro a;rw [a,zero_smul] at z
      exact mul_ne_zero X_ne_zero (mul_ne_zero B.nonzero Nne) z
    let E:=D.filter (fun i=>c i≠0)
    have e:E.Nonempty:=by
      obtain ⟨a,ta⟩:=Finset.card_pos.mp (by rw [tc];decide:0<T.card)
      obtain ⟨a0,sa⟩:=Finset.mem_erase.mp ta
      obtain ⟨i,iw,ic⟩:=Finset.mem_image.mp sa
      exact ⟨i,Finset.mem_filter.mpr ⟨iw,ic.symm ▸ a0⟩⟩
    let i:=E.min' e
    let u:=c i
    have ui:=Finset.mem_filter.mp (E.min'_mem e)
    have wi:θ i≠0:=(mem_activeRows i).mp ui.1
    have un:u≠0:=ui.2
    have ut:u∈T:=Finset.mem_erase.mpr ⟨un,headSites_mem _ wi⟩
    have q:=unit_zero_filter B ha wi X (by simp) (by
      intro j ji w
      have v:c j=0:=by
        by_contra n
        exact (not_le_of_gt ji) (E.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows j).mpr w,n⟩))
      change X.eval (c j)=0
      rwa [eval_X])
    rw [smul_eq_C_mul] at z
    have root:(odd8:K[X]).eval u=0:=by
      have h:=congrArg (eval u) z
      simp only [M,eval_mul,eval_X,eval_C,N0 u ut,mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left ln
    have hInv:C l⁻¹*C l=(1:K[X]):=by rw [←map_mul,inv_mul_cancel₀ ln,map_one]
    have div:P∣(odd8:K[X]):=by
      refine ⟨C l⁻¹*X*N,?_⟩
      calc
        odd8=C l⁻¹*(C l*odd8):=by rw [←mul_assoc,hInv,one_mul]
        _=C l⁻¹*M:=by rw [z]
        _=P*(C l⁻¹*X*N):=by dsimp only [M];ring
    exact RKCert.RadauEight.FirstMoment.radau8_first_moment div B.degree un root q
  · have nz(i:Fin 26)(h:θ i≠0):c i≠0:=fun z=>origin (z ▸ headSites_mem (c:=c) i h)
    have root:c 0=0:=Finset.sum_eq_zero fun k _=>ha 0 k (Fin.zero_le k)
    have w0:θ 0=0:=by by_contra z;exact nz 0 z root
    have P0:P.coeff 0=0:=by rw [coeff_zero_eq_eval_zero];exact B.initial w0
    obtain ⟨Q,hQ⟩:=X_dvd_iff.mpr P0
    have Qn:Q≠0:=fun z=>B.nonzero (by rw [hQ,z,mul_zero])
    have qd:Q.natDegree≤5:=by
      have p:=B.degree
      rw [hQ,natDegree_mul X_ne_zero Qn,natDegree_X] at p
      omega
    have Ds:D.Nonempty:=by
      obtain ⟨x,h⟩:=Finset.card_pos.mp (by rw [sc];decide:0<S.card)
      obtain ⟨i,iw,ic⟩:=Finset.mem_image.mp h
      exact ⟨i,iw⟩
    let i:=D.min' Ds
    let u:=c i
    have wi:θ i≠0:=(mem_activeRows i).mp (D.min'_mem Ds)
    let E:=D.filter (fun i=>c i≠u)
    have Es:E.Nonempty:=by
      by_contra h
      have only:S⊆{u}:=by
        intro x hx
        obtain ⟨k,kw,rfl⟩:=Finset.mem_image.mp hx
        apply Finset.mem_singleton.mpr
        by_contra z
        exact h ⟨k,Finset.mem_filter.mpr ⟨kw,z⟩⟩
      have l:=Finset.card_le_card only
      rw [sc,Finset.card_singleton] at l
      omega
    let j:=E.min' Es
    have ej:=Finset.mem_filter.mp (E.min'_mem Es)
    have wj:θ j≠0:=(mem_activeRows j).mp ej.1
    apply Qn (RKCert.EndpointPhysical.quintic_four_three Q qd (nz i wi) (nz j wj) ej.2 ?_ ?_)
    · intro k
      have H:=unit_zero_filter B ha wi ((X:K[X])^k.val)
        (by rw [natDegree_X_pow];have e:=k.isLt;omega)
        (fun j jl w=>False.elim ((not_le_of_gt jl) (D.min'_le _ ((mem_activeRows j).mpr w))))
      rwa [hQ,show (X:K[X])^k.val*(X*Q)=X^(k.val+1)*Q by rw [pow_succ,mul_assoc]] at H
    · intro k
      let H:K[X]:=X^k.val*(X-C u)
      have dH:H.natDegree≤3:=by
        have e:=natDegree_mul_le (p:=X^k.val) (q:=X-C u)
        rw [natDegree_X_pow,natDegree_X_sub_C] at e
        change H.natDegree≤_ at e
        have b:=k.isLt
        omega
      have h:=unit_zero_filter B ha wj H dH (by
        intro l lt wl
        have only:c l=u:=by
          by_contra p
          exact (not_le_of_gt lt) (E.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows l).mpr wl,p⟩))
        change H.eval (c l)=0
        simp [H,only])
      rwa [hQ,show H*(X*Q)=X^(k.val+1)*((X-C u)*Q) by dsimp only [H];rw [pow_succ];ring] at h

theorem BroadLinearCover.impossible (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8):False:=by
  obtain ⟨W,θ,P,u⟩:=B.actual_unit_four_ports ha ho S
  exact u.to_block.impossible ha

end
end RKCert.Paired.ReverseHull

