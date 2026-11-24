module
public import RKCert.ERKOddFourPort
public import RKCert.LobattoFactors

@[expose] public section
/-! # The four physical ports force a single paid free Jacobi pencil
The zero-clock and free-knot tests concern original ordinary RK stages; the
scalar arithmetic is left as a separate independently replayable gate. -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint
open RKCert.Paired.Terminal RKCert.Paired.ERKEvenHidden Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K} {b W θ:Vec K 26} {P:K[X]}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem TrueFourPort.zero_filter (B:TrueFourPort A b W θ P)
    (ha:StrictLower A) {i:Fin 26} (wi:W i≠0) (R:K[X]) (deg:R.natDegree≤2)
    (off:∀k:Fin 26,k < i → W k≠0 → R.eval (nodes A k)=0) :
    (Paired.primitive (R*P)).eval (nodes A i)=0:=by
  rw [←B.primitive R deg i wi]
  have e:mat A (weightedEval (nodes A) θ R) i=mat A 0 i:=by
    apply strictlyCausal_mat ha
    intro k kl
    rw [weightedEval_apply,Pi.zero_apply]
    by_cases wk:W k=0
    · rw [B.off k wk (fun e=>not_lt_of_ge (Fin.le_last i) (e ▸ kl)),mul_zero]
    · rw [off k kl wk,zero_mul]
  rw [e,map_zero,Pi.zero_apply]

theorem TrueFourPort.no_origin_clock (B:TrueFourPort A b W θ P)
    (ha:StrictLower A)(no:(0:K)∉headSites (nodes A) W):False:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let c:=nodes A
  let D:=activeRows W
  have Dne:D.Nonempty:=Finset.card_pos.mp (by rw [show D.card=4 from B.rows];decide)
  let i:=D.min' Dne
  let u:=c i
  have wi:W i≠0:=(mem_activeRows i).mp (D.min'_mem Dne)
  have origin:c 0=0:=Finset.sum_eq_zero (fun k _=>ha 0 k (Fin.zero_le k))
  have w0:W 0=0:=by
    by_contra w
    exact no (origin ▸ headSites_mem (c:=c) 0 w)
  have nz (k:Fin 26)(wk:W k≠0):c k≠0:=fun e=>no (e ▸ headSites_mem (c:=c) k wk)
  have zeroP:P.coeff 0=0:=by rw [coeff_zero_eq_eval_zero];exact B.initial w0
  obtain ⟨Q,hQ⟩:=X_dvd_iff.mpr zeroP
  have Qn:Q≠0:=fun z=>B.nonzero (by rw [hQ,z,mul_zero])
  have deg:Q.natDegree≤4:=by
    have E:=B.degree
    rw [hQ,natDegree_mul X_ne_zero Qn,natDegree_X] at E
    omega
  let E:=D.filter (fun k=>c k≠u)
  have En:E.Nonempty:=by
    by_contra hh
    have p:(headSites c W)⊆{u}:=by
      intro x hx
      obtain ⟨k,g,rfl⟩:=Finset.mem_image.mp hx
      apply Finset.mem_singleton.mpr
      by_contra f
      exact hh ⟨k,Finset.mem_filter.mpr ⟨g,f⟩⟩
    have d:=Finset.card_le_card p
    rw [B.sites,Finset.card_singleton] at d
    omega
  let j:=E.min' En
  have ej:=Finset.mem_filter.mp (E.min'_mem En)
  have wj:W j≠0:=(mem_activeRows j).mp ej.1
  apply Qn (ordered_quartic_physical Q deg (nz i wi) (nz j wj) ej.2 ?_ ?_)
  · intro R dR
    rw [←hQ]
    apply B.zero_filter ha wi R dR
    intro k kl wk
    exact False.elim ((not_le_of_gt kl) (D.min'_le _ ((mem_activeRows k).mpr wk)))
  · intro R dR
    let H:=R*(X-C u)
    have dH:H.natDegree≤2:=natDegree_mul_le.trans (by rw [natDegree_X_sub_C];omega)
    have h:=B.zero_filter ha wj H dH (by
      intro k kl wk
      have eu:c k=u:=by
        by_contra h
        exact (not_le_of_gt kl) (E.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows k).mpr wk,h⟩))
      change H.eval (c k)=0
      simp [H,eu])
    rwa [show H*P=R*(X*(X-C u)*Q) by dsimp [H];rw [hQ];ring] at h

theorem dx7_is_lobatto8 : (dx7:K[X])=lobatto 8:=by
  ext i
  by_cases h:i<11
  · rw [dx7_coeff i h,lobatto_coeff]
    interval_cases i <;> norm_num [lobattoCoeff,coeff_shiftedLegendre,Nat.choose]
  · exact (coeff_eq_zero_of_natDegree_lt (by have e:=dx7_degree (K:=K);omega)).trans
      (coeff_eq_zero_of_natDegree_lt (by have e:=RKCert.FixedFactor.degree_lobatto8 (K:=K);omega)).symm

theorem dx8_is_lobatto9 : (dx8:K[X])=lobatto 9:=by
  ext i
  by_cases h:i<11
  · rw [dx8_coeff i h,lobatto_coeff]
    interval_cases i <;> norm_num [lobattoCoeff,coeff_shiftedLegendre,Nat.choose]
  · exact (coeff_eq_zero_of_natDegree_lt (by have e:=dx8_degree (K:=K);omega)).trans
      (coeff_eq_zero_of_natDegree_lt (by have e:=lobatto_degree (K:=K) (m:=9) (by decide);omega)).symm

/-- The Jacobi pencil without the extraneous origin factor. -/
def oddPencil (a:K):K[X]:=
  C ((-1:K)^9)*((shiftedLegendre 9).derivative.map (Int.castRingHom K))+
  C a*(C ((-1:K)^8)*((shiftedLegendre 8).derivative.map (Int.castRingHom K)))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem X_mul_oddPencil (a:K) : X*oddPencil a=lobatto 9+C a*lobatto 8:=by
  unfold oddPencil lobatto
  ring

/-- Exact unsettled free-knot scalar data, with no order restriction on u. -/
structure OddPencilPorts (P:K[X]) (a u:K):Prop where
  degree:P.natDegree=5
  nonzero:u≠0
  omitted:P.eval u≠0
  root:(oddPencil a).eval u=0
  divides:P∣oddPencil a
  first:(Paired.primitive (X*P)).eval u=0
  second:(Paired.primitive (X^2*P)).eval u=0

set_option maxHeartbeats 2300000 in
theorem TrueFourPort.pencil_ports (B:TrueFourPort A b W θ P) (ha:StrictLower A)
    (origin:(0:K)∈headSites (nodes A) W):∃a u:K,OddPencilPorts P a u:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let c:=nodes A
  let T:=(headSites c W).erase 0
  have ct:T.card=3:=by rw [Finset.card_erase_of_mem origin,B.sites]
  let N:K[X]:=Lagrange.nodal T id
  have nd:N.natDegree=3:=Lagrange.natDegree_nodal.trans ct
  have N0 (a:K)(ha:a∈T):N.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
  let M:=X*(P*N)
  have dm:M.natDegree≤9:=by
    have h:=natDegree_mul_le (p:=X) (q:=P*N)
    have j:=natDegree_mul_le (p:=P) (q:=N)
    rw [natDegree_X] at h
    change M.natDegree≤1+(P*N).natDegree at h
    have k:=B.degree
    omega
  have db:M.coeff 0=0:=by simp [M]
  have bw(k:Fin 7):scalarMoment M k.val-scalarMoment M (k.val+1)=0:=by
    let S:K[X]:=X^k.val*(X*N)
    have deg:S.natDegree≤10:=by
      have p:=natDegree_mul_le (p:=X^k.val) (q:=X*N)
      have r:=natDegree_mul_le (p:=X) (q:=N)
      rw [natDegree_X_pow] at p
      rw [natDegree_X] at r
      change S.natDegree≤_ at p
      have kn:=k.isLt
      omega
    have E:=B.moments S deg
    have z:(∑i,weightedEval c W S i)=0:=by
      apply Finset.sum_eq_zero
      intro i _
      rw [weightedEval_apply]
      by_cases wi:W i=0
      · rw [wi,mul_zero]
      · by_cases y:c i=0
        · simp [S,y]
        · have h:c i∈T:=Finset.mem_erase.mpr ⟨y,headSites_mem (c:=c) i wi⟩
          simp [S,N0 _ h]
    rw [z] at E
    have e:S*((1-X)*P)=X^k.val*M-X^(k.val+1)*M:=by
      dsimp [S,M];rw [pow_succ];ring
    rw [e,map_sub,eval_sub] at E
    exact E.symm
  obtain ⟨a,e,M_eq⟩:=meshPrefix8_decode M dm db bw
  let J:Finset (Fin 26):=(activeRows W).filter (fun i=>c i≠0)
  have ne:J.Nonempty:=by
    obtain ⟨u,tu⟩:=Finset.card_pos.mp (by rw [ct];decide:0<T.card)
    obtain ⟨u0,ut⟩:=Finset.mem_erase.mp tu
    obtain ⟨i,iw,ic⟩:=Finset.mem_image.mp ut
    exact ⟨i,Finset.mem_filter.mpr ⟨iw,ic.symm ▸ u0⟩⟩
  let i:=J.min' ne
  let u:=c i
  have wu:=Finset.mem_filter.mp (J.min'_mem ne)
  have wi:W i≠0:=(mem_activeRows i).mp wu.1
  have un:u≠0:=wu.2
  have nt:u∈T:=Finset.mem_erase.mpr ⟨un,headSites_mem (c:=c) i wi⟩
  have pu:P.eval u≠0:=(B.on i wi).1 ▸ (B.on i wi).2
  have first(k:ℕ)(k1:1≤k)(k2:k≤2):(Paired.primitive (X^k*P)).eval u=0:=by
    apply B.zero_filter ha wi (X^k) (by rwa [natDegree_X_pow])
    intro j jl wj
    have h:c j=0:=by
      by_contra m
      exact (not_le_of_gt jl) (J.min'_le _ (Finset.mem_filter.mpr ⟨(mem_activeRows j).mpr wj,m⟩))
    change ((X:K[X])^k).eval (c j)=0
    rw [eval_pow,eval_X,h,zero_pow (by omega:k≠0)]
  by_cases ez:e=0
  · rw [ez,zero_smul,add_zero,dx7_is_lobatto8,smul_eq_C_mul] at M_eq
    have anz:a≠0:=by
      intro n
      apply B.nonzero
      have nN:N≠0:=by intro h;rw [h,natDegree_zero] at nd;omega
      rw [n,map_zero,zero_mul] at M_eq
      exact (mul_eq_zero.mp ((mul_eq_zero.mp M_eq).resolve_left X_ne_zero)).resolve_right nN
    have Div:P∣(lobatto (K:=K) 8):=by
      have hInv : C a⁻¹*C a=(1:K[X]):=by rw [←map_mul,inv_mul_cancel₀ anz,map_one]
      refine ⟨C a⁻¹*X*N,?_⟩
      calc
        lobatto 8=C a⁻¹*(C a*lobatto 8):=by rw [←mul_assoc,hInv,one_mul]
        _=C a⁻¹*M:=by rw [M_eq]
        _=P*(C a⁻¹*X*N):=by dsimp only [M];ring
    have root:(lobatto (K:=K) 8).eval u=0:=by
      have h:=congrArg (eval u) M_eq
      simp only [M,eval_mul,eval_X,eval_C,N0 u nt,mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left anz
    exact False.elim (RKCert.FixedFactor.lobatto8_first_moment Div B.degree un root
      (by simpa using first 1 (by decide) (by decide)))
  · have dM:9≤M.natDegree:=by
      apply le_natDegree_of_ne_zero
      have z:(dx7:K[X]).coeff 9=0:=coeff_eq_zero_of_natDegree_lt (by rw [dx7_degree];decide)
      rw [M_eq,coeff_add,smul_eq_C_mul,smul_eq_C_mul,coeff_C_mul,coeff_C_mul,z,dx8_coeff 9 (by decide)]
      norm_num
      exact ez
    have dP:P.natDegree=5:=by
      have g:=natDegree_mul_le (p:=X) (q:=P*N)
      have r:=natDegree_mul_le (p:=P) (q:=N)
      rw [natDegree_X] at g
      change M.natDegree≤_ at g
      have d:=B.degree
      omega
    let t:=a/e
    have PA:X*(C e*oddPencil t)=X*(P*N):=by
      rw [show X*(C e*oddPencil t)=C e*(X*oddPencil t) by ring,X_mul_oddPencil]
      change _=M
      rw [M_eq,dx7_is_lobatto8,dx8_is_lobatto9,smul_eq_C_mul,smul_eq_C_mul]
      have h:C e*C t=C a:=by rw [←map_mul,show e*t=a by dsimp [t];field_simp]
      rw [mul_add,←mul_assoc (C e),h,add_comm]
    have PZ:oddPencil t=C e⁻¹*P*N:=by
      have hInv : C e⁻¹*C e=(1:K[X]):=by rw [←map_mul,inv_mul_cancel₀ ez,map_one]
      calc
        oddPencil t=C e⁻¹*(C e*oddPencil t):=by rw [←mul_assoc,hInv,one_mul]
        _=C e⁻¹*(P*N):=by rw [mul_left_cancel₀ X_ne_zero PA]
        _=C e⁻¹*P*N:=(mul_assoc _ _ _).symm
    have root:(oddPencil t).eval u=0:=by rw [PZ,eval_mul,N0 u nt,mul_zero]
    refine ⟨t,u,⟨dP,un,pu,root,⟨C e⁻¹*N,?_⟩,?_,first 2 (by decide) (by decide)⟩⟩
    · rw [PZ];ring
    · simpa using first 1 (by decide) (by decide)
end
end RKCert.Paired.ERKOddHidden

