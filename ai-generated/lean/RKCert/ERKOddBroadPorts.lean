module
public import RKCert.ERKOddBroadFour
public import RKCert.ERKOddSignedRows
public import RKCert.ERKOddFourPort

@[expose] public section
/-! # The original wide branch yields four observed unit-weight ports -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Paired.ERKEvenHidden
open RKCert.Paired.ERKOddHidden RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b:Vec K 26}
noncomputable section

/-- Same physical port data also suffice for the localized branch.
Unlike the zero-linear-seed case, scalar moments carry unit weight and
each observed stage earns a cubic test. -/
structure TrueUnitFourPorts (A:Fin 26→Fin 26→K) (W θ:Vec K 26) (P:K[X]):Prop where
  nonzero:P≠0
  degree:P.natDegree≤5
  sites:(headSites (nodes A) W).card=4
  on:∀i,W i≠0→ θ i=P.eval (nodes A i) ∧ θ i≠0
  off:∀i,W i=0→θ i=0
  initial:W 0=0→P.eval 0=0
  moments:∀R:K[X],R.natDegree≤11→
    (∑i,weightedEval (nodes A) W R i)=(Paired.primitive (R*P)).eval 1
  primitive:∀R:K[X],R.natDegree≤3→∀i,W i≠0→
    mat A (weightedEval (nodes A) θ R) i=(Paired.primitive (R*P)).eval (nodes A i)

private theorem broad_contrast_four (ho:HasTreeOrderAtLeast A b 17) (Q P:K[X])
    (qn:Q≠0)(qd:Q.natDegree≤5)(pd:P.natDegree≤4):
    4≤(headSites (mirror A) (linearContrast A b Q P)).card:=by
  classical
  let y:=mirror A
  let W:=linearContrast A b Q P
  let S:=headSites y W
  by_contra! few
  change S.card<4 at few
  let T:K[X]:=Lagrange.nodal S id
  have td:T.natDegree=S.card:=Lagrange.natDegree_nodal
  have tn:T≠0:=Lagrange.nodal_ne_zero
  let R:K[X]:=T^2*Q
  have rr:R.natDegree≤11:=by
    have t:=natDegree_mul_le (p:=T^2) (q:=Q)
    rw [natDegree_pow,td] at t
    change R.natDegree≤_ at t
    omega
  have h:=linear_contrast_moment ho Q P R (by omega) (by omega)
  have z:(∑i,weightedEval y W R i)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    rw [weightedEval_apply]
    by_cases e:W i=0
    · rw [e,mul_zero]
    have t:T.eval (y i)=0:=Lagrange.eval_nodal_at_node (v:=id) (headSites_mem (c:=y) i e)
    simp [R,t]
  change (∑i,weightedEval y W R i)=_ at h
  rw [z,show R*Q=(T*Q)^2 by dsimp only [R];ring] at h
  have pos:=RKCert.OrderedGram.pow_square_pos 0 (T*Q) (mul_ne_zero tn qn)
  rw [pow_zero,one_mul] at pos
  exact pos.ne' h.symm

set_option maxHeartbeats 3600000 in
theorem BroadLinearCover.actual_unit_four_ports (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8):
    ∃W θ:Vec K 26,∃P:K[X],TrueUnitFourPorts A W θ P:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let t:=Fin.last 25
  let e:=terminal (K:=K) 25
  let c:=nodes A
  let Y:=mirror A
  let d:=backSeed1 A b
  let U:=linearCarrier A b
  let G:=blindRows c e (linearProbeMask A b) 0 t
  have dim:finrank K U=5:=B.hidden_rank_five ha ho S
  have inc:U≤zeroSpace A 8:=fun _ h=>B.pure_off_linear ho ((linear_carrier_iff S.lastLive).mp h).2
  have inv:U.map (diag c)≤U:=linear_carrier_clock S.lastLive
  have sites:8<(headSites Y d).card:=B.sites
  have dn:d≠0:=fun z=>by rw [z] at sites;simp [headSites] at sites
  have br:finrank K (back A b 0)=1:=finrank_span_singleton dn
  have cap:finrank K (zeroSpace A 9)≤10:=by
    have v:=S.nextCap
    change finrank K (zeroSpace A 9)+finrank K (back A b 0)≤11 at v
    omega
  obtain ⟨h,hn⟩:=five_hidden_staircase ha ho (by decide) (by decide) S.separated S.forwardMid
    (cap.trans (by decide:10≤11)) dim inc inv
  obtain ⟨Q,E,dQ,dE,fit⟩:=broad_linear_two_traces ho B hn.headGrade (by decide) (by decide) (by decide)
  have qn:Q≠0:=by
    intro z
    exact hn.outside ((linear_carrier_iff S.lastLive).mpr
      ⟨origin_zeroSpace A ha 5 hn.headGrade,linear_fit_invisible fit z⟩)
  let W:=linearContrast A b Q E
  have act(i:Fin 26)(wi:W i≠0):d i=0∧b i≠0∧Q.eval (Y i)≠0∧h i=0:=fit.contrast_support wi
  have offG(i:Fin 26)(ig:i∈G):¬linearVisible A b i:=fun vh=>
    ((linear_probe_live i).mpr vh) ((mem_blindRows i).mp ig).2.2.1
  have bg(i:Fin 26)(ig:i∈G):d i=0∧b i=0:=
    ⟨not_ne_iff.mp (fun a=>offG i ig (Or.inl a)),not_ne_iff.mp (fun a=>offG i ig (Or.inr a))⟩
  have wG(i:Fin 26)(ig:i∈G):W i=0:=by
    by_contra nz
    exact (act i nz).2.1 (bg i ig).2
  have bT:e t≠0:=by rw [show e t=1 from terminal_at_last];exact one_ne_zero
  have g5:G.card=5:=by rw [←carrier_rank bT];exact dim
  have nd:17≤(activeRows d).card:=by
    apply paid_signed_row_lower Y d (k:=9) (by omega) (by decide)
    intro R pay
    have a:=linear_seed_mass ho R (by omega)
    simpa only [weightedEval_apply,mul_comm] using a
  have nw:4≤(headSites Y W).card:=broad_contrast_four ho Q E qn dQ (by omega)
  have leW:(headSites Y W).card≤(activeRows W).card:=Finset.card_image_le
  have GD:Disjoint G (activeRows d):=Finset.disjoint_left.mpr fun i ig hd=>
    ((mem_activeRows i).mp hd) (bg i ig).1
  have GW:Disjoint G (activeRows W):=Finset.disjoint_left.mpr fun i ig hw=>
    ((mem_activeRows i).mp hw) (wG i ig)
  have DW:Disjoint (activeRows d) (activeRows W):=Finset.disjoint_left.mpr fun i hd hw=>
    ((mem_activeRows i).mp hd) (act i ((mem_activeRows i).mp hw)).1
  let whole:Finset (Fin 26):=(G∪activeRows d)∪activeRows W
  have count:whole.card=5+(activeRows d).card+(activeRows W).card:=by
    dsimp only [whole]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨GW,DW⟩),
      Finset.card_union_of_disjoint GD,g5]
  have ccap:=Finset.card_le_univ whole
  rw [Fintype.card_fin] at ccap
  have wn:(activeRows W).card=4:=by omega
  have ws:(headSites Y W).card=4:=by omega
  have eq:whole=Finset.univ:=Finset.eq_univ_of_card whole (by rw [Fintype.card_fin];omega)
  have offW(i:Fin 26)(w0:W i=0):i∈G∨d i≠0:=by
    have t:i∈whole:=eq ▸ Finset.mem_univ _
    simpa [whole,Finset.mem_union,mem_activeRows,w0] using t
  let R:=reflectPolynomial Q
  have rn:R≠0:=by
    intro hz
    have p:=reflect_involution_polynomial Q
    change reflectPolynomial R=Q at p
    rw [hz,reflectPolynomial,zero_comp] at p
    exact qn p.symm
  have rd:R.natDegree≤5:=(reflectPolynomial_degree Q).trans dQ
  obtain ⟨k,kU,hk⟩:=carrier_filler (c:=c) (d:=linearProbeMask A b) (o:=0) (t:=t)
    (f:=evalNodes A R-h) bT
  let θ:=evalNodes A R-h-k
  have hD(i:Fin 26)(di:d i≠0):h i=R.eval (c i):=by
    rw [show c i=nodes A i from rfl,eval_reflect_nodes]
    have eq:=fit.1 i
    change d i*h i=Q.eval (Y i)*d i at eq
    rw [mul_comm (Q.eval (Y i)) (d i)] at eq
    exact mul_left_cancel₀ di eq
  have hon(i:Fin 26)(wi:W i≠0):θ i=R.eval (c i)∧θ i≠0:=by
    have z:=((linear_carrier_iff S.lastLive).mp kU).2 i (Or.inr (act i wi).2.1)
    have e':θ i=R.eval (c i):=by simp [θ,c,(act i wi).2.2.2,z]
    refine ⟨e',?_⟩
    rw [e',show c i=nodes A i from rfl,eval_reflect_nodes]
    exact (act i wi).2.2.1
  have hoff(i:Fin 26)(wi:W i=0):θ i=0:=by
    rcases offW i wi with ig|di
    · change (evalNodes A R-h) i-k i=0
      rw [hk i ig,sub_self]
    change R.eval (c i)-h i-k i=0
    rw [hD i di,((linear_carrier_iff S.lastLive).mp kU).2 i (Or.inl di),sub_self,sub_zero]
  have horg(w0:W 0=0):R.eval 0=0:=by
    have z:=offW 0 w0
    have d0:d 0≠0:=z.resolve_left (fun h=>((mem_blindRows 0).mp h).1 rfl)
    have H:=hD 0 d0
    have c0:c 0=0:=Finset.sum_eq_zero fun i _=>ha 0 i (Fin.zero_le i)
    have h0:=origin_zeroSpace A ha 5 hn.headGrade
    change h 0=0 at h0
    rwa [h0,c0,eq_comm] at H
  have wsc:(headSites c W).card=4:=by
    have he:headSites c W=(headSites Y W).image (fun x=>1-x):=by
      change (activeRows W).image c=((activeRows W).image Y).image (fun x=>1-x)
      rw [Finset.image_image]
      congr 1;funext i;change nodes A i=1-(1-nodes A i);ring
    rw [he,Finset.card_image_of_injective _ (by intro a b e;linear_combination -e),ws]
  have quad(H:K[X])(deg:H.natDegree≤11):
      (∑i,weightedEval c W H i)=(Paired.primitive (H*R)).eval 1:=by
    let J:=reflectPolynomial H
    have jd:J.natDegree≤11:=(reflectPolynomial_degree H).trans deg
    have z:=linear_contrast_moment ho Q E J (by omega) (by omega)
    have eq:(∑i,weightedEval c W H i)=∑i,weightedEval Y W J i:=by
      apply Finset.sum_congr rfl;intro i _;simp [c,Y,J,eval_mirror_twice]
    have pair:(J*Q).comp (1-X)=H*R:=by
      rw [mul_comp,show J.comp (1-X)=H from reflect_involution_polynomial H]
      rfl
    rw [eq,z,←pair]
    exact (RKCert.OrderedGram.moment_reflect _).symm
  have clean(i:Fin 26)(wi:W i≠0)(v:Vec K 26)(hv:v∈zeroSpace A 9):v i=0:=by
    rw [hn.top cap] at hv
    obtain ⟨u,hu,_,_,e⟩:=Clock.exists_head_poly hv
    have z:=((linear_carrier_iff S.lastLive).mp hu).2 i (Or.inr (act i wi).2.1)
    rw [e i,z,(act i wi).2.2.2,mul_zero,zero_add]
  refine ⟨W,θ,R,⟨rn,rd,wsc,hon,hoff,horg,quad,?_⟩⟩
  intro H dH i wi
  have hd:(H*R).natDegree≤8:=natDegree_mul_le.trans (by omega)
  have pf:=clean i wi _ (primitive_defect A (H*R) hd)
  have h0:weightedEval c h H∈zeroSpace A 8:=by
    have e:weightedEval c h H=h*evalNodes A H:=by
      ext j;simp only [weightedEval_apply,Pi.mul_apply,evalNodes_apply,c];exact mul_comm _ _
    rw [e]
    exact zeroSpace_mul_treeSpace ho (m:=5) (n:=3) (by decide) hn.headGrade (evalNodes_mem_treeSpace _ _ dH)
  have k0:weightedEval c k H∈zeroSpace A 6:=by
    have e:weightedEval c k H=(fun i=>H.eval (c i)*k i):=by ext j;exact weightedEval_apply _ _ _ _
    rw [e]
    exact hn.inside (Clock.poly_preserves inv H k kU)
  have f1:=clean i wi _ (mat_zeroSpace_charZero A 8 h0)
  have f2:=clean i wi _ (zeroSpace_mono A (by decide:6+1≤9) (mat_zeroSpace_charZero A 6 k0))
  have e:weightedEval c θ H=evalNodes A (H*R)-weightedEval c h H-weightedEval c k H:=by
    ext j;simp only [weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,θ,c];ring
  rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,f1,f2,sub_zero,sub_zero]
  exact sub_eq_zero.mp pf

end
end RKCert.Paired.ReverseHull

