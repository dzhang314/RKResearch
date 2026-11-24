module
public import RKCert.ERKOddContrastSites
public import RKCert.ERKFiveHiddenStaircase
public import RKCert.ERKOddHiddenFiller
public import RKCert.DirkEvenPhysicalCount

@[expose] public section
/-! # The zero-seed ordered p17 case with five genuine hidden dimensions
This leaf earns four disjoint actual measured rows and the forward
primitive equations on those rows. It assumes no polynomial scalar gate. -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Paired.ReverseHull RKCert.Paired.ERKEvenHidden
open RKCert.Paired.Clock RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K} {b:Vec K 26}
noncomputable section
set_option maxRecDepth 3500
set_option maxHeartbeats 2600000

/-- A genuine observed row receives only the four chronological observed
rows (a possible uncompensated final value has zero effect). -/
structure TrueFourPort (A:Fin 26→Fin 26→K) (b W θ:Vec K 26) (P:K[X]) : Prop where
  nonzero:P≠0
  degree:P.natDegree≤5
  sites:(headSites (nodes A) W).card=4
  rows:(activeRows W).card=4
  last:W (Fin.last 25)=0
  on:∀i,W i≠0→ θ i=P.eval (nodes A i) ∧ θ i≠0
  off:∀i,W i=0→i≠Fin.last 25→θ i=0
  initial:W 0=0→P.eval 0=0
  moments:∀ R:K[X],R.natDegree≤10→
    (∑i,weightedEval (nodes A) W R i)=(primitive (R*((1-X)*P))).eval 1
  primitive:∀R:K[X],R.natDegree≤2→∀i,W i≠0→
    mat A (weightedEval (nodes A) θ R) i=(Paired.primitive (R*P)).eval (nodes A i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem eval_mirror_twice {s:ℕ}{A:Fin s→Fin s→K} (P:K[X]) (i:Fin s):
    (reflectPolynomial P).eval (mirror A i)=P.eval (nodes A i):=by
  simp [reflectPolynomial,eval_comp,mirror]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem eval_reflect_nodes {s:ℕ}{A:Fin s→Fin s→K} (P:K[X]) (i:Fin s):
    (reflectPolynomial P).eval (nodes A i)=P.eval (mirror A i):=by
  simp [reflectPolynomial,eval_comp,mirror]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem reflect_involution_polynomial (P:K[X]):reflectPolynomial (reflectPolynomial P)=P:=by
  have E:((1-X:K[X]).comp (1-X))=X:=by simp
  rw [reflectPolynomial,reflectPolynomial,comp_assoc,E,comp_X]

theorem odd17_zero_five_actual_ports (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (S:OddBalanced (s:=25) A b 8)(Z:OddZeroReverse (s:=25) A b 8)
    (dim:finrank K (carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25))=5):
    ∃W θ:Vec K 26,∃P:K[X],TrueFourPort A b W θ P:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let t:=Fin.last 25
  let d:=backSeed2 A b
  let Y:=mirror A
  let c:=nodes A
  let G:=blindRows c b d 0 t
  let U:=carrier c b d 0 t
  have ⟨_,u8,inv⟩:=balanced_odd_hidden_zero ha ho (by decide) S Z
  obtain ⟨h,hn⟩:=five_hidden_staircase ha ho (by decide) (by decide) S.separated S.forwardMid
    (by have e:=S.nextCap;omega) dim u8 inv
  have y0:Y t=0:=S.lastReflect Z.firstZero
  have sites:7<(headSites Y d).card:=Z.sites
  obtain ⟨Q,E,dQ,dE,qfit,efit⟩:=thin_reverse_two_traces (m:=8) (h:=6) ho hn.headGrade
    (by decide) (by decide) (by decide) t y0 Z.lastSeed sites
    (fun _ hw=>Z.poly_cover (by decide) hw)
  have qn:Q≠0:=by
    intro q0
    have dd(i:Fin 26):d i*h i=0:=by simpa [d,q0] using qfit i
    have bb(i:Fin 26):((1-c i)*b i)*h i=0:=by
      by_cases e:d i=0
      · simpa [d,c,mirror,e] using efit i
      · rw [(mul_eq_zero.mp (dd i)).resolve_left e,mul_zero]
    exact hn.outside (actual_defect_hidden ha ho (by decide) hn.headGrade dd bb)
  let W:=reverseContrast A b Q E
  have act(i:Fin 26)(wi:W i≠0):
      d i=0 ∧ Y i≠0 ∧ b i≠0 ∧ Q.eval (Y i)≠0 ∧ h i=0:=
    reverse_contrast_true_support qfit efit i wi
  have wT:W t=0:=by
    by_contra nz
    exact (act t nz).2.1 y0
  have wG(i:Fin 26)(ig:i∈G):W i=0:=by
    obtain ⟨_,_,dd,byes⟩:=(mem_blindRows i).mp ig
    have h0:Y i*b i=0:=by simpa [Y,mirror] using byes
    change (weightedEval Y b (X*Q)-weightedEval Y d E) i=0
    simp only [Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,dd,mul_zero,sub_zero]
    calc
      _=(Y i*b i)*Q.eval (Y i):=by ring
      _=0:=by rw [h0,zero_mul]
  have noD(i:Fin 26)(di:d i≠0):W i=0:=by
    by_contra nw
    exact di (act i nw).1
  have D16:16≤(activeRows d).card:=by
    apply Terminal.signed_fiber_payment Y d 8 (by omega)
    intro R pay
    have e:=seed_eval_mass ho R (by omega)
    simpa only [weightedEval_apply,mul_comm] using e
  have W4:4≤(headSites Y W).card:=odd17_contrast_four_sites ha ho Z Q E qn dQ (by omega)
    (fun i wi=>(act i wi).1)
  have Wrk:(headSites Y W).card≤(activeRows W).card:=Finset.card_image_le
  have bill:=carrier_contrast_budget (w:=W) S.lastLive Z.lastSeed wT noD wG
  have dimU:finrank K U=5:=dim
  change finrank K U+(activeRows d).card+(activeRows W).card+1≤26 at bill
  have w4:(activeRows W).card=4:=by omega
  have w4y:(headSites Y W).card=4:=by omega
  have d16:(activeRows d).card=16:=by omega
  have g5:G.card=5:=by rw [←carrier_rank S.lastLive];exact dim
  have disgd:Disjoint G (activeRows d):=Finset.disjoint_left.mpr fun i a e=>
    (mem_activeRows i).mp e ((mem_blindRows i).mp a).2.2.1
  have disgw:Disjoint G (activeRows W):=Finset.disjoint_left.mpr fun i a e=>
    (mem_activeRows i).mp e (wG i a)
  have disdw:Disjoint (activeRows d) (activeRows W):=Finset.disjoint_left.mpr fun i a e=>
    (mem_activeRows i).mp e (noD i ((mem_activeRows i).mp a))
  have tail:t∉(G∪activeRows d)∪activeRows W:=by
    have sd:d t=0:=Z.lastSeed
    have gt:t∉G:=fun h=>((mem_blindRows t).mp h).2.1 rfl
    simp [Finset.mem_union,gt,mem_activeRows,sd,wT]
  have whole:insert t ((G∪activeRows d)∪activeRows W)=Finset.univ:=by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem tail,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disgw,disdw⟩),
      Finset.card_union_of_disjoint disgd,g5,d16,w4,Fintype.card_fin]
  have cover(i:Fin 26)(nt:i≠t)(wz:W i=0):i∈G∨d i≠0:=by
    have e:i∈insert t ((G∪activeRows d)∪activeRows W):=whole ▸ Finset.mem_univ _
    simpa [Finset.mem_insert,Finset.mem_union,mem_activeRows,nt,wz] using e
  let R:=reflectPolynomial Q
  have rn:R≠0:=by
    intro rz
    have e:=reflect_involution_polynomial Q
    change reflectPolynomial R=Q at e
    rw [rz,reflectPolynomial,zero_comp] at e
    exact qn e.symm
  have rd:R.natDegree≤5:=(reflectPolynomial_degree Q).trans dQ
  obtain ⟨k,hk,fit⟩:=carrier_filler (c:=c) (d:=d) (o:=0) (t:=t) (f:=evalNodes A R-h) S.lastLive
  let θ:=evalNodes A R-h-k
  have keyT(i:Fin 26)(e:d i≠0):h i=R.eval (c i):=by
    rw [eval_reflect_nodes]
    have er:=qfit i
    rw [mul_comm (Q.eval _)] at er
    exact mul_left_cancel₀ e er
  have kg(i:Fin 26)(wi:W i≠0):k i=0:=
    (mem_ambientHidden.mp hk).1 i (fun ig=>wi (wG i ig)) (fun e=>wi (e ▸ wT))
  have on(i:Fin 26)(wi:W i≠0):θ i=R.eval (c i) ∧ θ i≠0:=by
    have e:θ i=R.eval (c i):=by simp [θ,c,(act i wi).2.2.2.2,kg i wi]
    exact ⟨e,e.symm ▸ (by rw [eval_reflect_nodes];exact (act i wi).2.2.2.1)⟩
  have off(i:Fin 26)(wz:W i=0)(nt:i≠t):θ i=0:=by
    rcases cover i nt wz with ig|di
    · change (evalNodes A R-h) i-k i=0
      rw [fit i ig,sub_self]
    · change R.eval (c i)-h i-k i=0
      rw [keyT i di,sub_self,carrier_zero_on_active Z.lastSeed hk di,sub_zero]
  have t0:t≠0:=by
    intro e
    have c0:c 0=0:=Finset.sum_eq_zero fun i _=>ha 0 i (Fin.zero_le i)
    exact zero_ne_one (c0.symm.trans (e ▸ Z.lastNode))
  have origin(wz:W 0=0):R.eval 0=0:=by
    have og:¬(0:Fin 26)∈G:=fun e=>((mem_blindRows 0).mp e).1 rfl
    have di:=(cover 0 (Ne.symm t0) wz).resolve_left og
    have c0:c 0=0:=Finset.sum_eq_zero fun i _=>ha 0 i (Fin.zero_le i)
    have he:=keyT 0 di
    have h0:=origin_zeroSpace A ha 5 hn.headGrade
    change h 0=0 at h0
    rwa [c0,h0,eq_comm] at he
  have count:(headSites c W).card=4:=by
    have eq:headSites c W=(headSites Y W).image (fun x=>1-x):=by
      change (activeRows W).image c=((activeRows W).image Y).image (fun x=>1-x)
      rw [Finset.image_image]
      congr 1;funext i;change nodes A i=1-(1-nodes A i);ring
    rw [eq,Finset.card_image_of_injective _ (by intro a b e;linear_combination -e),w4y]
  have quad(H:K[X])(deg:H.natDegree≤10):
      (∑i,weightedEval c W H i)=(Paired.primitive (H*((1-X)*R))).eval 1:=by
    let J:=reflectPolynomial H
    have dj:J.natDegree≤10:=(reflectPolynomial_degree H).trans deg
    have m:=reverse_contrast_moment ho Q E J (by omega) (by omega)
    have summ:(∑i,weightedEval c W H i)=∑i,weightedEval Y W J i:=by
      apply Finset.sum_congr rfl;intro i _;simp [c,Y,J,eval_mirror_twice]
    have flipped:(J*(X*Q)).comp (1-X)=H*((1-X)*R):=by
      rw [mul_comp,mul_comp,show J.comp (1-X)=H from reflect_involution_polynomial H,X_comp]
      rfl
    rw [summ,m,←flipped]
    exact (RKCert.OrderedGram.moment_reflect _).symm
  have clean(i:Fin 26)(wi:W i≠0)(v:Vec K 26)(hv:v∈zeroSpace A 8):v i=0:=by
    rw [hn.midpoint] at hv
    obtain ⟨u,hu,_,_,eq⟩:=Clock.exists_head_poly hv
    have u0:u i=0:=(mem_ambientHidden.mp hu).1 i (fun ig=>wi (wG i ig)) (fun e=>wi (e ▸ wT))
    rw [eq i,u0,(act i wi).2.2.2.2,mul_zero,zero_add]
  refine ⟨W,θ,R,⟨rn,rd,count,w4,wT,on,off,origin,quad,?_⟩⟩
  intro H dH i wi
  have hd:(H*R).natDegree≤7:=natDegree_mul_le.trans (by omega)
  have q0:=primitive_defect A (H*R) hd
  have F0:=clean i wi _ q0
  have u0:weightedEval c h H∈zeroSpace A 7:=by
    have eq:weightedEval c h H=h*evalNodes A H:=by
      ext j
      simp only [weightedEval_apply,Pi.mul_apply,evalNodes_apply,c]
      exact mul_comm _ _
    rw [eq]
    exact zeroSpace_mul_treeSpace ho (m:=5) (n:=2) (by decide) hn.headGrade (evalNodes_mem_treeSpace _ _ dH)
  have u1:weightedEval c k H∈zeroSpace A 6:=by
    have eq:weightedEval c k H=(fun i=>H.eval (c i)*k i):=by ext j;exact weightedEval_apply _ _ _ _
    rw [eq]
    exact hn.inside (Clock.poly_preserves inv H k hk)
  have f1:=clean i wi _ (zeroSpace_mono A (by decide:7+1≤8) (mat_zeroSpace_charZero A 7 u0))
  have f2:=clean i wi _ (zeroSpace_mono A (by decide:6+1≤8) (mat_zeroSpace_charZero A 6 u1))
  have e:weightedEval c θ H=evalNodes A (H*R)-weightedEval c h H-weightedEval c k H:=by
    ext j
    simp only [weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,θ,c]
    ring
  rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,f1,f2,sub_zero,sub_zero]
  exact sub_eq_zero.mp F0
end
end RKCert.Paired.ERKOddHidden
