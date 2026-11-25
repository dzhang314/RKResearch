module

public import RKCert.ReviewedNative.ERK17ContrastCount
public import RKCert.ReviewedNative.ERK17HiddenRank
public import RKCert.ReviewedNative.FiveHiddenHead
public import RKCert.ReviewedNative.ERK17PhysicalPorts
public import RKCert.ReviewedNative.ERK17OriginChronologicalPorts

@[expose] public section

/-! # Produce all four primitive ports on the actual width-26 matrix -/
namespace RKResearch.Certified.ERK17
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKResearch.Certified.Graded.Reverse.Hidden
open RKCert.ReviewedNative.OriginSignedSquares
open scoped Classical

noncomputable section

variable {K : Type*} [Field K]

private def flip (P : K[X]) : K[X] := P.comp (1-X)

private theorem flip_involution (P : K[X]) : flip (flip P)=P := by
  unfold flip
  rw [comp_assoc,show ((1-X:K[X]).comp (1-X))=X by simp,comp_X]

private theorem flip_degree (P : K[X]) : (flip P).natDegree≤P.natDegree := by
  unfold flip
  apply natDegree_comp_le.trans
  rw [one_sub_X_natDegree,mul_one]

private theorem weighted_core_mem {s : ℕ} {c : Fin s→K} {U : Submodule K (Fin s→K)}
    (stable : U.map (diag c)≤U) {v : Fin s→K} (hv : v∈U) (P : K[X]) :
    weightedEval c v P∈U := by
  have powers (n : ℕ) : (diag c ^ n) v∈U := by
    induction n with
    | zero => simpa only [pow_zero,one_apply_eq_self] using hv
    | succ n ih => rw [pow_succ',mul_apply_eq_comp]; exact stable (Submodule.mem_map_of_mem ih)
  have sum : weightedEval c v P=
      ∑ n∈P.support,weightedEval c v (monomial n (P.coeff n)) := by
    conv_lhs => rw [P.as_sum_support,map_sum]
  rw [sum]
  apply U.sum_mem
  intro n _
  have eq : weightedEval c v (monomial n (P.coeff n))=P.coeff n • (diag c ^ n) v := by
    ext i
    simp only [weightedEval_apply,eval_monomial,Pi.smul_apply,smul_eq_mul,
      HeadFiber.clock_power_value]
    ring
  rw [eq]
  exact U.smul_mem _ (powers n)

private theorem first_clock_zero {A : Matrix (Fin 26) (Fin 26) K}
    (ha : ∀ i j,i≤j → A i j=0) : nodes A 0=0 := by
  change (∑ j,A 0 j * (1:K))=0
  exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j),zero_mul]

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

set_option maxRecDepth 3500 in
set_option maxHeartbeats 1400000 in
theorem width26_actual_four_port_from_cover (gate : RadauFirstGate K)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (Z : Width26QuadraticCover A b) :
    ∃ W θ : Fin 26→K, ∃ P : K[X], PhysicalFourPort (s:=25) A W θ P ∧
      (active W).card=4 ∧ ActualReflectedAffinePacket A b W (reflectedProfile P) := by
  classical
  let : DecidableEq K := Classical.decEq K
  let t:=Fin.last 25
  let d:=quadraticSeed A b
  let Y:=reflectedClock A
  let c:=nodes A
  let G:=blindRows c b d 0 t
  let U:=carrier c b d 0 t
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have e := S.nextRoom
    change finrank K (zeroSpace A 9)+_≤11 at e
    omega
  let F := width26_hidden_frame ha ho S Z
  have dim : finrank K U=5 := width26_hidden_rank_five ha ho S Z F
  have inv : U.map (diag c)≤U := F.stable
  obtain ⟨h,hn⟩ := five_hidden_staircase ha (by decide) S.separated S.middleDefects
    cap dim F.toEight inv
  have y0 : Y t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have many : 7<(weightedSites Y d).card := Z.sites
  obtain ⟨Q,E,dQ,dE,qfit,efit⟩ := thin_reverse_two_traces (m:=8) (h:=6) ho hn.headGrade
    (by decide) (by decide) (by decide) t y0 Z.lastSeed many Z.pointwise
  have qn:Q≠0:=by
    intro q0
    have dd(i:Fin 26):d i*h i=0:=by simpa [d,q0] using qfit i
    have bb(i:Fin 26):((1-c i)*b i)*h i=0:=by
      by_cases e:d i=0
      · simpa [d,c,reflectedClock,e] using efit i
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
    have h0:Y i*b i=0:=by simpa [Y,reflectedClock] using byes
    change (weightedEval Y b (X*Q)-weightedEval Y d E) i=0
    simp only [Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,dd,mul_zero,sub_zero]
    calc
      _=(Y i*b i)*Q.eval (Y i):=by ring
      _=0:=by rw [h0,zero_mul]
  have noD(i:Fin 26)(di:d i≠0):W i=0:=by
    by_contra nw
    exact di (act i nw).1
  have D16:16≤(activeRows d).card:=by
    apply signed_fiber_payment Y d 8 (by omega)
    intro R pay
    have e:=seed_eval_mass ho R (by omega)
    simpa only [weightedEval_apply,mul_comm] using e
  have W4:4≤(weightedSites Y W).card:=width26_contrast_four_sites_of_radau gate ha ho Z Q E qn dQ dE
    (fun i wi=>(act i wi).1)
  have Wrk:(weightedSites Y W).card≤(activeRows W).card:=Finset.card_image_le
  have bill:=carrier_contrast_budget (w:=W) Z.lastLive.live Z.lastSeed wT noD wG
  have dimU:finrank K U=5:=dim
  change finrank K U+(activeRows d).card+(activeRows W).card+1≤26 at bill
  have w4:(activeRows W).card=4:=by omega
  have w4y:(weightedSites Y W).card=4:=by omega
  have d16:(activeRows d).card=16:=by omega
  have g5:G.card=5:=by rw [←carrier_rank Z.lastLive.live];exact dim
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
  let R := flip Q
  have rd : R.natDegree≤5 := (flip_degree Q).trans dQ
  have reflect (P : K[X]) (i : Fin 26) : (flip P).eval (Y i)=P.eval (c i) := by
    rw [flip,eval_comp,eval_sub,eval_one,eval_X]
    congr 1
    change 1-(1-nodes A i)=nodes A i
    ring
  have reflR (i : Fin 26) : R.eval (c i)=Q.eval (Y i) := by
    have h := reflect R i
    rwa [show flip R=Q from flip_involution Q,eq_comm] at h
  obtain ⟨k,hk,fit⟩ := carrier_filler (c:=c) (d:=d) (o:=0) (t:=t)
    (f:=evalNodes A R-h) Z.lastLive.live
  let θ := evalNodes A R-h-k
  have key (i : Fin 26) (nz : d i≠0) : h i=R.eval (c i) := by
    rw [reflR]
    have e := qfit i
    rw [mul_comm (Q.eval _)] at e
    exact mul_left_cancel₀ nz e
  have vis (i : Fin 26) (wi : W i≠0) : visible A b i :=
    Or.inr (mul_ne_zero (act i wi).2.1 (act i wi).2.2.1)
  have on (i : Fin 26) (wi : W i≠0) : R.eval (c i)≠0 := by
    rw [reflR]
    exact (act i wi).2.2.2.1
  have off (i : Fin 26) (wi : W i=0) (nt : i≠t) : θ i=0 := by
    rcases cover i nt wi with ig|di
    · change (evalNodes A R-h) i-k i=0
      rw [fit i ig,sub_self]
    · change R.eval (c i)-h i-k i=0
      rw [key i di,sub_self,carrier_zero_on_active Z.lastSeed hk di,sub_zero]
  have t0 : t≠0 := by
    intro e
    exact zero_ne_one ((first_clock_zero ha).symm.trans (e ▸ Z.lastClock))
  have origin (wz : W 0=0) : R.eval 0=0 := by
    have ng : ¬(0:Fin 26)∈G := fun e => ((mem_blindRows 0).mp e).1 rfl
    have di := (cover 0 (Ne.symm t0) wz).resolve_left ng
    have he := key 0 di
    have h0 := origin_zeroSpace ha 5 hn.headGrade
    change h 0=0 at h0
    rwa [show c 0=0 from first_clock_zero ha,h0,eq_comm] at he
  have count : (RKResearch.Certified.ERK17.sites c W).card=4 := by
    have eq : RKResearch.Certified.ERK17.sites c W=(weightedSites Y W).image (fun x=>1-x) := by
      ext x
      rw [mem_sites,Finset.mem_image]
      constructor
      · rintro ⟨i,wi,rfl⟩
        exact ⟨Y i,mem_weightedSites.mpr ⟨i,wi,rfl⟩,by change 1-(1-nodes A i)=nodes A i; ring⟩
      · rintro ⟨y,hy,e⟩
        obtain ⟨i,wi,rfl⟩ := mem_weightedSites.mp hy
        exact ⟨i,wi,(show c i=1-Y i by change nodes A i=1-(1-nodes A i); ring).trans e⟩
    rw [eq,Finset.card_image_of_injective _ (by intro a b e; linear_combination -e),w4y]
  have quad (H : K[X]) (hh : H.natDegree≤10) :
      (primitive (H*((1-X)*R))).eval 1=∑i,H.eval (c i)*W i := by
    let J := flip H
    let B := J*(X*Q)
    let D := H*((1-X)*R)
    have dj : J.natDegree≤10 := (flip_degree H).trans hh
    have bd : B.natDegree≤16 := by
      have e := natDegree_mul_le (p:=J) (q:=X*Q)
      have i := natDegree_mul_le (p:=X) (q:=Q)
      rw [natDegree_X] at i
      dsimp [B]
      omega
    have dd : D.natDegree≤16 := by
      have e := natDegree_mul_le (p:=H) (q:=(1-X)*R)
      have i := natDegree_mul_le (p:=(1-X:K[X])) (q:=R)
      rw [one_sub_X_natDegree] at i
      dsimp [D]
      omega
    have eq : flip B=D := by
      unfold flip
      change (J*(X*Q)).comp (1-X)=D
      rw [mul_comp,mul_comp,X_comp]
      change flip J*((1-X)*R)=D
      rw [show flip J=H from flip_involution H]
    have now := probe_evalNodes ho D 0 (by omega)
    have law : (∑i,D.eval (c i)*b i)=(primitive D).eval 1 := by
      rw [pow_zero,one_mul] at now
      simpa only [probe,pow_zero,mul_one,row_apply,dotProduct,evalNodes_apply,c,mul_comm] using now
    have reflMass := reflected_polynomial_mass ho B (by omega)
    have sumB : (∑i,weightedEval Y b B i)=∑i,D.eval (c i)*b i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedEval_apply,←eq]
      have h := reflect (flip B) i
      rw [flip_involution] at h
      exact congrArg (fun u : K => u*b i) h
    have prim : (primitive D).eval 1=(primitive B).eval 1 := law.symm.trans (sumB.symm.trans reflMass)
    have sm := reverse_contrast_moment ho Q E J (by omega) (by omega)
    have read : (∑ i,weightedEval Y W J i)=∑i,H.eval (c i)*W i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedEval_apply,reflect H i]
    exact prim.trans (sm.symm.trans read)
  have clean (i : Fin 26) (wi : W i≠0) (v : Fin 26→K) (hv : v∈zeroSpace A 8) :
      v i=0 := by
    rw [hn.midpoint] at hv
    obtain ⟨u,hu,P,_,e⟩ := HeadFiber.exists_poly hv
    rw [e,Pi.add_apply,F.invisible u hu i (vis i wi),weightedEval_apply,
      (act i wi).2.2.2.2,mul_zero,add_zero]
  refine ⟨W,θ,R,⟨rd,count,on,fun i w n=>off i w n,origin,?_,?_⟩,?_,?_⟩
  · intro H hh
    rw [formalPrimitive_eq_native]
    exact quad H hh
  · intro H hdeg i wi
    rw [formalPrimitive_eq_native]
    have hd : (H*R).natDegree≤7 := natDegree_mul_le.trans (by omega)
    have fd := clean i wi _ (primitive_defect A (H*R) hd)
    have hdef : weightedEval c h H∈zeroSpace A 7 := by
      have e : weightedEval c h H=h*evalNodes A H := by ext i; simp [c,mul_comm]
      rw [e]
      exact zeroSpace_mul_treeSpace ho (m:=5) (n:=2) (by decide) hn.headGrade
        (evalNodes_mem_treeSpace _ _ hdeg)
    have kdef : weightedEval c k H∈zeroSpace A 6 := hn.inside (weighted_core_mem inv hk H)
    have f1 := clean i wi _ (mat_zeroSpace_charZero A 7 hdef)
    have f2 := clean i wi _ (zeroSpace_mono A (by decide : 7≤8) (mat_zeroSpace_charZero A 6 kdef))
    have e : weightedEval c θ H=evalNodes A (H*R)-weightedEval c h H-weightedEval c k H := by
      ext j
      simp only [weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,θ,c]
      ring
    have input : (fun j => H.eval (nodes A j)*θ j)=weightedEval c θ H := by
      ext j
      rw [weightedEval_apply]
    rw [input,e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,f1,f2,sub_zero,sub_zero]
    exact sub_eq_zero.mp fd
  · have eq : active W=activeRows W := by
      ext i
      exact (mem_active W i).trans (mem_activeRows i).symm
    rw [eq]
    exact w4
  · change ActualReflectedAffinePacket A b W (flip R)
    rw [show flip R=Q from flip_involution Q]
    have covered : SupportsComplement A b 8 t :=
      supportsComplement_of_cover (h:=6) (fun v hv =>
        Z.poly_cover (mem_zeroAt.mp hv).1 (mem_zeroAt.mp hv).2)
    exact ActualReflectedAffinePacket.of_contrast ho y0
      (fun i=>ha i t (Fin.le_last i)) covered Q E (by omega) (by omega)
      (fun i wi=>⟨(act i wi).1,(act i wi).2.2.1,(act i wi).2.1⟩)

/-- Keep the previously checked physical four-port interface unchanged. -/
theorem width26_physical_four_port_from_cover (gate : RadauFirstGate K)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (Z : Width26QuadraticCover A b) :
    ∃ W θ : Fin 26→K, ∃ P : K[X], PhysicalFourPort (s:=25) A W θ P := by
  obtain ⟨W,θ,P,H,_,_⟩ := width26_actual_four_port_from_cover gate ha ho S Z
  exact ⟨W,θ,P,H⟩

/-- Retain the live-row count and the reflected affine trace on the actual
witness. The earlier signed contrast-count scalar gate stays explicit. -/
theorem ordered_width26_actual_four_port (gate : RadauFirstGate K)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (zero : firstSeed A b=0) :
    ∃ W θ : Fin 26→K, ∃ P : K[X], PhysicalFourPort (s:=25) A W θ P ∧
      (active W).card=4 ∧ ActualReflectedAffinePacket A b W (reflectedProfile P) :=
  width26_actual_four_port_from_cover gate ha ho (ordered_width26_full_frame ha ho).1
    (ordered_width26_quadratic_cover ha ho zero)

theorem ordered_width26_physical_four_port (gate : RadauFirstGate K)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (zero : firstSeed A b=0) :
    ∃ W θ : Fin 26→K, ∃ P : K[X], PhysicalFourPort (s:=25) A W θ P :=
  width26_physical_four_port_from_cover gate ha ho (ordered_width26_full_frame ha ho).1
    (ordered_width26_quadratic_cover ha ho zero)

end
end RKResearch.Certified.ERK17
