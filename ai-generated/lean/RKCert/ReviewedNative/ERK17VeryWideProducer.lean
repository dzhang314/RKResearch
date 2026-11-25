module

public import RKCert.ReviewedNative.ERK17UnitFourPort

@[expose] public section

/-! # The ordinary very-wide branch produces a unit signed four-port

Seventeen actual first-seed rows, four signed contrasts, and the five
actual inactive rows exhaust width 26. The forward grade-nine clock
step pays the full degree-three primitive without a terminal exception. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch.Certified.Graded.Reverse.Hidden (activeRows mem_activeRows)
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K]

private def flip (P : K[X]) : K[X] := P.comp (1-X)

private theorem flip_involution (P : K[X]) : flip (flip P)=P := by
  unfold flip
  rw [comp_assoc,show ((1-X:K[X]).comp (1-X))=X by simp,comp_X]

private theorem flip_degree (P : K[X]) : (flip P).natDegree≤P.natDegree := by
  unfold flip
  apply natDegree_comp_le.trans
  rw [Thin.one_sub_X_natDegree,mul_one]

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

set_option maxRecDepth 3500 in
set_option maxHeartbeats 1350000 in
theorem WideLinear.very_wide_unit_ports (B : WideLinear A b)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (nz : firstSeed A b≠0)
    (wide : 17≤(weightedSites (reflectedClock A) (firstSeed A b)).card) :
    ∃ W θ : Fin 26→K,∃ R : K[X],UnitPhysicalFourPort (s:=25) A W θ R := by
  classical
  let : DecidableEq K := Classical.decEq K
  let c := nodes A
  let Y := reflectedClock A
  let d := firstSeed A b
  let G := inactiveRows A b
  let U := FirstWide.carrier A b
  obtain ⟨h,h5,hNot,h6,chain9⟩ := B.forward_nine_head ha ho S nz
  obtain ⟨Q,E,dQ,dE,tr⟩ := two_traces ho B.firstCover h5 (by decide) (by decide) (by decide)
  have qn : Q≠0 := fun qz => hNot (mem_carrier_iff.mpr (fit_invisible tr qz))
  let W := linearContrast A b Q E
  have act (i : Fin 26) (wi : W i≠0) : d i=0 ∧ b i≠0 ∧ Q.eval (Y i)≠0 ∧ h i=0 :=
    tr.contrast_support wi
  have g5 : G.card=5 := (carrier_rank_eq_inactive_card (A:=A) (b:=b)).symm.trans
    (B.carrier_rank_five ha ho S)
  have d17 : 17≤(activeRows d).card := wide.trans (show (weightedSites Y d).card≤(activeRows d).card from Finset.card_image_le)
  have w4 : 4≤(weightedSites Y W).card := contrast_four_sites_of_order17 ho Q E qn dQ dE
  have hw : (weightedSites Y W).card≤(activeRows W).card := Finset.card_image_le
  have gd : Disjoint G (activeRows d) := Finset.disjoint_left.mpr (fun i gi di =>
    ((mem_activeRows i).mp di) (mem_inactiveRows.mp gi).1)
  have gw : Disjoint G (activeRows W) := Finset.disjoint_left.mpr (fun i gi wi =>
    (act i ((mem_activeRows i).mp wi)).2.1 (mem_inactiveRows.mp gi).2)
  have dw : Disjoint (activeRows d) (activeRows W) := Finset.disjoint_left.mpr (fun i di wi =>
    (mem_activeRows i).mp di (act i ((mem_activeRows i).mp wi)).1)
  let T := (G∪activeRows d)∪activeRows W
  have cnt : T.card=5+(activeRows d).card+(activeRows W).card := by
    dsimp only [T]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨gw,dw⟩),
      Finset.card_union_of_disjoint gd,g5]
  have cap : T.card≤26 := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  have sites : (weightedSites Y W).card=4 := by omega
  have full : T=Finset.univ := Finset.eq_univ_of_card T (by rw [Fintype.card_fin];omega)
  have cover (i : Fin 26) (wz : W i=0) : i∈G∨d i≠0 := by
    have e : i∈T := full ▸ Finset.mem_univ i
    simpa [T,Finset.mem_union,mem_activeRows,wz] using e
  let R := flip Q
  have rn : R≠0 := by
    intro z
    have e := flip_involution Q
    change flip R=Q at e
    rw [z,flip,zero_comp] at e
    exact qn e.symm
  have rd : R.natDegree≤5 := (flip_degree Q).trans dQ
  have reflect (P : K[X]) (i : Fin 26) : (flip P).eval (Y i)=P.eval (c i) := by
    rw [flip,eval_comp,eval_sub,eval_one,eval_X]
    congr 1
    change 1-(1-nodes A i)=nodes A i
    ring
  have reflR (i : Fin 26) : R.eval (c i)=Q.eval (Y i) := by
    have h := reflect R i
    rwa [show flip R=Q from flip_involution Q,eq_comm] at h
  obtain ⟨k,hk,fit⟩ := inactive_filler (b:=b) (evalNodes A R-h)
  let θ := evalNodes A R-h-k
  have key (i : Fin 26) (di : d i≠0) : h i=R.eval (c i) := by
    rw [reflR]
    have e := tr.1 i
    rw [mul_comm (Q.eval _)] at e
    exact mul_left_cancel₀ di e
  have live (i : Fin 26) (wi : W i≠0) : FirstWide.visible A b i :=
    Or.inr (act i wi).2.1
  have on (i : Fin 26) (wi : W i≠0) : θ i=R.eval (c i) ∧ θ i≠0 := by
    have he : θ i=R.eval (c i) := by
      simp [θ,c,(act i wi).2.2.2,mem_carrier_iff.mp hk i (live i wi)]
    exact ⟨he,by rw [he,reflR]; exact (act i wi).2.2.1⟩
  have off (i : Fin 26) (wz : W i=0) : θ i=0 := by
    rcases cover i wz with g|di
    · change (evalNodes A R-h) i-k i=0
      rw [fit i g,sub_self]
    · change R.eval (c i)-h i-k i=0
      rw [key i di,mem_carrier_iff.mp hk i (Or.inl di),sub_self,sub_zero]
  have eqSupport (i : Fin 26) : θ i≠0↔W i≠0 :=
    ⟨fun h z=>h (off i z),fun w=>(on i w).2⟩
  have origin (t0 : θ 0=0) : R.eval 0=0 := by
    have wz : W 0=0 := by by_contra n; exact (eqSupport 0).mpr n t0
    have no : (0:Fin 26)∉G := by
      intro e
      obtain ⟨u,hu,filled⟩ := inactive_filler (A:=A) (b:=b) (1:Fin 26→K)
      have inF := B.firstCover.carrier_pure ho (by decide) hu
      have z := origin_zeroSpace ha 8 inF
      change u 0=0 at z
      have f := filled 0 e
      rw [z,Pi.one_apply] at f
      exact zero_ne_one f
    have dz := (cover 0 wz).resolve_left no
    have he := key 0 dz
    have h0 := origin_zeroSpace ha 5 h5
    change h 0=0 at h0
    rwa [show c 0=0 from unit_origin_clock_zero ha,h0,eq_comm] at he
  have count : (weightedSites c θ).card=4 := by
    have e : weightedSites c θ=(weightedSites Y W).image (fun x=>1-x) := by
      ext x
      rw [mem_weightedSites,Finset.mem_image]
      constructor
      · rintro ⟨i,wi,rfl⟩
        exact ⟨Y i,mem_weightedSites.mpr ⟨i,(eqSupport i).mp wi,rfl⟩,by
          change 1-(1-nodes A i)=nodes A i;ring⟩
      · rintro ⟨y,hy,eq⟩
        obtain ⟨i,wi,rfl⟩ := mem_weightedSites.mp hy
        exact ⟨i,(eqSupport i).mpr wi,(show c i=1-Y i by change nodes A i=1-(1-nodes A i);ring).trans eq⟩
    rw [e,Finset.card_image_of_injective _ (by intro a b e;linear_combination -e),sites]
  have quad (H : K[X]) (hh : H.natDegree≤11) :
      (primitive (H*R)).eval 1=∑i,H.eval (c i)*W i := by
    let J := flip H
    let B := J*Q
    let D := H*R
    have dj : J.natDegree≤11 := (flip_degree H).trans hh
    have bd : B.natDegree≤16 := by
      have e := natDegree_mul_le (p:=J) (q:=Q)
      dsimp [B]
      omega
    have dd : D.natDegree≤16 := by
      have e := natDegree_mul_le (p:=H) (q:=R)
      dsimp [D]
      omega
    have eq : flip B=D := by
      unfold flip
      change (J*Q).comp (1-X)=D
      rw [mul_comp]
      change flip J*R=D
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
    have sm := linear_contrast_moment ho Q E J (by omega) (by omega)
    have read : (∑ i,weightedEval Y W J i)=∑i,H.eval (c i)*W i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedEval_apply,reflect H i]
    exact prim.trans (sm.symm.trans read)
  have clean (i : Fin 26) (wi : W i≠0) (v : Fin 26→K) (hv : v∈zeroSpace A 9) : v i=0 := by
    rw [chain9] at hv
    obtain ⟨u,hu,P,_,e⟩ := HeadFiber.exists_poly hv
    rw [e,Pi.add_apply,mem_carrier_iff.mp hu i (live i wi),weightedEval_apply,
      (act i wi).2.2.2,mul_zero,zero_add]
  refine ⟨W,θ,R,⟨rn,rd,count,on,off,origin,?_,?_⟩⟩
  · intro H hdeg
    simpa only [weightedEval_apply] using (quad H hdeg).symm
  · intro H hdeg i θi
    have wi := (eqSupport i).mp θi
    have hd : (H*R).natDegree≤8 := natDegree_mul_le.trans (by omega)
    have pf := clean i wi _ (primitive_defect A (H*R) hd)
    have hdef : weightedEval c h H∈zeroSpace A 8 := by
      have e : weightedEval c h H=h*evalNodes A H := by ext j; simp [c,mul_comm]
      rw [e]
      exact zeroSpace_mul_treeSpace ho (m:=5) (n:=3) (by decide) h5
        (evalNodes_mem_treeSpace _ _ hdeg)
    have kdef : weightedEval c k H∈zeroSpace A 6 :=
      h6 (mem_carrier_iff.mpr fun j hv => by
        rw [weightedEval_apply,mem_carrier_iff.mp hk j hv,mul_zero])
    have f1 := clean i wi _ (mat_zeroSpace_charZero A 8 hdef)
    have f2 := clean i wi _ (zeroSpace_mono A (by decide : 7≤9) (mat_zeroSpace_charZero A 6 kdef))
    have e : weightedEval c θ H=evalNodes A (H*R)-weightedEval c h H-weightedEval c k H := by
      ext j
      simp only [weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,θ,c]
      ring
    change mat A (weightedEval c θ H) i=_
    rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,f1,f2,sub_zero,sub_zero]
    exact sub_eq_zero.mp pf

end
end RKResearch.Certified.ERK17
