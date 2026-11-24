module

public import RKCert.ReviewedNative.ERKOrder16StrongThreePorts
public import RKCert.ReviewedNative.PaidClockCore
public import RKCert.ReviewedNative.QuadraticSeedCensus

@[expose] public section

/-! # From the strong native ERK16 width frame to the actual three-row mask

Two cheap clock shifts exclude the four-dimensional hidden carrier.
The five actual blind rows, fifteen seed rows, three contrast rows,
and genuine terminal then exhaust the original tableau. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

abbrev strongHiddenCarrier (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K) :=
  Hidden.carrier (nodes A) b (quadraticSeed A b) 0 (Fin.last 23)

private theorem strong_six_cap (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (r7 : finrank K (zeroSpace A 7)=8) :
    finrank K (zeroSpace A 6) ≤ 7 := by
  have g : finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) :=
    Submodule.finrank_lt_finrank_of_lt
      (zeroSpace_strict_of_separation ha (j:=6) (coeff_separated ho (q:=7) (by decide))
        (by decide) (by decide))
  omega

/-- The exact rank-five physical carrier. The argument only needs eight
quadratic seed values and the marked E7 horizon. -/
theorem width24_strong_hidden_five (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (r7 : finrank K (zeroSpace A 7)=8)
    (G : Width24StrongCover A b) :
    strongHiddenCarrier A b≤zeroSpace A 7 ∧
      (strongHiddenCarrier A b).map (diag (nodes A))≤strongHiddenCarrier A b ∧
      finrank K (strongHiddenCarrier A b)=5 := by
  let F := zeroSpace A
  let C := diag (nodes A)
  let H := strongHiddenCarrier A b
  let E := G.quadratic.frame
  have y0 : reflectedClock A (Fin.last 23)=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [E.lastClock,sub_self]
  have inc : H≤F 7 :=
    Hidden.carrier_le_defects (q:=7) ha ho (by decide) E.lastClock E.lastLive.live
      G.quadratic.lastSeed G.supports
  have inv : H.map C≤H := Hidden.carrier_invariant E.lastClock
  have four : F 4≤H := by
    have h := paid_clock_core_le_carrier (m:=7) (h:=6) (j:=4) (k:=0)
      ha ho y0 G.quadratic.lastSeed (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by exact G.sites) (fun _ hv=>G.poly_cover hv)
    simpa only [core_zero] using h
  have threeL : 2≤finrank K (F 3) := zeroSpace_finrank ha ho (n:=2) (by decide)
  have fourL : 3≤finrank K (F 4) := zeroSpace_finrank ha ho (n:=3) (by decide)
  have fourU : finrank K (F 4)≤finrank K H := Submodule.finrank_mono four
  have fourNot (r : finrank K (F 4)=3) : ¬ (F 4).map C≤F 4 := by
    intro stable
    have incoming := clock_invariant_incoming (j:=3) ha
      (PolySeparated.of_coeff (coeff_separated ho (q:=4) (by decide))) stable
    change finrank K (F 3)+2≤finrank K (F 4) at incoming
    omega
  have early (n : ℕ) : (F n).map C≤F (n+1) :=
    Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A n)
  have cap : finrank K H≤5 := by
    have outgoing := clock_invariant_outgoing (j:=7) ha
      (PolySeparated.of_coeff (coeff_separated ho (q:=7) (by decide))) inc inv
    change finrank K H+4≤finrank K (F 8) at outgoing
    have e : finrank K (F 8)=9 := E.forward
    omega
  have minH : 4≤finrank K H := by
    by_contra! small
    have r : finrank K (F 4)=3 := by omega
    have e : F 4=H := Submodule.eq_of_le_of_finrank_le four (by omega)
    exact fourNot r (by rw [e];exact inv)
  refine ⟨inc,inv,?_⟩
  by_contra nope
  change finrank K H≠5 at nope
  have h4 : finrank K H=4 := by omega
  have h5 : H≤F 5 := by
    by_cases f4high : finrank K (F 4)=4
    · have e : F 4=H := Submodule.eq_of_le_of_finrank_le four (by omega)
      exact e.ge.trans (zeroSpace_mono A (by decide))
    have f4exact : finrank K (F 4)=3 := by omega
    let W := F 4⊔(F 4).map C
    have wh : W≤H := sup_le four ((Submodule.map_mono four).trans inv)
    have lt : F 4<W := lt_of_le_of_ne le_sup_left
      (fun e=>fourNot f4exact (le_sup_right.trans e.ge))
    have rwW := Submodule.finrank_lt_finrank_of_lt lt
    have wH : W=H := Submodule.eq_of_le_of_finrank_le wh (by omega)
    exact wH.ge.trans (sup_le (zeroSpace_mono A (by decide)) (early 4))
  have gain := clock_invariant_outgoing (j:=5) ha
    (PolySeparated.of_coeff (coeff_separated ho (q:=5) (by decide))) h5 inv
  change finrank K H+3≤finrank K (F 6) at gain
  have up : finrank K (F 6)≤7 := strong_six_cap ha ho r7
  have f6 : finrank K (F 6)=7 := by omega
  have small : finrank K (F 6⊔(F 6).map C : Submodule K (Fin 24→K))≤8 := by
    have sub : F 6⊔(F 6).map C≤F 7 := sup_le (zeroSpace_mono A (by decide)) (early 6)
    exact (Submodule.finrank_mono sub).trans_eq r7
  have c1 := core_rank_step C (F 6) 0
  have c2 := core_rank_step C (F 6) 1
  rw [core_zero] at c1
  change finrank K (F 6)+finrank K (F 6)≤finrank K (core C (F 6) 1)+
    finrank K (F 6⊔(F 6).map C : Submodule K (Fin 24→K)) at c1
  change finrank K (core C (F 6) 1)+finrank K (F 6)≤finrank K (core C (F 6) 2)+
    finrank K (F 6⊔(F 6).map C : Submodule K (Fin 24→K)) at c2
  have cheap : core C (F 6) 2≤H :=
    paid_clock_core_le_carrier (m:=7) (h:=6) (j:=6) (k:=2)
      ha ho y0 G.quadratic.lastSeed (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by exact G.sites) (fun _ hv=>G.poly_cover hv)
  have cr := Submodule.finrank_mono cheap
  change finrank K (core C (F 6) 2)≤finrank K H at cr
  omega

/-- Four paid powers of any chosen nonhidden F5 head fill the F8 strip;
a premature dependence would already create a too large invariant at F7. -/
private theorem strong_head_strip (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (r7 : finrank K (zeroSpace A 7)=8)
    (r8 : finrank K (zeroSpace A 8)=9)
    (inc : strongHiddenCarrier A b≤zeroSpace A 7)
    (inv : (strongHiddenCarrier A b).map (diag (nodes A))≤strongHiddenCarrier A b)
    (rh : finrank K (strongHiddenCarrier A b)=5) :
    ∃ w∈zeroSpace A 5, w∉strongHiddenCarrier A b ∧
      zeroSpace A 8=chain (diag (nodes A)) (strongHiddenCarrier A b) w 4 := by
  let F := zeroSpace A
  let H := strongHiddenCarrier A b
  let C := diag (nodes A)
  change finrank K H=5 at rh
  change finrank K (F 8)=9 at r8
  have f5 : 5≤finrank K (F 5) := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have up : finrank K (F 6)≤7 := strong_six_cap ha ho r7
  have no5 : ¬F 5≤H := by
    intro hid
    have eq : F 5=H := Submodule.eq_of_le_of_finrank_le hid (by change finrank K H≤_;omega)
    have e := clock_invariant_outgoing (j:=5) ha
      (PolySeparated.of_coeff (coeff_separated ho (q:=5) (by decide))) eq.ge inv
    change finrank K H+3≤finrank K (F 6) at e
    omega
  obtain ⟨w,hw,hwH⟩ := Set.not_subset.mp no5
  change w∈F 5 at hw
  change w∉H at hwH
  let B := chain C H w
  have pow (k : ℕ) : (C^k) w∈F (5+k) := by
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self,Nat.add_zero] using hw
    | succ k ih =>
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact diag_zeroSpace A (5+k) ih
  have b7 (n : ℕ) (hn : n≤3) : B n≤F 7 :=
    (clock_chain_le_iff n).mpr ⟨inc,fun k hk=>zeroSpace_mono A (by omega) (pow k)⟩
  have b8 : B 4≤F 8 :=
    (clock_chain_le_iff 4).mpr ⟨inc.trans (zeroSpace_mono A (by decide)),
      fun k hk=>zeroSpace_mono A (by omega) (pow k)⟩
  have hB (n : ℕ) : H≤B n := ((clock_chain_le_iff n).mp (le_rfl : B n≤B n)).1
  have proper (n : ℕ) (hn : n<4) : B n<B (n+1) := by
    refine lt_of_le_of_ne (show B n≤B (n+1) from le_sup_left) (fun eq=>?_)
    have mem : w∈B (n+1) := by
      simpa only [pow_zero,one_apply_eq_self] using
        ((clock_chain_le_iff (n+1)).mp (le_rfl : B (n+1)≤B (n+1))).2 0 (by omega)
    have lose : w∈B n := eq.symm ▸ mem
    by_cases z:n=0
    · subst n
      exact hwH lose
    have stable : (B n).map C≤B n := by
      have e : B n⊔(B n).map C=B (n+1) := clock_chain_next inv (by omega)
      exact le_sup_right.trans (le_of_eq (e.trans eq.symm))
    have lt : H<B n := lt_of_le_of_ne (hB n) (fun h=>hwH (h.symm ▸ lose))
    have rank := Submodule.finrank_lt_finrank_of_lt lt
    have gain := clock_invariant_outgoing (j:=7) ha
      (PolySeparated.of_coeff (coeff_separated ho (q:=7) (by decide))) (b7 n (by omega)) stable
    change finrank K (B n)+4≤finrank K (F 8) at gain
    omega
  have room (n : ℕ) (hn : n≤4) : 5+n≤finrank K (B n) := by
    induction n with
    | zero =>
      change 5≤finrank K H
      exact rh.ge
    | succ n ih =>
      have a := ih (by omega)
      have d := Submodule.finrank_lt_finrank_of_lt (proper n (by omega))
      omega
  refine ⟨w,hw,hwH,(Submodule.eq_of_le_of_finrank_le b8 ?_).symm⟩
  change finrank K (F 8)≤finrank K (B 4)
  rw [r8]
  exact room 4 le_rfl

/-- Two numerical contrast sites would give eight paid zero X-moments
for a nonzero polynomial of degree at most seven. -/
private theorem strong_contrast_three (ho : HasOrder 16 A b) {Q P : K[X]}
    (qn : Q≠0) (qd : Q.natDegree≤5) (pd : P.natDegree≤4) :
    3≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card := by
  by_contra! few
  let y := reflectedClock A
  let d := reverseContrast A b Q P
  let S := weightedSites y d
  let Z := nodalHull S
  change S.card<3 at few
  have zd : Z.natDegree≤2 := by rw [show Z=nodalHull S from rfl,natDegree_nodalHull];omega
  have qz : (Q*Z).natDegree≤7 := natDegree_mul_le_of_le qd zd
  apply (mul_ne_zero qn (monic_nodalHull S).ne_zero)
  apply NativeMoments.x_moments_detect qz
  intro i
  let R : K[X] := X^i.val*Z
  have rd : R.natDegree≤9 :=
    natDegree_mul_le_of_le (show (X^i.val:K[X]).natDegree≤7 from by
      rw [natDegree_X_pow];have := i.isLt;omega) zd
  have Z0 : (∑ k,weightedEval y d R k)=0 := by
    apply reverse_contrast_vanishes
    intro x hx
    rw [show R=X^i.val*Z from rfl,eval_mul,nodalHull_eval_of_mem hx,mul_zero]
  have moment := reverse_contrast_moment ho Q P R (by omega) (by omega)
  change (∑ k,weightedEval y d R k)=(primitive (R*(X*Q))).eval 1 at moment
  rw [Z0,show R*(X*Q)=X^i.val*(X*(Q*Z)) by dsimp [R];ring] at moment
  exact moment.symm

/-- The source of the three-row mask is entirely paid on the original
width-24 tableau. No premise asserting mask existence is needed. -/
theorem width24_strong_actual_mask (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (r7 : finrank K (zeroSpace A 7)=8) :
    ∃ (w g : Fin 24→K) (Q P : K[X]), StrongThreeActualMask A b w g Q P := by
  classical
  let B := width24_strong_reverse_cover ha ho r7
  let E := B.quadratic.frame
  let H := strongHiddenCarrier A b
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let G := Hidden.blindRows c b d 0 t
  let T := Hidden.activeRows d
  obtain ⟨hH,hC,h5⟩ := width24_strong_hidden_five ha ho r7 B
  obtain ⟨w,hw,wo,form⟩ := strong_head_strip ha ho r7 E.forward hH hC h5
  obtain ⟨Q,P,qd,pd,qfit,pfit⟩ := B.two_traces ho hw
  have qn : Q≠0 := by
    intro z
    have h0 (i : Fin 24) : d i*w i=0 := by simpa only [d,z,eval_zero,zero_mul] using qfit i
    apply wo
    refine Hidden.actual_defect_hidden ha ho (by decide) hw h0 (fun i=>?_ )
    change y i*b i*w i=0
    by_cases di:d i=0
    · have e := pfit i
      change y i*b i*w i=P.eval (y i)*d i at e
      rwa [di,mul_zero] at e
    · rw [(mul_eq_zero.mp (h0 i)).resolve_left di,mul_zero]
  let z := reverseContrast A b Q P
  let V := strongThreeRows A b Q P
  have live (i : Fin 24) (hi : i∈V) :
      d i=0 ∧ y i≠0 ∧ b i≠0 ∧ Q.eval (y i)≠0 ∧ w i=0 :=
    reverse_contrast_true_support qfit pfit i ((Hidden.mem_activeRows i).mp hi)
  have y0 : y t=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [E.lastClock,sub_self]
  have d0 : d t=0 := B.quadratic.lastSeed
  have maskSeed (i : Fin 24) (hi : d i≠0) : z i=0 := by
    by_contra ne
    exact hi (reverse_contrast_true_support qfit pfit i ne).1
  have maskBlind (i : Fin 24) (hi : i∈G) : z i=0 := by
    by_contra ne
    obtain ⟨_,a,bi,_,_⟩ := reverse_contrast_true_support qfit pfit i ne
    exact mul_ne_zero a bi ((Hidden.mem_blindRows i).mp hi).2.2.2
  have maskTail : z t=0 := by
    by_contra ne
    exact (reverse_contrast_true_support qfit pfit t ne).2.1 y0
  have census := Hidden.carrier_contrast_budget (w:=z) (c:=c) (o:=0)
    E.lastLive.live d0 maskTail maskSeed maskBlind
  change finrank K H+T.card+V.card+1≤24 at census
  have imageT : T.image y=weightedSites y d := by
    ext a
    simp only [Finset.mem_image,Hidden.mem_activeRows,mem_weightedSites,T]
  have imageV : V.image y=weightedSites y z := by
    ext a
    simp only [Finset.mem_image,Hidden.mem_activeRows,mem_weightedSites,V,strongThreeRows,z]
  have useS : (weightedSites y d).card≤T.card := by rw [←imageT];exact Finset.card_image_le
  have useV : (weightedSites y z).card≤V.card := by rw [←imageV];exact Finset.card_image_le
  have moreV : 3≤(weightedSites y z).card := strong_contrast_three ho qn qd pd
  have s8 : 8≤(weightedSites y d).card := B.sites
  change finrank K H=5 at h5
  have s15 : 15≤(weightedSites y d).card := by
    by_contra! few
    have double := quadratic_seed_double_rows ho (by change (weightedSites y d).card+2≤16;omega)
    change 2*(weightedSites y d).card≤T.card at double
    omega
  have t15 : T.card=15 := by omega
  have v3 : V.card=3 := by omega
  have vs3 : (weightedSites y z).card=3 := by omega
  have g5 : G.card=5 :=
    (Hidden.carrier_rank (c:=c) (d:=d) (o:=0) E.lastLive.live).symm.trans h5
  have ysimple : Set.InjOn y (V : Set (Fin 24)) :=
    Finset.card_image_iff.mp (by rw [imageV,vs3,v3])
  have csimple : Set.InjOn c (V : Set (Fin 24)) := by
    intro i hi j hj ce
    apply ysimple hi hj
    change 1-c i=1-c j
    rw [ce]
  have GT : Disjoint G T := Finset.disjoint_left.mpr fun i gi ti=>
    (Hidden.mem_activeRows _).mp ti ((Hidden.mem_blindRows _).mp gi).2.2.1
  have GV : Disjoint G V := Finset.disjoint_left.mpr fun i gi vi=>
    (Hidden.mem_activeRows _).mp vi (maskBlind i gi)
  have TV : Disjoint T V := Finset.disjoint_left.mpr fun i ti vi=>
    (Hidden.mem_activeRows _).mp vi (maskSeed i ((Hidden.mem_activeRows _).mp ti))
  have dis : Disjoint (G∪T) V := Finset.disjoint_union_left.mpr ⟨GV,TV⟩
  have ntG : t∉G := fun h=>((Hidden.mem_blindRows _).mp h).2.1 rfl
  have ntT : t∉T := fun h=>(Hidden.mem_activeRows _).mp h d0
  have ntV : t∉V := fun h=>(Hidden.mem_activeRows _).mp h maskTail
  have nt : t∉(G∪T)∪V := by simp [ntG,ntT,ntV]
  have full : insert t ((G∪T)∪V)=(Finset.univ : Finset (Fin 24)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    change 24≤(insert t ((G∪T)∪V)).card
    rw [Finset.card_insert_of_notMem nt,Finset.card_union_of_disjoint dis,
      Finset.card_union_of_disjoint GT,g5,t15,v3]
  let q := Q.comp (1-X)
  have refl (i : Fin 24) : q.eval (c i)=Q.eval (y i) := by
    simp [q,c,y,reflectedClock,eval_comp]
  obtain ⟨g,hg,fill⟩ := Hidden.carrier_filler (t:=t) (o:=0) (d:=d) (c:=c)
    (f:=evalNodes A q-w) E.lastLive.live
  have outside (i : Fin 24) (ni : i∉V) (it : i≠t) : strongThreeMask A Q w g i=0 := by
    have iS : i∈insert t ((G∪T)∪V) := by rw [full];exact Finset.mem_univ _
    have iU : i∈G∪T := ((Finset.mem_union.mp ((Finset.mem_insert.mp iS).resolve_left it)).resolve_right ni)
    change q.eval (c i)-(w i+g i)=0
    rcases Finset.mem_union.mp iU with gi|ti
    · have e := fill i gi
      change g i=q.eval (c i)-w i at e
      rw [e]
      ring
    · have dn : d i≠0 := (Hidden.mem_activeRows i).mp ti
      have wi : w i=Q.eval (y i) := mul_left_cancel₀ dn
        ((qfit i).trans (mul_comm _ _))
      have gi : g i=0 := Hidden.carrier_zero_on_active d0 hg dn
      rw [gi,add_zero,wi,refl,sub_self]
  have off (v : Fin 24→K) (hv : v∈zeroSpace A 8)
      (i : Fin 24) (iv : i∈V) : v i=0 := by
    obtain ⟨u,hu,R,_,eq⟩ := HeadFiber.exists_poly (form.le hv)
    obtain ⟨_,yn,bi,_,wi⟩ := live i iv
    have ui : u i=0 := (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero E.lastClock hu i)).resolve_left
      (mul_ne_zero yn bi)
    rw [eq,Pi.add_apply,weightedEval_apply,ui,wi,mul_zero,add_zero]
  exact ⟨w,g,Q,P,⟨hw,⟨H,hH,hC,hg⟩,qd,pd,qfit,pfit,outside,off,v3,csimple⟩⟩

theorem width24_strong_actual_ports_and_origin
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b) (r7 : finrank K (zeroSpace A 7)=8) :
    ∃ (w g : Fin 24→K) (Q P : K[X]) (ι : Fin 3→Fin 24),
      StrongThreeActualMask A b w g Q P ∧ StrongThreePhysicalPorts A b Q P ι ∧ ι 0=0 := by
  obtain ⟨w,g,Q,P,M⟩ := width24_strong_actual_mask ha ho r7
  obtain ⟨ι,N,orig⟩ := width24_strong_three_ports_and_origin ha ho r7 M
  exact ⟨w,g,Q,P,ι,M,N,orig⟩

end
end RKResearch.Certified.ERK16
