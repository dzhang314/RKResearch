module

public import RKCert.ReviewedNative.ERKOrder16WeakFivePorts
public import RKCert.ReviewedNative.NativeHiddenCarrier
public import RKCert.ReviewedNative.ClockHeadFibers
public import RKCert.ReviewedNative.OrderedNodalGain
public import RKCert.ReviewedNative.PhysicalEndpointMomentPorts

@[expose] public section

/-! # The original grade-four source and grade-seven support of the weak-five mask

The three blind coordinates are filled by a genuine vector in the
terminal-compensated carrier. Equality in the 15+3+5+1 physical count
ensures no unlabelled rows remain. The absent origin would leave a
cubic in the already checked characteristic-zero 3+2 endpoint gate. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
variable {Q P : K[X]}

abbrev width24WeakFiveCarrier (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K) :=
  Hidden.carrier (nodes A) b (quadraticSeed A b) 0 (Fin.last 23)

/-- The remaining native entry to the mask construction. Both actual
grade-four admissions and the one-head grade-seven strip are explicit
hypotheses; the mask itself is not assumed. -/
structure Width24WeakFiveChart (A : Matrix (Fin 24) (Fin 24) K)
    (b w : Fin 24 → K) (Q P : K[X]) : Prop where
  carrierRank : finrank K (width24WeakFiveCarrier A b)=3
  carrierGrade : width24WeakFiveCarrier A b≤zeroSpace A 4
  headGrade : w∈zeroSpace A 4
  seventh : zeroSpace A 7=chain (diag (nodes A)) (width24WeakFiveCarrier A b) w 4
  seedSites : 15≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card
  contrastSites : 5≤(weightedSites (reflectedClock A) (reverseContrast A b Q P)).card
  qDegree : Q.natDegree≤4
  pDegree : P.natDegree≤3
  qFit : ∀ i, quadraticSeed A b i*w i=Q.eval (reflectedClock A i)*quadraticSeed A b i
  pFit : ∀ i, reflectedClock A i*b i*w i=P.eval (reflectedClock A i)*quadraticSeed A b i

theorem Width24WeakFiveChart.contrast_data (H : Width24WeakFiveChart A b w Q P)
    {i : Fin 24} (hi : i∈weakFiveRows A b Q P) :
    quadraticSeed A b i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧
    Q.eval (reflectedClock A i)≠0 ∧ w i=0 :=
  reverse_contrast_true_support H.qFit H.pFit i ((mem_weakFiveRows i).mp hi)

theorem Width24WeakFiveChart.seventh_zero (H : Width24WeakFiveChart A b w Q P)
    (ct : nodes A (Fin.last 23)=1) (f : Fin 24 → K) (hf : f∈zeroSpace A 7)
    (i : Fin 24) (hi : i∈weakFiveRows A b Q P) : f i=0 := by
  obtain ⟨_,y,bi,_,wi⟩ := H.contrast_data hi
  obtain ⟨u,hu,R,_,rfl⟩ := HeadFiber.exists_poly (H.seventh.le hf)
  have ui : u i=0 := (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero ct hu i)).resolve_left
    (mul_ne_zero y bi)
  simp only [Pi.add_apply,weightedEval_apply,ui,wi,mul_zero,add_zero]

private theorem weak_five_mask_prefix [CharZero K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    {q : K[X]} {θ : Fin 24 → K} (qd : q.natDegree≤4)
    (src : ∃ x∈zeroSpace A 4, θ=evalNodes A q-x)
    (off : ∀ i, i∉weakFiveRows A b Q P → i≠Fin.last 23 → θ i=0)
    (f7 : ∀ f∈zeroSpace A 7, ∀ i∈weakFiveRows A b Q P, f i=0)
    (R : K[X]) (rd : R.natDegree≤2) {i : Fin 24} (hi : i∈weakFiveRows A b Q P)
    (pre : ∀ j < i, j∈weakFiveRows A b Q P → R.eval (nodes A j)=0) :
    (primitive (R*q)).eval (nodes A i)=0 := by
  obtain ⟨x,hx,e⟩ := src
  have feed : weightedEval (nodes A) θ R =
      evalNodes A (R*q)-x*evalNodes A R := by
    rw [e]
    ext j
    simp only [weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.mul_apply,eval_mul]
    ring
  have xd : x*evalNodes A R∈zeroSpace A 6 :=
    zeroSpace_mul_treeSpace ho (by decide : 2+1≤16) hx (evalNodes_mem_treeSpace A R rd)
  have zm := f7 _ (mat_zeroSpace_charZero A 6 xd) i hi
  have fact := f7 _ (primitive_defect A (R*q) (natDegree_mul_le_of_le rd qd)) i hi
  change mat A (evalNodes A (R*q)) i-(primitive (R*q)).eval (nodes A i)=0 at fact
  have zs : mat A (weightedEval (nodes A) θ R) i=0 := by
    apply causal_mat ha
    intro j hj
    by_cases jv : j∈weakFiveRows A b Q P
    · simp only [weightedEval_apply,pre j hj jv,zero_mul]
    · have jt : j≠Fin.last 23 := fun e=>not_lt_of_ge (Fin.le_last i) (e ▸ hj)
      simp only [weightedEval_apply,off j jv jt,mul_zero]
  rwa [feed,map_sub,Pi.sub_apply,zm,sub_zero,sub_eq_zero.mp fact] at zs

/-- Once the true source and support have been constructed, the origin
follows from the already checked cubic 3+2 gate. No degree-four
eliminations or table replay are involved. -/
theorem weak_five_origin_of_source [CharZero K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    {q : K[X]} {θ : Fin 24 → K} (qd : q.natDegree≤4)
    (src : ∃ x∈zeroSpace A 4, θ=evalNodes A q-x)
    (off : ∀ i, i∉weakFiveRows A b Q P → i≠Fin.last 23 → θ i=0)
    (f7 : ∀ f∈zeroSpace A 7, ∀ i∈weakFiveRows A b Q P, f i=0)
    (live : ∀ i∈weakFiveRows A b Q P,q.eval (nodes A i)≠0)
    (nV : (weakFiveRows A b Q P).card=5)
    (simple : Set.InjOn (nodes A) (weakFiveRows A b Q P : Set (Fin 24))) :
    (0:Fin 24)∈weakFiveRows A b Q P := by
  classical
  let V := weakFiveRows A b Q P
  by_contra absent
  have c0 : nodes A (0:Fin 24)=0 := by
    change (∑ j,A 0 j*(1:K))=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have q0 : q.eval 0=0 := by
    obtain ⟨x,hx,e⟩ := src
    have z := off 0 absent (by decide)
    have x0 : x 0=0 := origin_zeroSpace ha 4 hx
    rwa [e,Pi.sub_apply,evalNodes_apply,c0,x0,sub_zero] at z
  have dv : (X:K[X])∣q := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  obtain ⟨L,eq⟩ := dv
  have neV : V.Nonempty := Finset.card_pos.mp (by change 0<(weakFiveRows A b Q P).card; omega)
  let i := V.min' neV
  have hi : i∈V := V.min'_mem neV
  let B := V.erase i
  have nB : B.Nonempty := Finset.card_pos.mp (by
    change 0<(V.erase i).card
    rw [Finset.card_erase_of_mem hi]
    change 0<(weakFiveRows A b Q P).card-1
    omega)
  let j := B.min' nB
  obtain ⟨ji,hj⟩ := Finset.mem_erase.mp (B.min'_mem nB)
  have qn : q≠0 := fun z=>live i hi (by rw [z,eval_zero])
  have ln : L≠0 := fun z=>qn (by rw [eq,z,mul_zero])
  have ld : L.natDegree≤3 := by rw [eq,natDegree_X_mul ln] at qd;omega
  have nz (k : Fin 24) (hk : k∈V) : nodes A k≠0 :=
    fun e=>live k hk (by rw [e,q0])
  apply ln (RKCert.EndpointPhysical.cubic_eq_zero_of_primitives ld (nz i hi) (nz j hj)
    (fun e=>ji (simple hj hi e)) ⟨?_,?_⟩)
  · intro R rd
    rw [formalPrimitive_eq_native,←eq]
    apply weak_five_mask_prefix ha ho qd src off f7 R rd hi
    intro k ki kv
    exact False.elim ((not_le_of_gt ki) (V.min'_le k kv))
  · intro R rd
    let H := R*(X-C (nodes A i))
    have hd : H.natDegree≤2 := by
      have e := natDegree_mul_le (p:=R) (q:=X-C (nodes A i))
      rw [natDegree_X_sub_C] at e
      dsimp [H]
      omega
    have test := weak_five_mask_prefix ha ho qd src off f7 H hd hj (by
      intro k kj kv
      have same : k=i := by
        by_contra noti
        exact (not_le_of_gt kj) (B.min'_le k (Finset.mem_erase.mpr ⟨noti,kv⟩))
      simp [H,same])
    rw [formalPrimitive_eq_native,show R*(X*(X-C (nodes A i))*L)=H*q by
      dsimp [H];rw [eq];ring]
    exact test

/-- The five-site weak chart produces the full, actual `WeakFivePaidMask`.
The native compensation is done on the original blind coordinates and
may alter only the true terminal coordinate in addition. -/
theorem actual_weak_five_paid_mask [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (H : Width24WeakFiveChart A b w Q P) :
    ∃ (q : K[X]) (θ : Fin 24 → K), WeakFivePaidMask A b q Q P θ ∧ q≠0 ∧
      ∀ i∈weakFiveRows A b Q P, θ i=q.eval (nodes A i) ∧ θ i≠0 := by
  classical
  let : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let G := Hidden.blindRows c b d 0 t
  let T := Hidden.activeRows d
  let V := weakFiveRows A b Q P
  have dt : d t=0 := (width24_quadratic_cover ha ho).lastSeed
  have F := width24_paid_frame ha ho
  have yt : y t=0 := by change (1:K)-nodes A (Fin.last 23)=0;rw [F.lastClock,sub_self]
  have gRank : G.card=3 := (Hidden.carrier_rank F.lastLive.live).symm.trans H.carrierRank
  have notT : t∉T := fun h=>(Hidden.mem_activeRows _).mp h dt
  have notG : t∉G := fun h=>((Hidden.mem_blindRows _).mp h).2.1 rfl
  have notV : t∉V := fun h=>(H.contrast_data h).2.1 yt
  have GT : Disjoint G T := Finset.disjoint_left.mpr fun i gi ti=>
    (Hidden.mem_activeRows _).mp ti ((Hidden.mem_blindRows _).mp gi).2.2.1
  have GV : Disjoint G V := Finset.disjoint_left.mpr fun i gi vi=>
    (mul_ne_zero (H.contrast_data vi).2.1 (H.contrast_data vi).2.2.1)
      ((Hidden.mem_blindRows _).mp gi).2.2.2
  have TV : Disjoint T V := Finset.disjoint_left.mpr fun i ti vi=>
    (Hidden.mem_activeRows _).mp ti (H.contrast_data vi).1
  have unV : Disjoint (G∪T) V := Finset.disjoint_union_left.mpr ⟨GV,TV⟩
  have nt : t∉(G∪T)∪V := by simpa only [Finset.mem_union,not_or] using ⟨⟨notG,notT⟩,notV⟩
  have count : (insert t ((G∪T)∪V)).card=24 ↔ G.card+T.card+V.card+1=24 := by
    rw [Finset.card_insert_of_notMem nt,Finset.card_union_of_disjoint unV,Finset.card_union_of_disjoint GT]
  have lowT : 15≤T.card := H.seedSites.trans (Finset.card_image_le (f:=y) (s:=T))
  have lowV : 5≤V.card := H.contrastSites.trans (Finset.card_image_le (f:=y) (s:=V))
  have upl := Finset.card_le_univ (insert t ((G∪T)∪V))
  rw [Fintype.card_fin,Finset.card_insert_of_notMem nt,Finset.card_union_of_disjoint unV,
    Finset.card_union_of_disjoint GT] at upl
  have nV : V.card=5 := by omega
  have full : insert t ((G∪T)∪V)=Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by change 24≤_; rw [count.mpr (by omega)])
  have ysimple : Set.InjOn y (V : Set (Fin 24)) := Finset.card_image_iff.mp
    (le_antisymm Finset.card_image_le (by rw [nV];exact H.contrastSites))
  have simple : Set.InjOn c (V : Set (Fin 24)) := by
    intro i hi j hj h
    apply ysimple hi hj
    change 1-c i=1-c j
    rw [h]
  let q := Q.comp (1-X)
  have affine : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  have qd : q.natDegree≤4 := natDegree_comp_le.trans
    (by simpa only [mul_one] using Nat.mul_le_mul H.qDegree affine)
  have reflect (x : K) : q.eval x=Q.eval (1-x) := by simp [q,eval_comp]
  have live (i : Fin 24) (hi : i∈V) : q.eval (c i)≠0 := by
    rw [reflect]
    exact (H.contrast_data hi).2.2.2.1
  have neV : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := neV
  have qn : q≠0 := fun e=>live i hi (by rw [e,eval_zero])
  obtain ⟨g,hg,gval⟩ := Hidden.carrier_filler (f:=evalNodes A q-w) F.lastLive.live
  let θ := evalNodes A q-(w+g)
  have src : ∃ x∈zeroSpace A 4, θ=evalNodes A q-x :=
    ⟨w+g,(zeroSpace A 4).add_mem H.headGrade (H.carrierGrade hg),rfl⟩
  have off (i : Fin 24) (ni : i∉V) (it : i≠t) : θ i=0 := by
    have all : i∈insert t ((G∪T)∪V) := by rw [full];exact Finset.mem_univ _
    have gOrT : i∈G∪T := ((Finset.mem_union.mp
      ((Finset.mem_insert.mp all).resolve_left it)).resolve_right ni)
    rcases Finset.mem_union.mp gOrT with ig|id
    · have h := gval i ig
      change g i=q.eval (c i)-w i at h
      change q.eval (c i)-(w i+g i)=0
      rw [h]
      ring
    · have pd := (Hidden.mem_activeRows i).mp id
      have he := H.qFit i
      rw [mul_comm (Q.eval (y i))] at he
      have wi : w i=Q.eval (y i) := mul_left_cancel₀ pd he
      have gi := Hidden.carrier_zero_on_active dt hg pd
      change q.eval (c i)-(w i+g i)=0
      rw [gi,add_zero,wi,reflect]
      change Q.eval (1-c i)-Q.eval (1-c i)=0
      rw [sub_self]
  have f7 := H.seventh_zero F.lastClock
  have sourceOrigin := weak_five_origin_of_source ha ho qd src off f7 live nV simple
  have value (i : Fin 24) (vi : i∈V) : θ i=q.eval (c i) ∧ θ i≠0 := by
    obtain ⟨_,yi,bi,_,wi⟩ := H.contrast_data vi
    have gi : g i=0 := (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero F.lastClock hg i)).resolve_left
      (mul_ne_zero yi bi)
    have e : θ i=q.eval (c i) := by
      change q.eval (c i)-(w i+g i)=q.eval (c i)
      rw [wi,gi,add_zero,sub_zero]
    exact ⟨e, e ▸ live i vi⟩
  exact ⟨q,θ,⟨qd,H.qDegree,H.pDegree,reflect,src,off,f7,⟨w,H.qFit,H.pFit⟩,simple,nV,sourceOrigin⟩,
    qn,value⟩

theorem width24_weak_five_ports_of_chart [LinearOrder K] [IsStrictOrderedRing K]
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (H : Width24WeakFiveChart A b w Q P) :
    ∃ (q : K[X]) (ι : Fin 5 → Fin 24) (Z : K[X]), q≠0 ∧ WeakFiveInnerPorts A b q Q P Z ι := by
  obtain ⟨q,θ,M,qn,_⟩ := actual_weak_five_paid_mask ha ho H
  obtain ⟨ι,Z,B⟩ := width24_weak_five_true_inner_ports ha ho M
  exact ⟨q,ι,Z,qn,B⟩

end
end RKResearch.Certified.ERK16
