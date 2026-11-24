module
public import RKCert.ReviewedNative.ERK19ZeroOriginSplit
public import RKCert.ReviewedNative.ERK19ZeroScalarInput
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.Thin
open Graded.Reverse.Hidden Graded.NativeMoments RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.ERK19ZeroScalar
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b h θ : Fin 29 → K}
variable {Q E P : K[X]} {spare : Finset (Fin 29)}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem opposed_origin_zero (ha : ∀ i j, i≤j → A i j=0) : nodes A 0=0 := by
  change (∑ j,A 0 j*(1:K))=0
  exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le j),zero_mul]

structure OpposedPhysicalRows (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (Q E : K[X]) (r : Fin 4 ↪o Fin 29) (e : ℕ) : Prop where
  live : ∀ k, reverseContrast A b Q E (r k)≠0
  cover : ∀ i, reverseContrast A b Q E i≠0 → i≠0 → ∃ k, r k=i
  distinct : Function.Injective (fun k=>nodes A (r k))
  nonzero : ∀ k, nodes A (r k)≠0
  originBit : e≤1
  originLive : reverseContrast A b Q E 0≠0 → e=1

set_option maxHeartbeats 900000 in
theorem width29_opposed_physical_rows (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (H : Width29ZeroHead A b h Q E) (O : Width29OriginSplit A b Q E P spare) :
    ∃ r e, OpposedPhysicalRows A b Q E r e := by
  classical
  let W := reverseContrast A b Q E
  let y := reflectedClock A
  let S := activeRows W
  let T := S.erase 0
  let e : ℕ := if W 0=0 then 0 else 1
  have img : S.image y=zeroContrastSites A b Q E := by
    ext x
    simp only [Finset.mem_image, mem_activeRows, mem_weightedSites, S, W, y, zeroContrastSites]
  have sites : (S.image y).card=S.card := by
    rw [img]
    rcases O.layout with ⟨_,_,_,sr,sc⟩|⟨_,_,_,sr,sc⟩
    · exact sc.trans sr.symm
    · exact sc.trans sr.symm
  have inj : Set.InjOn y (S : Set (Fin 29)) := Finset.card_image_iff.mp sites
  have cardT : T.card=4 := by
    change (S.erase 0).card=4
    rcases O.layout with ⟨_,live,_,sr,_⟩|⟨_,dead,_,sr,_⟩
    · have i0 : (0:Fin 29)∈S := (mem_activeRows 0).mpr live
      rw [Finset.card_erase_of_mem i0,sr]
    · have i0 : (0:Fin 29)∉S := fun p=>((mem_activeRows 0).mp p) dead
      rw [Finset.erase_eq_of_notMem i0,sr]
  let r := T.orderEmbOfFin cardT
  have inT (k : Fin 4) : r k∈T := T.orderEmbOfFin_mem cardT k
  have inS (k : Fin 4) : r k∈S := (Finset.mem_erase.mp (inT k)).2
  have live (k : Fin 4) : W (r k)≠0 := (mem_activeRows _).mp (inS k)
  have off0 (k : Fin 4) : r k≠0 := (Finset.mem_erase.mp (inT k)).1
  have allRows (i : Fin 29) (wi : W i≠0) (i0 : i≠0) : ∃ k,r k=i := by
    change i∈Set.range (T.orderEmbOfFin cardT)
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_erase.mpr ⟨i0,(mem_activeRows i).mpr wi⟩
  have y0 : y 0=1 := by change 1-nodes A 0=1; rw [opposed_origin_zero ha,sub_zero]
  have zInj : Function.Injective (fun k : Fin 4=>nodes A (r k)) := by
    intro j k eq
    apply r.injective
    exact inj (inS j) (inS k) (congrArg (fun v : K=>1-v) eq)
  have zNonzero (k : Fin 4) : nodes A (r k)≠0 := by
    intro z
    have yi : y (r k)=1 := by change 1-nodes A (r k)=1; rw [z,sub_zero]
    by_cases w0 : W 0=0
    · have four : (zeroContrastSites A b Q E).card=4 := by
        rcases O.layout with ⟨_,w,_,_,_⟩|⟨_,_,_,_,c⟩
        · exact (w w0).elim
        · exact c
      have qn : Q≠0 := by intro n; have d:=H.quintic; simp [n] at d
      have d : Q.natDegree+(zeroContrastSites A b Q E).card≤9 := by
        rw [H.quintic,four]
      have none := x_nodal_paid_moments_exclude_one (n:=9) qn d (H.four_site_orthogonal ho four).2
      exact none (mem_weightedSites.mpr ⟨r k,live k,yi⟩)
    · exact off0 k (inj (inS k) ((mem_activeRows 0).mpr w0) (yi.trans y0.symm))
  exact ⟨r,e,⟨live,allRows,zInj,zNonzero,
    by by_cases w : W 0=0 <;> simp [e,w],fun wi=>by
      change W 0 ≠ 0 at wi
      simp [e,wi]⟩⟩

private theorem opposed_left_port (ha : ∀ i j,i≤j→A i j=0)
    (F : Width29ForwardPorts A b θ Q E P spare) {i : Fin 29}
    (wi : reverseContrast A b Q E i≠0) (T : K[X]) (dT : T.natDegree≤3)
    (at0 : T.eval 0=0)
    (earlier : ∀ j : Fin 29, j < i → j ≠ 0 → reverseContrast A b Q E j≠0 → T.eval (nodes A j)=0) :
    integral 0 (nodes A i) (T*P)=0 := by
  have halt : mat A (weightedEval (nodes A) θ T) i=0 := by
    apply causal_mat ha
    intro j hj
    change j < i at hj
    rw [weightedEval_apply]
    by_cases j0 : j=0
    · rw [j0,opposed_origin_zero ha,at0,zero_mul]
    · by_cases live : reverseContrast A b Q E j≠0
      · rw [earlier j hj j0 live,zero_mul]
      · have away := F.supportAway j (not_not.mp live)
          (ne_of_lt (hj.trans_le (Fin.le_last i))) j0
        rw [away,mul_zero]
  rw [integral_zero_left,formalPrimitive_eq_native]
  exact (F.port i wi T dT).symm.trans halt

private theorem opposed_right_port
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (H : Width29ZeroHead A b h Q E) (F : Width29ForwardPorts A b θ Q E P spare)
    (Z : Width29ZeroCover A b) {i : Fin 29} (wi : reverseContrast A b Q E i≠0)
    (T : K[X]) (dT : T.natDegree≤2)
    (later : ∀ j, i<j → reverseContrast A b Q E j≠0 → T.eval (nodes A j)=0) :
    integral (nodes A i) 1 ((1-X)*P*T)=0 := by
  let R : K[X] := T.comp (1-X)
  have dR : R.natDegree≤2 := natDegree_comp_le.trans (by
    rw [one_sub_X_natDegree,mul_one]
    exact dT)
  have e := H.port_of_later_mask ha ho Z wi R dR (by
    intro j hj
    by_cases live : reverseContrast A b Q E j≠0
    · have flip : 1-reflectedClock A j=nodes A j := by
        change 1-(1-nodes A j)=nodes A j
        ring
      change (T.comp (1-X)).eval (reflectedClock A j)*reverseContrast A b Q E j=0
      rw [eval_comp,eval_sub,eval_one,eval_X,flip,later j hj live,zero_mul]
    · rw [not_not.mp live,mul_zero])
  have invol : ((1-X : K[X]).comp (1-X))=X := by simp
  have back : P.comp (1-X)=Q := by rw [F.reflected,comp_assoc,invol,comp_X]
  have poly : (((1-X)*P*T).comp (1-X))=R*(X*Q) := by
    rw [mul_comp,mul_comp,invol,back]
    change (X*Q)*R=R*(X*Q)
    exact mul_comm _ _
  rw [←integral_reflect ((1-X)*P*T) (nodes A i),poly,integral_zero_left,
    formalPrimitive_eq_native]
  exact e

private theorem opposed_global_port (F : Width29ForwardPorts A b θ Q E P spare)
    (T : K[X]) (dT : T.natDegree≤12)
    (kills : ∀ j, reverseContrast A b Q E j≠0 → T.eval (nodes A j)=0) :
    integral 0 1 (T*((1-X)*P))=0 := by
  rw [integral_zero_left,formalPrimitive_eq_native,F.moments T dT]
  apply Finset.sum_eq_zero
  intro j _
  by_cases live : reverseContrast A b Q E j≠0
  · rw [kills j live,zero_mul]
  · rw [not_not.mp live,mul_zero]

set_option maxHeartbeats 1300000 in
theorem width29_zero_geometry_to_opposed_windows
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (H : Width29ZeroHead A b h Q E) (F : Width29ForwardPorts A b θ Q E P spare)
    (O : Width29OriginSplit A b Q E P spare) (Z : Width29ZeroCover A b) :
    ∃ z e, OpposedQuinticWindows P z e := by
  obtain ⟨r,e,B⟩ := width29_opposed_physical_rows ha ho H O
  let z (k : Fin 4) := nodes A (r k)
  have active (k : Fin 4) : z k≠0 ∧ z k≠1 ∧ P.eval (z k)≠0 := by
    have w := H.active (B.live k)
    refine ⟨B.nonzero k,?_,?_⟩
    · intro c
      apply w.2.1
      change 1-nodes A (r k)=0
      change nodes A (r k)=1 at c
      rw [c,sub_self]
    · change P.eval (nodes A (r k))≠0
      rw [F.reflected,eval_comp,eval_sub,eval_one,eval_X]
      exact w.2.2.2.1
  have before {j : Fin 29} {k : Fin 4} (hj : j<r k) (j0 : j≠0)
      (wj : reverseContrast A b Q E j≠0) : ∃ l : Fin 4, l<k ∧ r l=j := by
    obtain ⟨l,rfl⟩ := B.cover j wj j0
    exact ⟨l,r.lt_iff_lt.mp hj,rfl⟩
  have after {j : Fin 29} {k : Fin 4} (hj : r k<j)
      (wj : reverseContrast A b Q E j≠0) : ∃ l : Fin 4, k<l ∧ r l=j := by
    have j0 : j≠0 := ne_of_gt ((Fin.zero_le (r k)).trans_lt hj)
    obtain ⟨l,rfl⟩ := B.cover j wj j0
    exact ⟨l,r.lt_iff_lt.mp hj,rfl⟩
  have xDeg : (X : K[X]).natDegree≤1 := natDegree_X.le
  have lin (x : K) : (X-C x : K[X]).natDegree≤1 := (natDegree_X_sub_C x).le
  refine ⟨z,e,⟨F.quintic,B.originBit,B.distinct,active,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro k
    let T : K[X] := X*X^k.val
    have kd : (X^k.val : K[X]).natDegree≤2 := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    have d : T.natDegree≤3 := natDegree_mul_le_of_le xDeg kd
    have m := opposed_left_port ha F (B.live 0) T d (by simp [T]) (by
      intro j hj j0 wj
      obtain ⟨l,hl,rfl⟩ := before hj j0 wj
      change l.val<0 at hl
      omega)
    rw [show (X:K[X])*P*X^k.val=T*P by dsimp only [T]; ac_rfl]
    exact m
  · intro k
    let T : K[X] := X*(X-C (z 0))*X^k.val
    have kd : (X^k.val : K[X]).natDegree≤1 := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    have d : T.natDegree≤3 := natDegree_mul_le_of_le (natDegree_mul_le_of_le xDeg (lin _)) kd
    have m := opposed_left_port ha F (B.live 1) T d (by simp [T]) (by
      intro j hj j0 wj
      obtain ⟨l,hl,rfl⟩ := before hj j0 wj
      have l0 : l=0 := Fin.ext (by change l.val<1 at hl; change l.val=0; omega)
      rw [l0]
      simp [T,z])
    rw [show (X:K[X])*(X-C (z 0))*P*X^k.val=T*P by dsimp only [T]; ac_rfl]
    exact m
  · let T : K[X] := X*(X-C (z 0))*(X-C (z 1))
    have d : T.natDegree≤3 := natDegree_mul_le_of_le (natDegree_mul_le_of_le xDeg (lin _)) (lin _)
    exact opposed_left_port ha F (B.live 2) T d (by simp [T]) (by
      intro j hj j0 wj
      obtain ⟨l,hl,rfl⟩ := before hj j0 wj
      change l.val<2 at hl
      have alt : l=0 ∨ l=1 := by
        by_cases z0 : l.val=0
        · exact Or.inl (Fin.ext z0)
        · exact Or.inr (Fin.ext (by change l.val=1; omega))
      rcases alt with z0|z1
      · rw [z0]; simp [T,z]
      · rw [z1]; simp [T,z])
  · intro k
    have d : (X^k.val : K[X]).natDegree≤2 := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    exact opposed_right_port ha ho H F Z (B.live 3) (X^k.val) d (by
      intro j hj wj
      obtain ⟨l,hl,rfl⟩ := after hj wj
      change 3<l.val at hl
      have lc := l.isLt
      omega)
  · intro k
    let T : K[X] := (X-C (z 3))*X^k.val
    have kd : (X^k.val : K[X]).natDegree≤1 := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    have d : T.natDegree≤2 := natDegree_mul_le_of_le (lin _) kd
    have m := opposed_right_port ha ho H F Z (B.live 2) T d (by
      intro j hj wj
      obtain ⟨l,hl,rfl⟩ := after hj wj
      have lc := l.isLt
      have l3 : l=3 := Fin.ext (by change 2<l.val at hl; change l.val=3; omega)
      rw [l3]
      simp [T,z])
    rw [show ((1-X):K[X])*(X-C (z 3))*P*X^k.val=(1-X)*P*T by dsimp only [T]; ac_rfl]
    exact m
  · let T : K[X] := (X-C (z 3))*(X-C (z 2))
    have d : T.natDegree≤2 := natDegree_mul_le_of_le (lin _) (lin _)
    have m := opposed_right_port ha ho H F Z (B.live 1) T d (by
      intro j hj wj
      obtain ⟨l,hl,rfl⟩ := after hj wj
      change 1<l.val at hl
      have lc := l.isLt
      have alt : l=2 ∨ l=3 := by
        by_cases z2 : l.val=2
        · exact Or.inl (Fin.ext z2)
        · exact Or.inr (Fin.ext (by change l.val=3; omega))
      rcases alt with z2|z3
      · rw [z2]; simp [T,z]
      · rw [z3]; simp [T,z])
    rw [show ((1-X):K[X])*(X-C (z 3))*(X-C (z 2))*P=(1-X)*P*T by
      dsimp only [T]; ac_rfl]
    exact m
  · intro k
    let N := opposedNodalProduct z
    let T : K[X] := X^e*N*X^k.val
    have dN : N.natDegree≤4 := by
      change (opposedNodalProduct z).natDegree≤4
      unfold opposedNodalProduct
      exact natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (natDegree_mul_le_of_le (lin _) (lin _)) (lin _)) (lin _)
    have root (i : Fin 4) : N.eval (z i)=0 := by fin_cases i <;> simp [N,opposedNodalProduct]
    have de : (X^e : K[X]).natDegree≤e := by rw [natDegree_X_pow]
    have dk : (X^k.val : K[X]).natDegree≤k.val := by rw [natDegree_X_pow]
    have dT : T.natDegree≤12 := (natDegree_mul_le_of_le (natDegree_mul_le_of_le de dN) dk).trans
      (by have h := k.isLt; have bnd := B.originBit; omega)
    have m := opposed_global_port F T dT (by
      intro j wj
      by_cases j0 : j=0
      · have w0 : reverseContrast A b Q E 0≠0 := by simpa only [j0] using wj
        simp [T,j0,opposed_origin_zero ha,B.originLive w0]
      · obtain ⟨l,rfl⟩ := B.cover j wj j0
        change T.eval (z l)=0
        simp [T,root l])
    rw [show ((1-X):K[X])*X^e*(P*opposedNodalProduct z)*X^k.val=T*((1-X)*P) by
      dsimp only [T,N]; ac_rfl]
    exact m

theorem width29_zero_opposed_windows (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 19 A b) (zero : firstSeed A b=0) :
    ∃ (P : K[X]) (z : Fin 4 → K) (e : ℕ), OpposedQuinticWindows P z e := by
  obtain ⟨_,_,_,_,_,_,_,P,_,H,_,F,O⟩ := width29_zero_origin_split ha ho zero
  obtain ⟨z,e,p⟩ := width29_zero_geometry_to_opposed_windows ha ho H F O
    (width29_zero_cover_data ha ho zero)
  exact ⟨P,z,e,p⟩

theorem width29_zero_first_seed_impossible_of_scalar
    (scalar : ∀ (P : K[X]) (z : Fin 4→K) (e : ℕ), OpposedQuinticWindows P z e → False)
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b) (zero : firstSeed A b=0) : False := by
  obtain ⟨P,z,e,M⟩ := width29_zero_opposed_windows ha ho zero
  exact scalar P z e M

end
end RKResearch.Certified.ERK19
