module

public import RKCert.ERKOrderNineFiveSixFirstPlacement
public import RKCert.ERKLowMomentCollision

@[expose] public section

/-! # Actual eighth-clean terminal Hankel obstruction -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}

noncomputable def fiveSixCollisionPoly (P : K[X]) (h : K) : K[X] := -(X*(X-C h)*P)

noncomputable def fiveSixCollisionVector (A : Fin s→Fin s→K) (P : K[X]) (h : K) : Vec K s :=
  fun i=>nodes A i*(nodes A i-h)*(qdef A i-P.eval (nodes A i))

theorem fiveSixCollision_profile [CharZero K] {A : Fin s→Fin s→K} (P : K[X]) (dP : P.natDegree≤2) (h : K) :
    let R := fiveSixCollisionPoly P h
    let f := fiveSixCollisionVector A P h
    R.natDegree≤4 ∧ f-evalNodes A R∈zeroSpace A 4 ∧ f∈treeSpace A 4 := by
  dsimp only
  let R := fiveSixCollisionPoly P h
  let f := fiveSixCollisionVector A P h
  let U : K[X] := X*(X-C h)
  have dU : U.natDegree≤2 := by
    have e1 : (X : K[X]).natDegree≤1 := by simp
    have e2 : (X-C h).natDegree≤1 := by simp
    exact natDegree_mul_le_of_le e1 e2
  have dR : R.natDegree≤4 := by
    change (-(U*P)).natDegree≤4
    rw [natDegree_neg]
    exact natDegree_mul_le_of_le dU dP
  have e : f-evalNodes A R=diag (qdef A) (evalNodes A U) := by
    ext i
    change nodes A i*(nodes A i-h)*(qdef A i-P.eval (nodes A i))-R.eval (nodes A i)=
      qdef A i*U.eval (nodes A i)
    simp [R,U,fiveSixCollisionPoly]
    ring
  have g : f-evalNodes A R∈zeroSpace A 4 := by
    rw [e]
    exact chainSpan_le_zeroSpace (qdef_mem A) 2 (chainSpan_iff_polynomial.mpr ⟨U,dU,rfl⟩)
  exact ⟨dR,g,by
    have z := (treeSpace A 4).add_mem (zeroSpace_le_treeSpace A 4 g) (evalNodes_mem_treeSpace A R dR)
    rwa [sub_add_cancel] at z⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

set_option maxHeartbeats 1400000 in
/-- Both exact operator identities are in the full physical vector
space. In particular the repeated stage is not deleted or reweighted. -/
theorem order9_actual_five_six_on_eighth_two_step
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (fg : ActualSixOnFG A P) (on : qdef A (lowPrefix10 (7:Fin 10))=0) :
    let h := nodes A (lowPrefix10 fg.first)
    let r := nodes A (lowPrefix10 fg.middle)
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let f := fiveSixCollisionVector A P h
    let w := diag (nodes A) f-r • f
    let e : Vec K 12 := Pi.single (Fin.last 11) 1
    ∃ κ lam t t' : K, mat A f=κ • w+t • e ∧
      mat A w=lam • (diag (nodes A) w-u • w)+t' • e := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  dsimp only
  let c := nodes A∘lowPrefix10
  let g := qdef A∘lowPrefix10
  let h := c fg.first
  let r := c fg.middle
  let u := c 8
  let v := c (Fin.last 9)
  let f := fiveSixCollisionVector A P h
  let w := diag (nodes A) f-r • f
  let y := diag (nodes A) w-u • w
  let E : Vec K 12 := Pi.single (Fin.last 11) 1
  obtain ⟨e5,e6,_,hEndOn,hEnd,_,uniq⟩ := order9_five_six_stage_chart ha ho N M fit
  have e5s : treeSpace A 5≤onOffSpace A := e5 ▸ gradeFive_profiles_state_valued fit
  obtain ⟨bij,⟨i,hi,hs,a,_,ra⟩,hWOn,_⟩ := order9_five_six_ten_distinct_prefix ha ho N M
  change Function.Bijective (fun i : Fin 10=>lowNonterminalStateAt ha (lowPrefix10 i)) at bij
  have only (i : Fin 10) (di : g i=0) : c i≠1 :=
    first_prefix_clean_value_ne_one uniq i di
  have eqOn {i j : Fin 10} (di : g i=0) (dj : g j=0) (x:c i=c j) : i=j :=
    bij.1 ((lowNonterminalState_eq_iff ha (only i) (only j)).mpr
      (lowState_eq_iff.mpr ⟨by change (g i=0 ↔ g j=0); rw [di,dj],x⟩))
  let W : Fin 4→K := ![h,r,u,v]
  have wi : Function.Injective W := fg.root_set_injective
  have hr : h≠r := fun e=>(by decide : (0:Fin 4)≠1) (wi e)
  have hu : h≠u := fun e=>(by decide : (0:Fin 4)≠2) (wi e)
  have hv : h≠v := fun e=>(by decide : (0:Fin 4)≠3) (wi e)
  have ru : r≠u := fun e=>(by decide : (1:Fin 4)≠2) (wi e)
  have rv : r≠v := fun e=>(by decide : (1:Fin 4)≠3) (wi e)
  have uv : u≠v := fun e=>(by decide : (2:Fin 4)≠3) (wi e)
  have h0 : h≠0 := fg.first_nonzero
  have r0 : r≠0 := fg.middle_nonzero
  have u0 : u≠0 := fg.late_u_nonzero
  have v0 : v≠0 := fg.late_v_nonzero
  have hd : g fg.first=0 := fg.first_clean
  have rd : g fg.middle=0 := fg.middle_clean
  have ud : g 8=0 := fg.late_u_clean
  have vd : g (Fin.last 9)=0 := fg.late_v_clean
  have h1 : h≠1 := only _ hd
  have r1 : r≠1 := only _ rd
  have u1 : u≠1 := only _ ud
  have v1 : v≠1 := only _ vd
  have hsOn : (onNodes A)={0,1,h,r,u,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      · exact zero_mem_onNodes ha
      · exact mem_onNodes.mpr ⟨_,hEndOn,hEnd⟩
      · exact mem_onNodes.mpr ⟨_,hd,rfl⟩
      · exact mem_onNodes.mpr ⟨_,rd,rfl⟩
      · exact mem_onNodes.mpr ⟨_,ud,rfl⟩
      · exact mem_onNodes.mpr ⟨_,vd,rfl⟩
    · have z0 : (0:K)∉({1,h,r,u,v}:Finset K) := by
        simp [Ne.symm h0,Ne.symm r0,Ne.symm u0,Ne.symm v0]
      have z1 : (1:K)∉({h,r,u,v}:Finset K) := by
        simp [Ne.symm h1,Ne.symm r1,Ne.symm u1,Ne.symm v1]
      have zh : h∉({r,u,v}:Finset K) := by simp [hr,hu,hv]
      have zr : r∉({u,v}:Finset K) := by simp [ru,rv]
      rw [M,Finset.card_insert_of_notMem z0,Finset.card_insert_of_notMem z1,
        Finset.card_insert_of_notMem zh,Finset.card_insert_of_notMem zr,Finset.card_pair uv]
  have fvOn (j : Fin 10) (dj : g j=0) :
      f (lowPrefix10 j)=-(c j*(c j-h)*P.eval (c j)) := by
    change c j*(c j-h)*(g j-P.eval (c j))=_
    rw [dj]
    ring
  have fv0 (j : Fin 10) (nr : j≠fg.middle) (nu : j≠8) (nv : j≠Fin.last 9) :
      f (lowPrefix10 j)=0 := by
    by_cases nj : g j=0
    · have e : c j∈onNodes A := mem_onNodes.mpr ⟨_,nj,rfl⟩
      rw [hsOn] at e
      simp only [Finset.mem_insert,Finset.mem_singleton] at e
      rcases e with e|e|e|e|e|e
      · rw [fvOn j nj,e,zero_mul,zero_mul,neg_zero]
      · exact (only j nj e).elim
      · rw [fvOn j nj,e,sub_self,mul_zero,zero_mul,neg_zero]
      · exact (nr (eqOn nj rd e)).elim
      · exact (nu (eqOn nj ud e)).elim
      · exact (nv (eqOn nj vd e)).elim
    · have e : P.eval (c j)=g j := fit _ nj
      change c j*(c j-h)*(g j-P.eval (c j))=0
      rw [e,sub_self,mul_zero]
  have wv0 (j : Fin 10) (nu : j≠8) (nv : j≠Fin.last 9) : w (lowPrefix10 j)=0 := by
    change c j*f (lowPrefix10 j)-r*f (lowPrefix10 j)=0
    by_cases e : j=fg.middle
    · subst j
      change r*f _-r*f _=0
      exact sub_self _
    · rw [fv0 j e nu nv,mul_zero,mul_zero,sub_self]
  have fo (j : Fin 10) (pre : j≤fg.middle) : mat A f (lowPrefix10 j)=0 := by
    apply causal_mat ha
    intro k hk
    have hk' : k.val<j.val := hk
    let l : Fin 10 := ⟨k.val,hk'.trans j.isLt⟩
    have e : lowPrefix10 l=k := Fin.ext rfl
    rw [←e]
    have lr : l<fg.middle := (show l<j from hk).trans_le pre
    exact fv0 l (ne_of_lt lr) (ne_of_lt (lr.trans fg.middle_lt_late))
      (ne_of_lt ((lr.trans fg.middle_lt_late).trans (by decide)))
  have wo (j : Fin 10) (pre : j≤8) : mat A w (lowPrefix10 j)=0 := by
    apply causal_mat ha
    intro k hk
    have hk' : k.val<j.val := hk
    let l : Fin 10 := ⟨k.val,hk'.trans j.isLt⟩
    have e : lowPrefix10 l=k := Fin.ext rfl
    rw [←e]
    have lu : l<(8:Fin 10) := (show l<j from hk).trans_le pre
    exact wv0 l (ne_of_lt lu) (ne_of_lt (lu.trans (by decide)))
  have f4 := (fiveSixCollision_profile (A:=A) P dP h).2.2
  have w5 : w∈treeSpace A 5 := (treeSpace A 5).sub_mem (diag_treeSpace A 4 f4)
    ((treeSpace A 5).smul_mem _ (treeSpace_mono A (by decide) f4))
  have y6 : y∈treeSpace A 6 := (treeSpace A 6).sub_mem (diag_treeSpace A 5 w5)
    ((treeSpace A 6).smul_mem _ (treeSpace_mono A (by decide) w5))
  have tail (q : Vec K 12) (qs : q∈onOffSpace A) (q0 : ∀ i : Fin 10,q (lowPrefix10 i)=0) :
      q=q (Fin.last 11) • E := by
    have qi : q i=0 := by
      let i' : Fin 10 := ⟨i.val,hi⟩
      have e : lowPrefix10 i'=i := Fin.ext rfl
      simpa only [e] using q0 i'
    ext j
    by_cases j11 : j=Fin.last 11
    · subst j
      simp [E]
    · have j0 : q j=0 := by
        by_cases j10 : j=(10:Fin 12)
        · rw [j10]
          exact (onOffSpace_eq_at_states hs qs).symm.trans qi
        · have n10 : j.val≠10 := fun e=>j10 (Fin.ext e)
          have n11 : j.val≠11 := fun e=>j11 (Fin.ext e)
          let j' : Fin 10 := ⟨j.val,by have:=j.isLt; omega⟩
          have e : lowPrefix10 j'=j := Fin.ext rfl
          simpa only [e] using q0 j'
      change q j=q (Fin.last 11)*E j
      rw [j0]
      have ez : E j=0 := by
        change (Pi.single (Fin.last 11) (1:K):Vec K 12) j=0
        have jn : j≠(11:Fin 12) := j11
        simp [jn]
      rw [ez,mul_zero]
  let aRow := transMat A (orderAdjoint A b 1)
  have aq : aRow∈annih (treeSpace A 5) := transMat_mem_annih_pred (orderAdjoint_annih ho (by decide))
  have cut (j : Fin 12) (hj : (10:Fin 12)≤j) : aRow j=0 := by
    change transMat A (orderAdjoint A b 1) j=0
    rw [ra,map_smul,map_sub,transMat_single_incoming_row,transMat_single_incoming_row,
      Pi.smul_apply,Pi.sub_apply,ha i j (hi.le.trans hj),ha 10 j hj,sub_self,smul_zero]
  have av : aRow (lowPrefix10 (Fin.last 9))≠0 := by
    have e : onWeight A aRow v=aRow (lowPrefix10 (Fin.last 9)) := by
      unfold onWeight
      rw [Finset.sum_eq_single (lowPrefix10 (Fin.last 9))]
      · have e : qdef A (lowPrefix10 (Fin.last 9))=0 ∧ nodes A (lowPrefix10 (Fin.last 9))=v := ⟨vd,rfl⟩
        rw [ite_eq_left e]
      · intro j _ jn
        by_cases hj : j.val<10
        · let l : Fin 10 := ⟨j.val,hj⟩
          have e : lowPrefix10 l=j := Fin.ext rfl
          have ne : ¬ (qdef A j=0 ∧ nodes A j=v) := by
            intro hz
            have gd : g l=0 := by change qdef A (lowPrefix10 l)=0; rw [e]; exact hz.1
            have ce : c l=v := by change nodes A (lowPrefix10 l)=v; rw [e]; exact hz.2
            have jl : l=Fin.last 9 := eqOn gd vd ce
            exact jn (e.symm.trans (congrArg lowPrefix10 jl))
          simp [ne]
        · have ct := cut j (by exact Nat.le_of_not_gt hj)
          simp [ct]
      · simp
    rw [←e]
    exact hWOn v (Finset.mem_erase.mpr ⟨v1,mem_onNodes.mpr ⟨_,vd,rfl⟩⟩)
  obtain ⟨_,Pnz⟩ := order9_five_six_remainder ha ho N M hF P dP fit
  have nzf (j : Fin 10) (dj : g j=0) (j0 : c j≠0) (jh : c j≠h) : f (lowPrefix10 j)≠0 := by
    rw [fvOn _ dj]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero j0 (sub_ne_zero.mpr jh))
      (Pnz _ (Finset.mem_erase.mpr ⟨only j dj,mem_onNodes.mpr ⟨_,dj,rfl⟩⟩)))
  have nzw (j : Fin 10) (dj : g j=0) (j0 : c j≠0) (jh : c j≠h) (jr : c j≠r) :
      w (lowPrefix10 j)≠0 := by
    have eq : w (lowPrefix10 j)=(c j-r)*f (lowPrefix10 j) := by
      change c j*f (lowPrefix10 j)-r*f (lowPrefix10 j)=_
      ring
    rw [eq]
    exact mul_ne_zero (sub_ne_zero.mpr jr) (nzf j dj j0 jh)
  let κ := mat A f (lowPrefix10 8)/w (lowPrefix10 8)
  have kEq : κ*w (lowPrefix10 8)=mat A f (lowPrefix10 8) :=
    div_mul_cancel₀ _ (nzw _ ud u0 hu.symm ru.symm)
  let x := mat A f-κ • w
  have x5 : x∈treeSpace A 5 := (treeSpace A 5).sub_mem (mat_treeSpace A 4 f4)
    ((treeSpace A 5).smul_mem _ w5)
  have middle7 : fg.middle=(7:Fin 10) := by
    have cap:=fg.middle_lt_late
    by_contra ne
    have lt : fg.middle<(7:Fin 10) := by
      have n : fg.middle.val≠7 := fun e=>ne (Fin.ext e)
      change fg.middle.val<8 at cap
      change fg.middle.val<7
      omega
    exact fg.penultimate_max 7 lt (by decide) (by decide) on
  have x0 (j : Fin 10) (jv : j≠Fin.last 9) : x (lowPrefix10 j)=0 := by
    by_cases ju : j=(8:Fin 10)
    · subst j
      change mat A f (lowPrefix10 8)-κ*w (lowPrefix10 8)=0
      rw [kEq,sub_self]
    · have h : j≤fg.middle := by
        rw [middle7]
        have n : j.val≠8 := fun e=>ju (Fin.ext e)
        have nv : j.val≠9 := fun e=>jv (Fin.ext e)
        have := j.isLt
        change j.val≤7
        omega
      change mat A f (lowPrefix10 j)-κ*w (lowPrefix10 j)=0
      rw [fo j h,wv0 j ju jv,mul_zero,sub_self]
  have xv : x (lowPrefix10 (Fin.last 9))=0 := by
    have ex := mem_annih.mp aq _ x5
    rw [row_apply,Finset.sum_eq_single (lowPrefix10 (Fin.last 9))] at ex
    · exact (mul_eq_zero.mp ex).resolve_left av
    · intro j _ je
      by_cases h : j.val<10
      · let l : Fin 10 := ⟨j.val,h⟩
        have e : lowPrefix10 l=j := Fin.ext rfl
        have vv : l≠Fin.last 9 := fun hz=>je (e.symm.trans (congrArg lowPrefix10 hz))
        have w := x0 l vv
        rw [e] at w
        rw [w,mul_zero]
      · rw [cut j (by exact Nat.le_of_not_gt h),zero_mul]
    · simp
  have xE : x=x (Fin.last 11) • E := tail x (e5s x5) (fun j=>by
    by_cases h : j=Fin.last 9
    · simpa only [h] using xv
    · exact x0 j h)
  have nzY : y (lowPrefix10 (Fin.last 9))≠0 := by
    have e : y (lowPrefix10 (Fin.last 9))=(v-u)*w (lowPrefix10 (Fin.last 9)) := by
      change v*w (lowPrefix10 (Fin.last 9))-u*w (lowPrefix10 (Fin.last 9))=_
      ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.mpr uv.symm) (nzw _ vd v0 hv.symm rv.symm)
  let lam := mat A w (lowPrefix10 (Fin.last 9))/y (lowPrefix10 (Fin.last 9))
  let z := mat A w-lam • y
  have z6 : z∈treeSpace A 6 := (treeSpace A 6).sub_mem (mat_treeSpace A 5 w5)
    ((treeSpace A 6).smul_mem _ y6)
  have z0 (j : Fin 10) : z (lowPrefix10 j)=0 := by
    by_cases jv : j=Fin.last 9
    · subst j
      change mat A w (lowPrefix10 (Fin.last 9))-lam*y (lowPrefix10 (Fin.last 9))=0
      rw [show lam*y (lowPrefix10 (Fin.last 9))=mat A w _ from div_mul_cancel₀ _ nzY,sub_self]
    · have le : j≤(8:Fin 10) := by
        have t := j.isLt
        have n : j.val≠9 := fun e=>jv (Fin.ext e)
        change j.val≤8
        omega
      have vy : y (lowPrefix10 j)=0 := by
        change c j*w (lowPrefix10 j)-u*w (lowPrefix10 j)=0
        by_cases ju : j=(8:Fin 10)
        · subst j
          exact sub_self _
        · rw [wv0 j ju jv,mul_zero,mul_zero,sub_self]
      change mat A w (lowPrefix10 j)-lam*y (lowPrefix10 j)=0
      rw [wo j le,vy,mul_zero,sub_self]
  have zE : z=z (Fin.last 11) • E := tail z (e6 ▸ z6) z0
  exact ⟨κ,lam,x (Fin.last 11),z (Fin.last 11),by
    change mat A f=κ • w+x (Fin.last 11) • E
    rw [←xE]
    dsimp only [x]
    abel,by
    change mat A w=lam • y+z (Fin.last 11) • E
    rw [←zE]
    dsimp only [z]
    abel⟩

/-- The actual stage-eight-on branch forces the normalized polynomial
Hankel obstruction, at exactly the reflected moment budget of order nine. -/
theorem order9_actual_five_six_on_eighth_hankel
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (fg : ActualSixOnFG A P) (on : qdef A (lowPrefix10 (7:Fin 10))=0) :
    let R := fiveSixCollisionPoly P (nodes A (lowPrefix10 fg.first))
    let m (j : ℕ) := (primitive ((1-X)^j*R)).eval 1
    (m 2)*(m 4)-(m 3)^2=0 := by
  let h := nodes A (lowPrefix10 fg.first)
  let r := nodes A (lowPrefix10 fg.middle)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let R := fiveSixCollisionPoly P h
  let f := fiveSixCollisionVector A P h
  obtain ⟨_,_,_,_,hEnd,_,_⟩ := order9_five_six_stage_chart ha ho N M fit
  obtain ⟨κ,lam,t,t',fA,wA⟩ := order9_actual_five_six_on_eighth_two_step ha ho N M hF dP fit fg on
  have ur : u≠r := fun e=>(by decide : (2:Fin 4)≠1) (fg.root_set_injective e)
  obtain ⟨dR,paid,f4⟩ := fiveSixCollision_profile (A:=A) P dP h
  have hz := reflected_paid_two_step_collision ho f4 hEnd ur fA wA
  rw [reflected_unit_primitive_of_defect ho (k:=2) (by decide) R dR paid,
    reflected_unit_primitive_of_defect ho (k:=4) (by decide) R dR paid,
    reflected_unit_primitive_of_defect ho (k:=3) (by decide) R dR paid] at hz
  exact hz

end RKCert.Paired
