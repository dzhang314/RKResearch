module
public import RKCert.OrderTwelveGhostRankTwo
public import RKCert.ERKPhysicalContrasts
@[expose] public section

namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {i:Fin (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

/-- A physical off-head and off-mask row pays the primitive of its contrast.
The chronological row is the first nonzero one; no division by a zero or
repeated clock is used. This is attached to the exact grade-six chart. -/
theorem masked_primitive_zero (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hh:HeadData A 2 U w) (hU:MulClosed U) (hdis:∀ j,Live U j→w j=0)
    (hw4:w∈zeroSpace A 4) (P Q:K[X]) (hP:P≠0) (hQ:Q≠0)
    (degP:P.natDegree≤4) (degQ:Q.natDegree≤1)
    (profile:∀ j,w j≠0→w j=P.eval (nodes A j)) :
    ∃ k:Fin (s+1), ¬Live U k ∧ w k=0 ∧ (Q*P).eval (nodes A k)≠0 ∧
      (Paired.primitive (Q*P)).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,ee⟩:=core_indicator hU
  let c := nodes A
  let F := Q*P
  let v : Vec K (s+1) := w*evalNodes A Q+e*evalNodes A F
  let d := evalNodes A F-v
  have hv : v∈zeroSpace A 5 := by
    refine (zeroSpace A 5).add_mem ?_ ?_
    · apply zeroSpace_mono A (show 4+Q.natDegree≤5 by omega)
      exact zeroSpace_mul_treeSpace ho (by omega) hw4 (evalNodes_mem_treeSpace A Q le_rfl)
    · apply hh.low
      have h := poly_preserves hh.inv F e he
      have eq : e*evalNodes A F = (fun j => F.eval (nodes A j)*e j) := by
        ext j;exact mul_comm _ _
      rwa [eq]
  have dF : F.natDegree≤5 := natDegree_mul_le.trans (by omega)
  have dne : d≠0 := by
    intro h
    have hEq : evalNodes A F=v := sub_eq_zero.mp h
    have he0 := explicit_separated ha ho (q:=5) (by decide) (by omega) F dF (hEq ▸ hv)
    exact (mul_ne_zero hQ hP) he0
  let R := Finset.univ.filter (fun j=>d j≠0)
  have hR : R.Nonempty := by
    by_contra! e
    apply dne
    ext j
    by_contra hn
    exact (Finset.not_nonempty_iff_eq_empty.mpr e) ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let k := R.min' hR
  have hk : d k≠0 := (Finset.mem_filter.mp (R.min'_mem hR)).2
  have before (j:Fin (s+1)) (hj:j<k) : d j=0 := by
    by_contra h
    exact (not_le_of_gt hj) (R.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  have hko : ¬Live U k := by
    intro h
    apply hk
    simp [d,v,ee,h,hdis k h]
  have hwk : w k=0 := by
    by_contra h
    apply hk
    simp [d,v,ee,hko,profile k h,F,evalNodes,mul_comm]
  have Fk : F.eval (c k)≠0 := by
    intro h
    apply hk
    simp [d,v,ee,hko,hwk,evalNodes,c] at h ⊢
    exact h
  have hA : mat A d k=0 := by
    have h := strictlyCausal_mat ha k d 0 (fun j hj=>before j hj)
    simpa only [map_zero,Pi.zero_apply] using h
  let z := evalNodes A (Paired.primitive F)-mat A d
  have m1 : z∈zeroSpace A 6 := by
    unfold z d
    rw [map_sub]
    have e1 : evalNodes A (Paired.primitive F)-(mat A (evalNodes A F)-mat A v)=
        -(mat A (evalNodes A F)-evalNodes A (Paired.primitive F))+mat A v := by abel
    rw [e1]
    exact (zeroSpace A 6).add_mem ((zeroSpace A 6).neg_mem (primitive_defect A F dF))
      (mat_zeroSpace_charZero A 5 hv)
  rw [hh.f6] at m1
  obtain ⟨u,hu,W,_,hz⟩:=exists_head_poly m1
  have u0 : u k=0 := by by_contra h;exact hko ⟨u,hu,h⟩
  have heZ := hz k
  change (Paired.primitive F).eval (c k) - mat A d k = u k + W.eval (c k)*w k at heZ
  rw [u0,hwk,mul_zero,add_zero,hA,sub_zero] at heZ
  exact ⟨k,hko,hwk,Fk,heZ⟩

theorem off_mesh (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀j,i<j→b j=0)
    (hh:HeadData A 2 U w) {k:Fin (s+1)}
    (hu:¬Live U k) (hw:w k=0) :
    nodes A k=1 ∨ (mesh6:K[X]).eval (nodes A k)=0 := by
  classical
  by_cases h:k=i
  · subst k
    exact Or.inl (active_last_normal ha hs hi hl)
  right
  have he := mesh_at_end ha ho hs hi hl
  rw [hh.f6] at he
  obtain ⟨v,hv,P,_,hp⟩:=exists_head_poly he
  have zero : v k=0 := by by_contra hn;exact hu ⟨v,hv,hn⟩
  have hh:=hp k
  change (Pi.single i (1:K):Vec K (s+1)) k-(mesh6:K[X]).eval (nodes A k)=
    v k+P.eval (nodes A k)*w k at hh
  rwa [Pi.single_eq_of_ne h,zero,hw,mul_zero,add_zero,zero_sub,neg_eq_zero] at hh

theorem pure_primitive_formula (P:K[X]) (hP:P.natDegree≤4) (u:K) :
    (Paired.primitive (X*P)).eval u=RKCert.OrderTwelve.purePolynomialMoment P u := by
  classical
  let a:Fin 5→K:=fun j=>P.coeff j.val
  have e:ofFn 5 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have hh:=primitive_monomial_moment a u 1
  rw [pow_one,e] at hh
  rw [hh]
  unfold RKCert.OrderTwelve.purePolynomialMoment RKCert.OrderTwelve.pureMoment
  norm_num [moment,Fin.sum_univ_succ,a]
  ring

/-- On the pure rank-two chart the square determines an actual quartic
head of a fixed polynomial, not a freely fitted quartic. -/
theorem exclude_pure_two (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀j,i<j→b j=0)
    (hh:HeadData A 2 U w) (hU:MulClosed U) (hdis:∀ j,Live U j→w j=0)
    (hw4:w∈zeroSpace A 4) (hsites:7≤(headSites (nodes A) w).card)
    (hpure:w*w∈chain (diag (nodes A)) U w 5) : False := by
  classical
  let c:=nodes A
  change 7≤(headSites c w).card at hsites
  obtain ⟨h,hhU,P,hP,ep⟩:=exists_head_poly hpure
  have hp (j:Fin (s+1)) (hwj:w j≠0) : w j=P.eval (c j) := by
    have zh : h j=0 := by by_contra hz;exact hwj (hdis j ⟨h,hhU,hz⟩)
    have e:=ep j
    change w j*w j=h j+P.eval (c j)*w j at e
    rw [zh,zero_add] at e
    exact mul_right_cancel₀ hwj e
  have hp0:P≠0 := by
    intro hPz
    have w0:w=0 := by
      ext j
      by_contra hj
      apply hj
      simpa [hPz] using hp j hj
    simp [w0,headSites] at hsites
  have dp : P.natDegree≤4 := Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hp0).mpr hP)
  have hz: (Pi.single i (1:K):Vec K (s+1))-evalNodes A mesh6∈zeroSpace A 6 := mesh_at_end ha ho hs hi hl
  rw [hh.f6] at hz
  obtain ⟨e,he,Q,hQ,eq⟩:=exists_head_poly hz
  have dq : Q.natDegree≤2 := by
    by_cases em:Q=0
    · simp [em]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt em).mpr hQ)
  have hwi:=f5_vanish_at_last_active ha ho hs hi hl (zeroSpace_mono A (by decide :4≤5) hw4)
  have hf : (mesh6:K[X])=P*(-Q) := by
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
    · exact (Polynomial.degree_le_natDegree (p:=mesh6)).trans_lt (by exact_mod_cast
        (show (mesh6:K[X]).natDegree<(headSites c w).card from mesh6_natDegree.trans_lt (by omega)))
    · apply Polynomial.degree_le_natDegree.trans_lt
      have hm0 := natDegree_mul_le (p:=P) (q:= -Q)
      rw [natDegree_neg] at hm0
      exact_mod_cast (show (P*(-Q)).natDegree<(headSites c w).card from by omega)
    · intro x hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      have hwj:(w j)≠0 := (Finset.mem_filter.mp hj).2
      have e0:e j=0 := by by_contra hn;exact hwj (hdis j ⟨e,he,hn⟩)
      have hn:j≠i := by rintro rfl;exact hwj hwi
      have hhj:=eq j
      change (Pi.single i (1:K):Vec K (s+1)) j-(mesh6:K[X]).eval (c j)=e j+Q.eval (c j)*w j at hhj
      rw [Pi.single_eq_of_ne hn,e0,zero_sub,zero_add,hp j hwj] at hhj
      rw [eval_mul,eval_neg]
      linear_combination -hhj
  let D := (RKCert.OrderTwelve.dFivePoly:K[X])
  have dD:D.natDegree=5 := RKCert.OrderTwelve.natDegree_dFivePoly
  have hD:D≠0 := by intro hz; simp [hz] at dD
  have hM:(mesh6:K[X])≠0 := by rw [mesh_factor];exact mul_ne_zero X_ne_zero hD
  have dM:(mesh6:K[X]).natDegree=6 := by rw [mesh_factor,natDegree_X_mul hD,dD]
  have hQ0:(-Q)≠0 := by
    intro hq
    apply hM
    rw [hf,hq,mul_zero]
  have degPQ : P.natDegree+Q.natDegree=6 := by
    simpa only [hf,natDegree_mul hp0 hQ0,natDegree_neg] using dM
  have dP : P.natDegree=4 := by omega
  let T := -Q
  have fact : X*D=P*T := mesh_factor.symm.trans hf
  -- Consume one of two masks, depending on where the factor X lives.
  have noGate (M P0 : K[X]) (hM0:M≠0) (hdeg:M.natDegree≤1)
      (hp0':P0.natDegree=3∨P0.natDegree=4)
      (hdv:P0∣D) (fitted:M*P=X*P0) : False := by
    obtain ⟨k,hk,hk0,hkn,hprim⟩:=masked_primitive_zero ha ho hh hU hdis hw4 P M hp0 hM0 dp hdeg hp
    rw [fitted] at hkn hprim
    change (X*P0).eval (c k)≠0 at hkn
    have ck : c k≠0 := by intro h0;exact hkn (by simp [eval_mul,h0])
    have ep0 : P0.eval (c k)≠0 := by intro h0;exact hkn (by simp [eval_mul,h0])
    have hnode : c k=1 ∨ RKCert.OrderTwelve.dFive (c k)=0 ∧ P0.eval (c k)≠0 := by
      rcases off_mesh ha ho hs hi hl hh hk hk0 with e | hm
      · exact Or.inl e
      · right
        have hf := hm
        rw [mesh_factor,eval_mul,eval_X,RKCert.OrderTwelve.eval_dFivePoly] at hf
        exact ⟨(mul_eq_zero.mp hf).resolve_left ck,ep0⟩
    have hg := RKCert.OrderTwelve.pure_divisor_moment_ne_zero P0 hdv (c k) hp0' hnode
    rw [←pure_primitive_formula P0 (by rcases hp0' with h|h <;> omega)] at hg
    exact hg hprim
  by_cases hpz:P.eval 0=0
  · let W := P.divX
    have hcoeff : P.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
    have e : X*W=P := by simpa [W,hcoeff] using X_mul_divX_add P
    have hW : W≠0 := by intro z;apply hp0;rw [←e,z,mul_zero]
    have degW : W.natDegree=3 := by
      have hr := natDegree_X_mul hW
      rw [e,dP] at hr
      omega
    have eg : D=W*T := by
      apply (mul_left_cancel₀ X_ne_zero)
      rw [fact,←mul_assoc,e]
    exact noGate 1 W one_ne_zero (by simp) (Or.inl degW) ⟨T,eg⟩ (by rw [one_mul,e])
  · have pT := congrArg (Polynomial.eval (0:K)) fact
    simp only [eval_mul,eval_X,zero_mul] at pT
    have hc : T.coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero]
      exact (mul_eq_zero.mp pT.symm).resolve_left hpz
    have e : X*T.divX=T := by simpa [hc] using X_mul_divX_add T
    have eg : D=P*T.divX := by
      apply (mul_left_cancel₀ X_ne_zero)
      rw [fact]
      calc
        P*T=P*(X*T.divX) := congrArg (fun W=>P*W) e.symm
        _ = X*(P*T.divX) := by ring
    exact noGate X P X_ne_zero (by simp) (Or.inr dP) ⟨T.divX,eg⟩ rfl

end RKCert.Paired.OrderTwelve

