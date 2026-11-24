module
public import RKCert.ERKOrder13JointPencil
public import RKCert.ERKOrder13JointAffine

@[expose] public section
/-! # Mixed affine head cancellation without exceptional repeated zeros
The literal GL=P Q identity is enough. If L fails to divide Q, the unique
root of the degree-one L forces L to divide P. The quotient profile then
holds even at that root by the original physical mesh relation. No
squarefree assumption on x times the pencil is used. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve
  RKCert.Endpoint RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G P:K[X]}
set_option maxHeartbeats 4500000

theorem marked13_mixed_identity (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G) (hr:4≤r)
    (vn:v∉U) (vbase:v∈chain (diag (nodes A)) U w 2)
    (dis:∀i,Live U i→w i=0) (pd:P.natDegree+r+a≤13)
    (rep:∀i,w i≠0→v i=P.eval (nodes A i)) :
    ∃ L Q:K[X], L≠0 ∧ Q≠0 ∧ P≠0 ∧ L.natDegree≤1 ∧ Q.natDegree≤r+1 ∧
      (a=5→Q.natDegree=r+1) ∧ G*L=P*Q ∧
      ∀i,w i≠0→w i*L.eval (nodes A i)=P.eval (nodes A i)∧w i*Q.eval (nodes A i)=G.eval (nodes A i) := by
  classical
  obtain ⟨u,hu,L,Ld,vals⟩:=exists_head_poly vbase
  have ln:L≠0 := by
    intro z
    apply vn
    have eq : v=u := by ext i;simpa only [z,eval_zero,zero_mul,add_zero] using vals i
    rwa [eq]
  have ld:L.natDegree≤1 := by have :=(natDegree_lt_iff_degree_lt ln).mpr Ld;omega
  have edge:=C.meshPaid
  rw [C.marked.edge] at edge
  obtain ⟨g,hg,Q,Qd,mes⟩:=exists_head_poly edge
  have qd:Q.natDegree≤r+1 := by
    by_cases h:Q=0
    · simp [h]
    · have :=(natDegree_lt_iff_degree_lt h).mpr Qd
      omega
  have nv:G≠0 := by intro z;have h:=C.meshDegree;rw [z,natDegree_zero] at h;omega
  have vals' (i:Fin (s+1)) (wi:w i≠0) :
      w i*L.eval (nodes A i)=P.eval (nodes A i)∧w i*Q.eval (nodes A i)=G.eval (nodes A i) := by
    have zero {x:Vec K (s+1)} (hx:x∈U) : x i=0 := by
      by_contra hz
      exact wi (dis i ⟨x,hx,hz⟩)
    have t:=vals i
    rw [rep i wi,zero hu,zero_add,mul_comm] at t
    have z:=mes i
    rw [evalNodes_apply,zero hg,zero_add,mul_comm] at z
    exact ⟨t.symm,z.symm⟩
  have facts:G*L=P*Q := by
    have N:=marked13_head_sites_eleven ha ho S M C
    have wa:=C.width
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites (nodes A) w)
    · have h := natDegree_mul_le (p:=G) (q:=L)
      rw [C.meshDegree] at h
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (G*L).natDegree < (headSites (nodes A) w).card by unfold headLen at N;omega))
    · have h := natDegree_mul_le (p:=P) (q:=Q)
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree < (headSites (nodes A) w).card by unfold headLen at N;omega))
    · intro x hx
      obtain ⟨i,wi,rfl⟩:=stage_of_headSite13 hx
      have ⟨l,q⟩:=vals' i wi
      rw [eval_mul,eval_mul,←l,←q]
      ring
  have prod:G*L≠0 := mul_ne_zero nv ln
  have pn:P≠0 := fun p=>prod (by rw [facts,p,zero_mul])
  have qn:Q≠0 := fun q=>prod (by rw [facts,q,mul_zero])
  refine ⟨L,Q,ln,qn,pn,ld,qd,?_,facts,vals'⟩
  intro al
  by_contra! less
  have pay := marked13_mask_budget6 C.marked Q (by omega)
  have eq : evalNodes A G=g+weightedEval (nodes A) w Q := by
    ext i
    simpa only [Pi.add_apply,weightedEval_apply] using mes i
  have gp:evalNodes A G∈defectPlus A 1 6 := by
    rw [eq]
    exact (defectPlus A 1 6).add_mem (Fplus_mono A 1 (by decide) (C.marked.core hg)) pay
  exact nv (separated_plus S M G (by rw [C.meshDegree,al]) gp)

theorem marked13_clean_smaller_factor_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    (pn:P≠0) (pd:P.natDegree≤3) (pf:P∣G)
    (pay:6≤P.natDegree+r) (rep:∀i,w i≠0→w i=P.eval (nodes A i)) : False := by
  rcases C.shape with rfl|⟨rfl,_⟩
  · have mult:w*w-weightedEval (nodes A) w P∈U := by
      have eq : w*w-weightedEval (nodes A) w P=(0:Vec K (s+1)) := by
        ext i
        by_cases wi:w i=0
        · simp [weightedEval_apply,wi]
        · simp [weightedEval_apply,←rep i wi]
      rw [eq];exact U.zero_mem
    have st:U.map (diag w)≤U := by
      rintro _ ⟨u,hu,rfl⟩
      have e : diag w u=0 := by
        ext i
        by_cases h:u i=0
        · simp [h]
        · simp [dis i ⟨u,hu,h⟩]
      rw [e];exact U.zero_mem
    have w5 : w∈defectPlus A 1 5 := by
      have h:=marked13_mask_budget5 C.marked (1:K[X]) (by have := C.marked.rTwo;simp;omega)
      have e : weightedEval (nodes A) w (1:K[X])=w := by ext i;simp [weightedEval_apply]
      rwa [e] at h
    exact marked13_joint_unaliased_impossible ha ho S M C st mult w5 pn (by omega) pf
      (fun B h=>marked13_mask_budget5 C.marked B (by omega))
      (fun B h=>marked13_mask_budget6 C.marked B (by omega))
  · exact marked13_clean_alias_impossible ha S M C alg dis pn pd pf rep

theorem marked13_mixed_factor_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G) (hr:4≤r)
    (alg:MulClosed U) (dis:∀i,Live U i→w i=0)
    {k:ℕ} (sk:k≤3) (budget:k+r≤7) (vk:v∈defectPlus A 1 k) (vn:v∉U)
    (vbase:v∈chain (diag (nodes A)) U w 2)
    (pd:P.natDegree+r+a≤13) (rep:∀i,w i≠0→v i=P.eval (nodes A i)) : False := by
  obtain ⟨L,Q,ln,qn,pn,ld,qd,al,identity,vals⟩:=
    marked13_mixed_identity ha ho S M C hr vn vbase dis pd rep
  have wa:=C.width
  have nv:G≠0 := by intro z;have h:=C.meshDegree;rw [z,natDegree_zero] at h;omega
  have deg:=congrArg natDegree identity
  rw [natDegree_mul nv ln,C.meshDegree,natDegree_mul pn qn] at deg
  have shape (D:K[X]) (p:D≠0) (d:D.natDegree≤3) (pf:D∣G) (ju:6≤D.natDegree+r)
      (rep:∀i,w i≠0→w i=D.eval (nodes A i)) : False :=
    marked13_clean_smaller_factor_impossible ha ho S M C alg dis p d pf ju rep
  by_cases ld0:L.natDegree=0
  · let c:=L.coeff 0
    have lc:L=Polynomial.C c := eq_C_of_natDegree_eq_zero ld0
    have cn:c≠0 := fun z=>ln (by rw [lc,z,map_zero])
    let D:=c⁻¹•P
    have dn:D≠0 := smul_ne_zero (inv_ne_zero cn) pn
    have dd:D.natDegree=P.natDegree := natDegree_smul _ (inv_ne_zero cn)
    have id:G=D*Q := by
      have h:=congrArg (fun z:K[X]=>c⁻¹•z) identity
      change c⁻¹ • (G*L)=c⁻¹ • (P*Q) at h
      rw [lc,mul_comm G,←smul_eq_C_mul,smul_smul,inv_mul_cancel₀ cn,one_smul,←smul_mul_assoc] at h
      exact h
    have rc:∀i,w i≠0→w i=D.eval (nodes A i) := by
      intro i wi
      have h: w i*c=P.eval (nodes A i) := by simpa only [lc,eval_C] using (vals i wi).1
      change w i=(c⁻¹•P).eval (nodes A i)
      rw [eval_smul,smul_eq_mul,←h,mul_comm (w i),←mul_assoc,inv_mul_cancel₀ cn,one_mul]
    rcases C.shape with rfl|⟨rfl,_⟩
    · exact shape D dn (by omega) ⟨Q,id⟩ (by omega) rc
    · exact marked13_clean_alias_impossible ha S M C alg dis dn (by have := al rfl;omega) ⟨Q,id⟩ rc
  have ld1:L.natDegree=1 := by omega
  by_cases divides:L∣Q
  · obtain ⟨J,jf⟩:=divides
    have fac:G=P*J := by
      apply mul_right_cancel₀ ln
      simpa only [jf,mul_left_comm,mul_comm,mul_assoc] using identity
    have v5:=Fplus_mono A 1 (by omega : k≤5) vk
    have st:=marked13_multiplier_stable ha ho S M C (Fplus_mono A 1 sk vk)
    have mult:v*w-weightedEval (nodes A) w P∈U := by
      have h:v*w-weightedEval (nodes A) w P=(0:Vec K (s+1)) := by
        ext i
        by_cases z:w i=0
        · simp [weightedEval_apply,z]
        · simp [weightedEval_apply,rep i z]
      rw [h];exact U.zero_mem
    rcases C.shape with rfl|⟨rfl,_⟩
    · exact marked13_joint_unaliased_impossible ha ho S M C st mult v5 pn (by omega) ⟨J,fac⟩
        (fun B h=>Fplus_mono A 1 (by omega) (marked_weight_from_grade B vk))
        (fun B h=>Fplus_mono A 1 (by omega) (marked_weight_from_grade B vk))
    · have w5 : weightedEval (nodes A) v X∈defectPlus A 1 5 :=
        Fplus_mono A 1 (by rw [natDegree_X];omega) (marked_weight_from_grade X vk)
      exact marked13_joint_alias_impossible ha S M C st mult v5 w5 pn (by have := al rfl;omega) ⟨J,fac⟩
  · obtain ⟨t,rt⟩:=L.exists_root_of_natDegree_eq_one ld1
    obtain ⟨J,Jf⟩:=dvd_iff_isRoot.mpr rt
    have jn:J≠0 := fun z=>ln (by rw [Jf,z,mul_zero])
    have jd := congrArg natDegree Jf
    rw [ld1,natDegree_mul (X_sub_C_ne_zero _) jn,natDegree_X_sub_C] at jd
    let c:=J.coeff 0
    have jc:J=Polynomial.C c := eq_C_of_natDegree_eq_zero (by omega)
    have cn:c≠0 := fun z=>jn (by rw [jc,z,map_zero])
    have lu : IsUnit J := by rw [jc];exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr cn)
    have same (H:K[X]) : L∣H↔H.eval t=0 := by
      rw [Jf,lu.mul_right_dvd,dvd_iff_isRoot]
      rfl
    have qt:Q.eval t≠0 := fun z=>divides ((same Q).mpr z)
    have pt:P.eval t=0 := by
      have h:=congrArg (Polynomial.eval t) identity
      rw [eval_mul,show L.eval t=0 from rt,mul_zero,eval_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right qt
    obtain ⟨D,Df⟩:=(same P).mpr pt
    have dn:D≠0 := fun z=>pn (by rw [Df,z,mul_zero])
    have dd:=congrArg natDegree Df
    rw [natDegree_mul ln dn,ld1] at dd
    have fact:G=D*Q := by
      apply mul_right_cancel₀ ln
      rw [Df] at identity
      calc G*L = L*D*Q := identity
        _ = _ := by ring
    have rc (i:Fin (s+1)) (wi:w i≠0) : w i=D.eval (nodes A i) := by
      have ⟨wl,wq⟩:=vals i wi
      by_cases zero:L.eval (nodes A i)=0
      · have e : nodes A i=t := by
          rw [Jf,jc,eval_mul,eval_sub,eval_X,eval_C,eval_C] at zero
          exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right cn)
        rw [e,fact,eval_mul] at wq
        rw [e]
        exact mul_right_cancel₀ qt wq
      · rw [Df,eval_mul,mul_comm (L.eval (nodes A i))] at wl
        exact mul_right_cancel₀ zero wl
    rcases C.shape with rfl|⟨rfl,_⟩
    · exact shape D dn (by omega) ⟨Q,fact⟩ (by omega) rc
    · exact marked13_clean_alias_impossible ha S M C alg dis dn (by have :=al rfl;omega) ⟨Q,fact⟩ rc

end RKCert.Paired.FiniteMidpoint
