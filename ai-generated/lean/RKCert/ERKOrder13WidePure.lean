module
public import RKCert.ERKOrder13FourKnots
public import RKCert.ERKOrder13OddFactor

@[expose] public section
/-! # Full-odd pure two-chain with more than the minimum number of sites -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2000000

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem stage_of_headSite13 {c w:Vec K (s+1)} {x:K} (hx:x∈headSites c w) :
    ∃ i:Fin (s+1), w i≠0 ∧ c i=x := by
  classical
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hx
  exact ⟨i,(Finset.mem_filter.mp hi).2,he⟩

theorem order13_full_wide_pure_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 2 U w G)
    (mulc:MulClosed U) (dis:∀i,Live U i→w i=0) (pure:w*w∈Band13 A 6 2 U w 8)
    (wide:8≤(headSites (nodes A) w).card) : False := by
  classical
  let c:=nodes A
  change 8≤(headSites c w).card at wide
  have count : headLen 6 6 2 8<(headSites c w).card := by
    unfold headLen
    change 5<(headSites c w).card
    omega
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=w) (d:=0) dis count
    (fun k hk=>by
      have e : k=0 := by omega
      rw [e,pow_zero,one_apply_eq_self]
      exact pure)
  have pn : P≠0 := by
    intro hz
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites c w).card by omega)
    obtain ⟨i,hi',_⟩:=stage_of_headSite13 hx
    exact hi' (by rw [hP _ hi',hz,eval_zero])
  have deg := pd.resolve_left pn
  change P.natDegree+0<5 at deg
  have Pr : SevenProfile A 2 U w P := ⟨mulc,dis,pn,by omega,hP⟩
  have me : evalNodes A G∈chain (diag c) U w 4 := by
    change evalNodes A G∈chain (diag (nodes A)) U w (2+(6-4))
    rw [←C.marked.edge]
    exact C.meshPaid
  obtain ⟨u,hu,Q,Qd,eq⟩:=exists_head_poly me
  have qd : Q.natDegree≤3 := by
    by_cases q0:Q=0
    · simp [q0]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt q0).mpr Qd)
  have gu : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
    · exact degree_le_natDegree.trans_lt (by rw [C.meshDegree];exact_mod_cast (show 7<(headSites c w).card by omega))
    · have ht : (P*Q).natDegree≤7 := natDegree_mul_le.trans (by omega)
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree<(headSites c w).card by omega))
    · intro x hx
      obtain ⟨i,wi,rfl⟩:=stage_of_headSite13 hx
      have ui : u i=0 := by by_contra hz;exact wi (dis i ⟨u,hu,hz⟩)
      simpa only [ui,zero_add,hP i wi,eval_mul,evalNodes_apply,mul_comm] using eq i
  have gn:G≠0 := by intro h;have d:=C.meshDegree;rw [h,natDegree_zero] at d;omega
  have qn:Q≠0 := by intro h;exact gn (by rw [gu,h,mul_zero])
  have degP : P.natDegree=4 := by
    have h:=congrArg natDegree gu
    rw [C.meshDegree,natDegree_mul pn qn] at h
    omega
  by_cases p0:P.eval 0=0
  · have h : (X:K[X])∣P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
    obtain ⟨R,e⟩:=h
    have rn : R≠0 := fun hz=>pn (by rw [e,hz,mul_zero])
    have rd : R.natDegree≤3 := by rw [e,natDegree_X_mul rn] at degP;omega
    exact cubic_from_thirteen_masks ha ho S M C Pr R rn rd 0 (by decide) (by rwa [pow_zero,one_mul])
  · have scale : ∃ a:K,a≠0 ∧ G=a•(X*oddSixPoly) := by
      cases C.mesh with
      | full x h =>
        refine ⟨x,?_,?_⟩
        · intro hz;apply gn;rw [h,hz,zero_smul]
        · rw [h,odd6_as_oddSix]
    obtain ⟨a,an,hG⟩:=scale
    have h0 : Q.eval 0=0 := by
      have e:=congrArg (fun T:K[X]=>T.eval 0) gu
      rw [hG,eval_smul,eval_mul,eval_X,zero_mul,smul_zero,eval_mul] at e
      exact (mul_eq_zero.mp e.symm).resolve_left p0
    obtain ⟨J,hJ⟩ : (X:K[X])∣Q := by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr h0
    have h : (a•(oddSixPoly:K[X]))=P*J := by
      apply mul_left_cancel₀ X_ne_zero
      rw [mul_smul_comm,←hG,gu,hJ]
      ring
    have pfactor : P∣(oddSixPoly:K[X]) := by
      use a⁻¹•J
      have hh:=congrArg (fun V:K[X]=>a⁻¹•V) h
      simpa only [smul_smul,inv_mul_cancel₀ an,one_smul,mul_smul_comm] using hh
    obtain ⟨i,hi,hv,nz,tests⟩:=physical_thirteen_knot ha ho S M C Pr (X:K[X]) X_ne_zero (by simp)
    let z:=c i
    have nu:z*P.eval z≠0 := by simpa only [eval_mul,eval_X] using nz
    have inn:z≠0 := fun hz=>nu (by rw [hz,zero_mul])
    have hn:P.eval z≠0 := fun hz=>nu (by rw [hz,mul_zero])
    have ui:u i=0 := by by_contra hz;exact hi ⟨u,hu,hz⟩
    have e:=eq i
    change G.eval z=u i+Q.eval z*w i at e
    rw [ui,hv,mul_zero,add_zero,hG,eval_smul,smul_eq_mul,eval_mul,eval_X,oddSixPoly_eval] at e
    apply fixed13_odd_divisor_nonzero P degP pfactor z
      (Or.inr ⟨(mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left an)).resolve_left inn,hn⟩)
    have h := tests 1 (by simp)
    simpa only [one_mul] using h

end RKCert.Paired.FiniteMidpoint
