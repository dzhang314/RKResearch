module
public import RKCert.ERKOrder13MarkedCore
public import RKCert.ERKOrder13WidePure
public import RKCert.ERKFiniteCore

@[expose] public section
/-! # Literal pure marked rank-two factor, not a root-cloud assumption -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 3000000

theorem marked13_head_sites_eleven (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G) :
    headLen 6 a r 11≤(headSites (nodes A) w).card := by
  let n:=headLen 6 a r 10
  let D:=diag (nodes A)
  have width:=C.width
  have e10:=C.chart 10 (by omega) (by decide)
  have r10:=C.rich 10 (by omega) (by decide)
  obtain ⟨top,step⟩:=thirteen_prefix_exact_eleven ha ho S M C
  have r11 : finrank K (treePlus A 1 11)=s+1 := by
    calc finrank K (treePlus A 1 11) = finrank K (⊤:Submodule K (Vec K (s+1))) :=
          congrArg (fun T:Submodule K (Vec K (s+1))=>finrank K T) top
       _ = _ := by simp only [finrank_top,Module.finrank_fin_fun]
  have sz:=S.size
  have len : headLen 6 a r 11=n+1 := by unfold n headLen;omega
  have base : chain D U w n≤treePlus A 1 10 := le_sup_right.trans (le_of_eq e10.symm)
  have paid := (chain_le_iff n).mp base
  have notpaid : (D^n) w∉treePlus A 1 10 := by
    intro h
    have cb : Band13 A a r U w 11≤treePlus A 1 10 := by
      unfold Band13 forwardBand
      rw [len]
      exact sup_le base ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have ff : treePlus A 1 11≤treePlus A 1 10 := by
      rw [step]
      exact sup_le (le_sup_left.trans (le_of_eq e10.symm)) cb
    have rk:=Submodule.finrank_mono ff
    omega
  have ct:=more_sites_than_paid paid.2 notpaid
  omega

theorem marked13_pure_literal_factor (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (dis:∀i,Live U i→w i=0) (pure:w*w∈Band13 A a 2 U w 8) :
    ∃ P Q:K[X],P≠0 ∧ Q≠0 ∧ G=P*Q ∧ P.natDegree=a-2 ∧ Q.natDegree=3 ∧
      ∀ i,w i≠0→w i=P.eval (nodes A i) := by
  classical
  let c:=nodes A
  have wdt:=C.width
  have big:=marked13_head_sites_eleven ha ho S M C
  change headLen 6 a 2 11≤(headSites c w).card at big
  have ct : headLen 6 a 2 8<(headSites c w).card := by unfold headLen at *;omega
  obtain ⟨P,pd,rep⟩:=multiplier_degree (a:=w) (d:=0) dis ct
    (fun k hk=>by
      have e:k=0:=by omega
      rw [e,pow_zero,one_apply_eq_self]
      exact pure)
  have pn : P≠0 := by
    intro e
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites c w).card by omega)
    obtain ⟨i,h,_⟩:=stage_of_headSite13 hx
    exact h (by rw [rep i h,e,eval_zero])
  have fit:=pd.resolve_left pn
  have m : evalNodes A G∈chain (diag c) U w 4 := by
    change evalNodes A G∈chain (diag (nodes A)) U w (2+(6-4))
    rw [←C.marked.edge]
    exact C.meshPaid
  obtain ⟨u,hu,Q,Qd,values⟩:=exists_head_poly m
  have qd : Q.natDegree≤3 := by
    by_cases qn:Q=0
    · simp [qn]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt qn).mpr Qd)
  have gn:G≠0 := by intro e;have h:=C.meshDegree;rw [e,natDegree_zero] at h;omega
  have factor : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
    · apply degree_le_natDegree.trans_lt
      rw [C.meshDegree]
      exact_mod_cast (show a+1<(headSites c w).card by unfold headLen at big;omega)
    · apply degree_le_natDegree.trans_lt
      have deg:=natDegree_mul_le (p:=P) (q:=Q)
      exact_mod_cast (show (P*Q).natDegree<(headSites c w).card by unfold headLen at fit big;omega)
    · intro x hx
      obtain ⟨i,wn,rfl⟩:=stage_of_headSite13 hx
      have v0:u i=0 := by by_contra h;exact wn (dis i ⟨u,hu,h⟩)
      simpa only [evalNodes_apply,eval_mul,v0,zero_add,rep i wn,mul_comm] using values i
  have qn:Q≠0 := fun e=>gn (by rw [factor,e,mul_zero])
  have alias_top (h:a=5) : 3≤Q.natDegree := by
    by_contra! small
    have weighted : weightedEval c w Q∈chain (diag c) U w 3 := weighted_chain Q small
    have t : evalNodes A G∈defectPlus A 1 6 := by
      rw [C.marked.paid 6 (by decide) le_rfl]
      change evalNodes A G∈chain (diag c) U w 3
      have e : evalNodes A G=u+weightedEval c w Q := by ext i;simpa only [Pi.add_apply,weightedEval_apply] using values i
      rw [e]
      exact Submodule.add_mem _ (((chain_le_iff _).mp le_rfl).1 hu) weighted
    exact gn (separated_plus S M G (by rw [C.meshDegree,h]) t)
  have term:=congrArg natDegree factor
  rw [C.meshDegree,natDegree_mul pn qn] at term
  have cap:Q.natDegree=3 := by
    rcases C.shape with h|⟨h,_⟩
    · unfold headLen at fit;omega
    · have tl:=alias_top h
      omega
  exact ⟨P,Q,pn,qn,factor,by omega,cap,rep⟩

end RKCert.Paired.FiniteMidpoint
