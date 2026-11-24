module
public import RKCert.ERKFiniteCore

@[expose] public section

/-! # A genuine polynomial multiplier and the forced bulk mesh divisor -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
set_option maxHeartbeats 1500000
variable {K:Type*} [Field K] [CharZero K] {s q ε d a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}

structure Profile (A:Fin (s+1)→Fin (s+1)→K) (q a:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (G P:K[X]) : Prop where
  algebra : MulClosed U
  disjoint : ∀ i,Live U i→w i=0
  nonzero : P≠0
  degree : P.natDegree≤4
  aliasDegree : a<q→P.natDegree≤3
  repr : ∀ i,w i≠0→w i=P.eval (nodes A i)
  factor : P∣G

theorem physical_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:q=8∨q=9) (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d)
    (C:Chart A q ε d a r U w G) :
    ∃ v P,Chart A q ε d a r U v G ∧ Profile A q a U v G P := by
  classical
  obtain ⟨v,C,mulc,dis⟩:=clean_head ha ho hq he S M C
  have r2:=C.marked.rTwo
  have aLe:=C.aLe
  have aLo:=C.aLo
  have cms:=chart_sites (by omega) C
  have cn:=chart_count_ten (by omega) C
  obtain ⟨P,pd,hP⟩:=multiplier_degree (a:=v) (d:=2*r-2) dis cn (head_square_band ha ho hq he S M C)
  have pn:P≠0 := by
    intro hz
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩:=Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    exact hi' (by rw [hP _ hi',hz,eval_zero])
  have pdeg := pd.resolve_left pn
  unfold headLen at pdeg cms
  have gp : evalNodes A G∈chain (diag (nodes A)) U v (r+(q-4)) := by
    rw [←C.marked.edge]
    exact C.meshPaid
  obtain ⟨u,hu,Q,Qd,hG⟩:=exists_head_poly gp
  have Qd' : Q.natDegree≤r+q-5 := by
    by_cases hz:Q=0
    · simp [hz]
    · have h := (natDegree_lt_iff_degree_lt hz).mpr Qd
      omega
  have gn:G≠0 := by
    intro hz
    have d:=C.meshDegree
    rw [hz,natDegree_zero] at d
    omega
  have Gfact : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites (nodes A) v)
    · exact (degree_le_natDegree.trans_lt (by
        have : G.natDegree<(headSites (nodes A) v).card := by rw [C.meshDegree];omega
        exact_mod_cast this))
    · exact (degree_le_natDegree.trans_lt (by
        have : (P*Q).natDegree<(headSites (nodes A) v).card := by
          have h := natDegree_mul_le (p:=P) (q:=Q)
          omega
        exact_mod_cast this))
    · intro z hz
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hz
      have live := (Finset.mem_filter.mp hi).2
      have dead : u i=0 := by by_contra hn;exact live (dis _ ⟨_,hu,hn⟩)
      simpa [dead,hP _ live,eval_mul,mul_comm] using hG i
  have qn:Q≠0 := by intro hz;exact gn (by rw [Gfact,hz,mul_zero])
  have aliasP (h:a<q) : P.natDegree≤3 := by
    have ne : evalNodes A G∉defectPlus A d q := by
      intro hG
      exact gn (separated_plus S M _ (by rw [C.meshDegree];omega) hG)
    have top : r+q-5≤Q.natDegree := by
      by_contra hnot
      have hpaid : weightedEval (nodes A) v Q∈chain (diag (nodes A)) U v (r+(q-5)) :=
        weighted_chain Q (by omega)
      rw [←C.marked.paid q (by omega) le_rfl] at hpaid
      apply ne
      have eq : evalNodes A G=u+weightedEval (nodes A) v Q := by
        ext i
        simpa [weightedEval_apply] using hG i
      rw [eq]
      exact Submodule.add_mem _ (Fplus_mono A d (by omega) (C.marked.core hu)) hpaid
    have eq : G.natDegree=P.natDegree+Q.natDegree := by rw [Gfact,natDegree_mul pn qn]
    rw [C.meshDegree] at eq
    omega
  have pb:P.natDegree≤4 := by
    by_cases h:a<q
    · exact (aliasP h).trans (by decide)
    · omega
  exact ⟨v,P,C,⟨mulc,dis,pn,pb,aliasP,hP,⟨Q,Gfact⟩⟩⟩

end RKCert.Paired.FiniteMidpoint

