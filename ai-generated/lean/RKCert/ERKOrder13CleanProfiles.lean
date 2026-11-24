module
public import RKCert.ERKOrder13MarkedPureFactor
public import RKCert.ERKOrder13MarkedPureMasks

@[expose] public section

/-! # Rank dispatch for the full fourth-defect rank
All powers up to the actual product budget are checked with the same
three-shift lemma. The alias uses the exact top mesh coefficient, not
an assumed root split or degree count at too few nodes.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
  RKCert.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 3200000

/-- Three adjacent paid clock powers purify an entire finite tested run. -/
theorem marked13_purify_run (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (z:Vec K (s+1)) (n:ℕ) (nn:2≤n)
    (h:∀k≤n,(diag (nodes A)^k) z∈defectPlus A 1 8) :
    ∀k≤n,(diag (nodes A)^k) z∈Band13 A a r U w 8 := by
  let D:=diag (nodes A)
  intro k hk
  let j:=min k (n-2)
  have j1:j≤k := min_le_left _ _
  have j2:j≤n-2 := min_le_right _ _
  have e1 : D ((D^j) z)=(D^(j+1)) z := by rw [pow_succ'];rfl
  have e2 : D (D ((D^j) z))=(D^(j+2)) z := by
    calc
      _ = D ((D^(j+1)) z) := congrArg D e1
      _ = _ := by rw [show j+2=j+1+1 by omega,pow_succ' D (j+1)];rfl
  have res := order13_marked_no_leak ha ho S M C (h j (by omega))
    (by change D ((D^j) z)∈_;rw [e1];exact h _ (by omega))
    (by change D (D ((D^j) z))∈_;rw [e2];exact h _ (by omega))
  change (D^k) z∈_
  rcases (show k=j∨k=j+1∨k=j+2 by dsimp [j];omega) with u|u|u
  · rw [u];exact res.1
  · rw [u,←e1];exact res.2.1
  · rw [u,←e2];exact res.2.2

omit [CharZero K] in
theorem marked13_paid_square_run (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (H:MarkedHead A 6 1 r U w)
    (h4:finrank K (zeroSpace A 4)=4) :
    ∀ k≤2*r-4,(diag (nodes A)^k) (w*w)∈defectPlus A 1 8 := by
  let D:=diag (nodes A)
  have two:=H.rTwo
  have f4:=marked13_four_exact ho S M H h4
  have pay (k:ℕ) (hk:k<r-1) : (D^k) w∈defectPlus A 1 4 := by
    rw [f4]
    exact ((chain_le_iff _).mp le_rfl).2 _ hk
  intro k hk
  let i:=min k (r-2)
  let j:=k-i
  have eq:i+j=k := by dsimp [j,i];omega
  have ip:i<r-1 := by dsimp [i];omega
  have jp:j<r-1 := by dsimp [j,i];omega
  change (D^k) (w*w)∈defectPlus A 1 (4+4)
  have prod : (D^k) (w*w)=((D^i) w)*((D^j) w) := by
    ext l
    simp only [D,pow_diag_apply,Pi.mul_apply]
    rw [←eq,pow_add]
    ring
  rw [prod]
  exact Fplus_mul (pay i ip) (pay j jp)

/-- Extract a literal factor and its exact remaining stroke budget for
any rank ≥3 with fourth ordinary defect rank four. -/
theorem marked13_four_clean_profile (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (hr:3≤r) (h4:finrank K (zeroSpace A 4)=4) :
    ∃ v:Vec K (s+1), ∃ P:K[X], Chart13 A 1 a r U v G ∧
      MulClosed U ∧ (∀i,Live U i→v i=0) ∧ P≠0 ∧ P∣G ∧ P.natDegree+r=a ∧
      (∀i,v i≠0→v i=P.eval (nodes A i)) := by
  classical
  obtain ⟨v,C,alg,dis⟩:=marked13_four_clean ha ho S M C h4
  have wa:=C.width
  have ct:=marked13_head_sites_eleven ha ho S M C
  have pure := marked13_purify_run ha ho S M C (v*v) (2*r-4) (by omega)
    (marked13_paid_square_run ho S M C.marked h4)
  have rich : headLen 6 a r 8<(headSites (nodes A) v).card := by unfold headLen at *;omega
  obtain ⟨P,pd,rep⟩:=multiplier_degree dis rich pure
  have pn : P≠0 := by
    intro fake
    obtain ⟨z,hz⟩:=Finset.card_pos.mp (show 0<(headSites (nodes A) v).card by omega)
    obtain ⟨i,vi,_⟩:=stage_of_headSite13 hz
    exact vi (by rw [rep i vi,fake,eval_zero])
  have pdeg:=pd.resolve_left pn
  have edge:evalNodes A G∈chain (diag (nodes A)) U v (r+2) := by
    have c:=C.meshPaid
    rw [C.marked.edge] at c
    exact c
  obtain ⟨u,hu,Q,Qd,hrp⟩:=exists_head_poly edge
  have qd:Q.natDegree≤r+1 := by
    by_cases qn:Q=0
    · simp [qn]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt qn).mpr (by simpa only [Nat.add_assoc] using Qd))
  have gn:G≠0 := by intro z;have h:=C.meshDegree;rw [z,natDegree_zero] at h;omega
  have fact:G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites (nodes A) v)
    · exact degree_le_natDegree.trans_lt (by rw [C.meshDegree];exact_mod_cast (show a+1<(headSites (nodes A) v).card by unfold headLen at ct;omega))
    · have h:=natDegree_mul_le (p:=P) (q:=Q)
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (P*Q).natDegree<(headSites (nodes A) v).card by unfold headLen at ct pdeg;omega))
    · intro x hx
      obtain ⟨i,vi,rfl⟩:=stage_of_headSite13 hx
      have z:u i=0 := by
        by_contra no
        exact vi (dis i ⟨u,hu,no⟩)
      simpa only [evalNodes_apply,eval_mul,z,zero_add,rep i vi,mul_comm] using hrp i
  have qn:Q≠0 := fun hz=>gn (by rw [fact,hz,mul_zero])
  have deg := congrArg natDegree fact
  rw [C.meshDegree,natDegree_mul pn qn] at deg
  have alias_top (h:a=5) : Q.natDegree=r+1 := by
    by_contra! lo
    have fit := marked13_mask_budget6 C.marked Q (by omega)
    have t : evalNodes A G = u+weightedEval (nodes A) v Q := by ext i;simpa only [Pi.add_apply,weightedEval_apply] using hrp i
    have gp : evalNodes A G∈defectPlus A 1 6 := by
      rw [t]
      exact Submodule.add_mem _ (Fplus_mono A 1 (by decide) (C.marked.core hu)) fit
    exact gn (separated_plus S M G (by rw [C.meshDegree,h]) gp)
  refine ⟨v,P,C,alg,dis,pn,⟨Q,fact⟩,?_,rep⟩
  rcases C.shape with eq|⟨eq,_⟩
  · unfold headLen at pdeg
    omega
  · have :=alias_top eq
    omega

end RKCert.Paired.FiniteMidpoint
