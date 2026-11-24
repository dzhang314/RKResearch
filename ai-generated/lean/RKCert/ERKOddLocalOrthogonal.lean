module
public import RKCert.ERKOddLocalBand

@[expose] public section
/-! # Exact localization and projection for a native one-head reverse band -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.OneEscape RKCert.Endpoint
open Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
noncomputable section

theorem dot_orthogonal_inter_zero {s:ℕ}{U:Submodule K (Vec K s)}{v:Vec K s}
    (u:v∈U)(o:v∈annih U):v=0:=by
  have h:=Submodule.finrank_sup_add_finrank_inf_eq U (annih U)
  rw [dot_split_own_annih,finrank_top,Module.finrank_fin_fun,finrank_annih_eq] at h
  have hd:finrank K ↥(U⊓annih U)=0:=by omega
  have z:U⊓annih U=⊥:=Submodule.finrank_eq_zero.mp hd
  have hu:v∈U⊓annih U:=⟨u,o⟩
  rw [z] at hu
  exact hu

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem diag_annih_invariant {s:ℕ}{y:Vec K s}{U:Submodule K (Vec K s)}
    (h:U.map (diag y)≤U):(annih U).map (diag y)≤annih U:=by
  rintro _ ⟨v,hv,rfl⟩
  apply mem_annih.mpr
  intro u hu
  have e:=mem_annih.mp hv _ (h (Submodule.mem_map_of_mem hu))
  rw [row_apply] at e ⊢
  convert e using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [diag_apply]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem weightedEval_orthogonal {s:ℕ}{y τ:Vec K s}{U:Submodule K (Vec K s)}
    (h:U.map (diag y)≤U)(o:τ∈annih U)(P:K[X]):
    weightedEval y τ P∈annih U:=by
  have e:weightedEval y τ P=(fun i=>P.eval (y i)*τ i):=by ext i;exact weightedEval_apply _ _ _ _
  rw [e]
  exact Clock.poly_preserves (diag_annih_invariant h) P τ o

variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}

theorem LocalLinearBand.representation (B:LocalLinearBand A b r U τ)
    {v:Vec K 26}(h:v∈annih (treeSpace A 8)):
    ∃u∈U,∃P:K[X],P.natDegree≤7-r ∧ v=u+weightedEval (mirror A) τ P:=by
  rw [B.full] at h
  obtain ⟨u,hu,P,dP,eq⟩:=Clock.exists_head_poly h
  refine ⟨u,hu,P,?_,?_⟩
  · by_cases e:P=0
    · simp [e]
    have rle:r≤2:=by rcases B.short with z|z <;> omega
    rw [degree_eq_natDegree e] at dP
    have dx:P.natDegree<8-r:=by exact_mod_cast dP
    omega
  · ext i
    rw [Pi.add_apply,weightedEval_apply]
    exact eq i

theorem LocalLinearBand.representation_orthogonal (B:LocalLinearBand A b r U τ)
    {v:Vec K 26}(ov:v∈annih U)(h:v∈annih (treeSpace A 8)):
    ∃P:K[X],P.natDegree≤7-r ∧ weightedEval (mirror A) τ P=v:=by
  obtain ⟨u,hu,P,dP,e⟩:=B.representation h
  have z: u=v-weightedEval (mirror A) τ P:=by rw [e];abel
  have oz:u∈annih U:=z.symm ▸ (annih U).sub_mem ov (weightedEval_orthogonal B.clock B.orthogonal P)
  exact ⟨P,dP,by simpa [dot_orthogonal_inter_zero hu oz] using e.symm⟩

theorem LocalLinearBand.localized (B:LocalLinearBand A b r U τ) {v:Vec K 26}
    (h:v∈annih (treeSpace A 8)) {a:K} (off:∀i,mirror A i≠a→v i=0):v∈U:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  obtain ⟨u,hu,P,dP,E⟩:=B.representation h
  let T:=(headSites y τ).erase a
  have enough:8-r≤T.card:=by
    have hi:=B.sites
    change 9-r≤(headSites y τ).card at hi
    have h:=Finset.pred_card_le_card_erase (s:=headSites y τ) (a:=a)
    change (headSites y τ).card-1≤T.card at h
    rcases B.short with f|f <;> omega
  have counts:7-r<8-r:=by rcases B.short with f|f <;> omega
  have P0:P=0:=by
    apply eq_of_degrees_lt_of_eval_finset_eq T
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show P.natDegree<T.card by omega))
    · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<T.card by omega))
    intro x hx
    obtain ⟨xa,xS⟩:=Finset.mem_erase.mp hx
    obtain ⟨i,hi,ic⟩:=Finset.mem_image.mp xS
    have ti:τ i≠0:=(Finset.mem_filter.mp hi).2
    let w:=weightedEval y τ P
    have Wo:w∈annih U:=weightedEval_orthogonal B.clock B.orthogonal P
    have Xu:fiber y x u∈U:=fiber_mem B.clock x hu
    have Xw:fiber y x w∈annih U:=fiber_mem (diag_annih_invariant B.clock) x Wo
    have zz:fiber y x u + fiber y x w=0:=by
      ext j
      by_cases e:y j=x
      · have ff:v j=0:=off j (fun z=>xa (e.symm.trans z))
        have hh:=congrFun E j
        rw [Pi.add_apply,ff] at hh
        simpa only [Pi.add_apply,Pi.zero_apply,fiber,e,ite_true,w,y] using hh.symm
      · simp [fiber,e]
    have wu:fiber y x w∈U:=by
      have z:fiber y x w= -fiber y x u:=by
        calc
          fiber y x w = (fiber y x u+fiber y x w)-fiber y x u:=by abel
          _ = -fiber y x u:=by rw [zz,zero_sub]
      rw [z]
      exact U.neg_mem Xu
    have z:=congrFun (dot_orthogonal_inter_zero wu Xw) i
    simp only [fiber,ic,ite_true,Pi.zero_apply,w,weightedEval_apply] at z
    rw [eval_zero]
    exact (mul_eq_zero.mp z).resolve_right ti
  have eq:v=u:=by simpa [P0] using E
  rwa [eq]

theorem LocalLinearBand.base_annih (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17):U≤annih (treeSpace A (16-r)):=by
  rw [B.base]
  apply primitiveBack_annih ho
  rcases B.short with e|e <;> omega

/-- An actual forward vector preserves the early reverse subspace up to
the precise grade sum. This uses the full grade-eight annihilator only. -/
theorem LocalLinearBand.mul_base (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){j:ℕ}
    (pay:j+r≤8){f u:Vec K 26}(hf:f∈zeroSpace A j)(hu:u∈U):f*u∈U:=by
  classical
  let y:=mirror A
  have X:f*u=∑ a ∈ Clock.sites y,f*fiber y a u:=by rw [←Finset.mul_sum,sum_fibers]
  rw [X]
  apply U.sum_mem
  intro a _
  have ub:fiber y a u∈U:=fiber_mem B.clock a hu
  apply B.localized (a:=a)
  · apply mem_annih.mpr
    intro x hx
    have funpay:8+j≤16-r:=by omega
    have tot: x*f∈treeSpace A (16-r):=
      treeSpace_mono A funpay (treeSpace_mul hx (zeroSpace_le_treeSpace A j hf))
    have m:=mem_annih.mp (B.base_annih ho ub) _ tot
    rw [row_apply] at m ⊢
    convert m using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ring
  · intro i hi
    change y i≠a at hi
    simp only [Pi.mul_apply,fiber,hi,ite_false,mul_zero]

theorem LocalLinearBand.mul_head_orthogonal (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17){j:ℕ}(pay:j+r≤8)
    {f:Vec K 26}(hf:f∈zeroSpace A j):τ*f∈annih U:=by
  apply mem_annih.mpr
  intro u hu
  have ee:=mem_annih.mp B.orthogonal _ (B.mul_base ho pay hf hu)
  rw [row_apply] at ee ⊢
  convert ee using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  ring
end
end RKCert.Paired.ReverseHull

