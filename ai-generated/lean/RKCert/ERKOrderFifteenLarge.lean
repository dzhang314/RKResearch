module
public import RKCert.ERKOrderFifteenHead
public import RKCert.ERKOrderFifteenLateKnot

@[expose] public section

/-! # The true high-r chart is impossible over every characteristic-zero field. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d a r : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G P : K[X]}

theorem fifteen_factor_of_profile (S:Saturated A b 7 1) (M:Margin A b 7 1 d)
    (C:OddSevenChart A d a r U w G)
    (dis:∀ i,Live U i→w i=0) (pn:P≠0)
    (pdeg:P.natDegree+2*r-2<headLen 7 a r 10)
    (wval:∀ i,w i≠0→w i=P.eval (nodes A i)) :
    ∃ Q:K[X],G=P*Q ∧ Q.natDegree=r+2 ∧ P.natDegree+r+1=a := by
  let c:=nodes A
  have gd := C.meshDegree
  have alo := C.aLo
  have ale := C.aLe
  have r2 := C.marked.rTwo
  have cnt := C.sites
  unfold headLen at cnt pdeg
  have gn : G≠0 := by intro e;rw [e,natDegree_zero] at gd;omega
  have gPaid := C.meshPaid
  rw [C.marked.edge] at gPaid
  obtain ⟨v,hv,Q,qsmall,e⟩:=exists_head_poly gPaid
  have qd : Q.natDegree≤r+2 := by
    by_cases h:Q=0
    · simp [h]
    · have l:Q.natDegree<r+(7-4) := (natDegree_lt_iff_degree_lt h).mpr qsmall
      omega
  have pqd := natDegree_mul_le (p:=P) (q:=Q)
  have eq : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
    · exact degree_le_natDegree.trans_lt (by
        exact_mod_cast (show G.natDegree<(headSites (nodes A) w).card by omega))
    · exact degree_le_natDegree.trans_lt (by
        exact_mod_cast (show (P*Q).natDegree<(headSites (nodes A) w).card by omega))
    · intro x hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
      have wi := (Finset.mem_filter.mp hi).2
      have vi : v i=0 := by by_contra nz; exact wi (dis i ⟨v,hv,nz⟩)
      have ei := e i
      rw [evalNodes_apply,vi,zero_add,wval i wi,mul_comm] at ei
      simpa [c] using ei
  have qn : Q≠0 := fun z=>gn (by rw [eq,z,mul_zero])
  have degsum := congrArg Polynomial.natDegree eq
  rw [gd,natDegree_mul pn qn] at degsum
  have exact_deg : Q.natDegree=r+2 := by
    by_cases seven:a=7
    · omega
    by_contra nz
    have qlt : Q.natDegree<r+2 := by omega
    have wq : weightedEval (nodes A) w Q∈chain (diag (nodes A)) U w (r+2) :=
      weighted_chain Q qlt
    have ve := ((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+2)).mp le_rfl).1 hv
    have ge : evalNodes A G=v+weightedEval (nodes A) w Q := by
      ext i
      simpa only [Pi.add_apply,weightedEval_apply] using e i
    have gm : evalNodes A G∈defectPlus A d 7 := by
      rw [C.marked.paid 7 (by decide) (by decide),show r+(7-5)=r+2 by omega,ge]
      exact Submodule.add_mem _ ve wq
    exact gn (separated_plus S M G (by omega) gm)
  have sum := congrArg Polynomial.natDegree eq
  rw [natDegree_mul pn qn,exact_deg,gd] at sum
  exact ⟨Q,eq,exact_deg,by omega⟩

omit [CharZero K] in
theorem marked_weighted_six (H:MarkedHead A 7 d r U w) (R:K[X]) (hr:R.natDegree≤r) :
    weightedEval (nodes A) w R∈defectPlus A d 6 := by
  have rTwo:=H.rTwo
  apply weighted_paid
  intro k hk
  have dK := le_natDegree_of_mem_supp k hk
  by_cases ck:k<r
  · exact Fplus_mono A d (by decide) (marked_power H (by decide) ck)
  have ek:r-1+1=k := by omega
  have p := Fplus_power (marked_power H (by decide) (k:=r-1) (by omega)) 1
  change (diag (nodes A)^1) ((diag (nodes A)^(r-1)) w)∈defectPlus A d 6 at p
  rw [←ek,pow_succ']
  simpa only [pow_one,mul_apply_eq_comp] using p

theorem no_large_fifteen_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15)
    (S:Saturated A b 7 1) (M:Margin A b 7 1 d) (C:OddSevenChart A d a r U w G)
    (large:3≤r) : False := by
  obtain ⟨v,P,C',alg,dis,pn,degree,repr⟩:=fifteen_large_profile ha ho S M C large
  obtain ⟨Q,_,_,de⟩:=fifteen_factor_of_profile S M C' dis pn degree repr
  have ale := C'.aLe
  have Pr : SevenProfile A r U v P := ⟨alg,dis,pn,by omega,repr⟩
  have pay : defectPlus A d 7≤chain (diag (nodes A)) U v (r+2) := by
    rw [C'.marked.paid 7 (by decide) (by decide),show r+(7-5)=r+2 by omega]
  have source := physical_knot_of_paid (j:=6) (m:=3) (n:=r+2)
    ha S M C'.marked Pr (by decide) (by omega) (C'.marked.core.trans (Fplus_mono A d (by decide)))
    (fun T ht=>marked_weighted_six C'.marked T (by omega)) pay
  obtain ⟨u,y,J⟩:=five_tests_from_paid_knot source
  exact pn (cubic_no_profile (by decide) J (by omega))

/-- On any hypothetical ordered 22-stage order-fifteen tableau, the original
midpoint can be chosen with exactly two head coordinates, a marked terminal,
and the terminal column entering at grade eight. -/
theorem order15_only_early_terminal [LinearOrder K] [IsStrictOrderedRing K]
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 15) (sz:s+1≤22) :
    ∃ a U w G,Saturated A b 7 1 ∧ Margin A b 7 1 1 ∧ OddSevenChart A 1 a 2 U w G ∧
      terminal (K:=K) s∈treeSpace A 8 := by
  obtain ⟨d,a,r,U,w,G,S,M,C⟩:=at_order_fifteen ha ho sz
  have r2:=C.marked.rTwo
  have re:r=2 := by by_contra nz;exact no_large_fifteen_head ha ho S M C (by omega)
  subst r
  obtain ⟨rfl,term⟩:=order15_rank_two_marked_terminal ha ho S M C
  exact ⟨a,U,w,G,S,M,C,term⟩

end RKCert.Paired.FiniteMidpoint
