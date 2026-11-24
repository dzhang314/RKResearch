module

public import RKCert.ERKLowLobatto

@[expose] public section

/-! # The five-off and seven-or-more-off branches at explicit order eight -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- In the five-on quadrature a terminal polynomial of degree four is
the four nonterminal nodes' hull, normalized to one at the terminal. -/
theorem terminal_profile_polynomial_eq_hull {A : Fin 10 → Fin 10 → K} {Q R : K[X]}
    (hv : evalNodes A Q + diag (qdef A) (evalNodes A R) = Pi.single (Fin.last 9) 1)
    (hQ : Q.natDegree ≤ 4) (hc : nodes A (Fin.last 9)=1) (hi : qdef A (Fin.last 9)=0)
    (hM : (onNodes A).card=5) :
    ∃ a : K, a≠0 ∧ Q=C a * nodalHull ((onNodes A).erase 1) := by
  let T := (onNodes A).erase 1
  let H := nodalHull T
  let a := (H.eval 1)⁻¹
  have hH : H.eval 1≠0 := nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)
  have ht : T.card+1=(onNodes A).card := Finset.card_erase_add_one
    (mem_onNodes.mpr ⟨Fin.last 9,hi,hc⟩)
  have hd : H.natDegree=4 := by rw [show H.natDegree=T.card from natDegree_nodalHull _]; omega
  have hd' := (natDegree_C_mul_le a H).trans hd.le
  refine ⟨a,inv_ne_zero hH,?_⟩
  change Q=C a*H
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (onNodes A) _ (by omega)
  intro x hx
  by_cases h : x=1
  · rw [h,eval_mul,eval_C,inv_mul_cancel₀ hH]
    have hOne := profile_on_eval Q R hv hi
    rw [hc] at hOne
    simpa using hOne
  · obtain ⟨j,hj,hjc⟩ := mem_onNodes.mp hx
    have hne : j≠Fin.last 9 := fun he => h (hjc.symm.trans ((congrArg (nodes A) he).trans hc))
    rw [←hjc,profile_on_eval Q R hv hj,eval_mul,eval_C,hjc,
      nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨h,hx⟩)]
    change j≠(9 : Fin 10) at hne
    simp [hne]

/-- Five off states are excluded by the genuine terminal coordinate and
first-clean-row Lobatto equation. No ordering of the field is needed. -/
theorem order8_no_five_off_nodes {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    (supportedNodes A (qdef A)).card≠5 := by
  intro hN
  obtain ⟨hb,_,hc,hE,_,h3,h4,_,_,_,_⟩ := order8_ten_stage_chart ha ho
  obtain ⟨P,hPd,hPn,_,hF,hP⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨Q,R,hQd,hRd,hv⟩ := treeSpace_four_profile hE hF
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  have hState : Pi.single (Fin.last 9) 1 ∈ onOffSpace A :=
    hv ▸ pairProfile_mem_onOffSpace hP Q R
  have hi := on_of_state_single hState hb hoff
  have h1 : (1:K)∈onNodes A := mem_onNodes.mpr ⟨Fin.last 9,hi,hc⟩
  have hM := order8_five_on_of_middle_offs ha ho (Or.inr hN)
  have hS := order8_nodal_lobatto (s:=9) ha ho hM h1 hoff
  obtain ⟨a,ha0,hQ⟩ := terminal_profile_polynomial_eq_hull hv hQd hc hi hM
  have h0 : (0:K)∈(onNodes A).erase 1 := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  rw [nodalHull_erase_factor _ h0,hS,map_zero,sub_zero] at hQ
  have hL : (lobattoCubic : K[X])≠0 := by
    intro hz; have hd := lobattoCubic_degree (K:=K); simp [hz] at hd
  have hQd' : Q.natDegree=4 := by
    rw [hQ,natDegree_C_mul ha0,natDegree_mul X_ne_zero hL,natDegree_X,lobattoCubic_degree]
  have hOff := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (Q+P*R)
    (supportedNodes A (qdef A)) (fun x hx => by
      obtain ⟨j,hj,rfl⟩ := mem_supportedNodes.mp hx
      have hn : j≠Fin.last 9 := fun he => hj (he ▸ hi)
      rw [profile_off_eval hv hP hj]
      change j≠(9 : Fin 10) at hn
      simp [hn]) (by
        have hd := natDegree_add_le_of_degree_le hQd (natDegree_mul_le_of_le hPd hRd)
        omega)
  have hD : Q=P*(-R) := by rw [mul_neg,eq_neg_iff_add_eq_zero]; exact hOff
  have hD' := natDegree_mul_le (p:=P) (q:=-R)
  rw [←hD,natDegree_neg,hQd'] at hD'
  have hP2 : P.natDegree=2 := by omega
  have hP0 := (first_nonzero_on_forces_head_shape ha hF hPd hPn hP
    (exists_nonzero_on_of_card (by omega : 2 ≤ (onNodes A).card))).1
  have hRv : (-R).eval 0=0 := by
    have hz := congrArg (fun V : K[X] => V.eval (0:K)) hD
    have hQ0 : Q.eval 0=0 := by rw [hQ]; simp
    rw [hQ0,eval_mul] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left hP0
  obtain ⟨W,hW⟩ := Polynomial.X_dvd_iff.mpr ((coeff_zero_eq_eval_zero (-R)).trans hRv)
  have hcan : C a*lobattoCubic = P*W := by
    apply mul_left_cancel₀ (X_ne_zero : (X:K[X])≠0)
    rw [hQ,hW] at hD
    calc
      _ = C a*(X*lobattoCubic) := by ring
      _ = P*(X*W) := hD
      _ = _ := by ring
  have hdiv : P∣lobattoCubic := by
    refine ⟨C a⁻¹*W,?_⟩
    calc
      _ = C a⁻¹*(C a*lobattoCubic) := by rw [←mul_assoc,←map_mul,inv_mul_cancel₀ ha0,map_one,one_mul]
      _ = _ := by rw [hcan]; ring
  obtain ⟨u,t,ht,hfac⟩ := lobatto_divisor_linear_factor hP2 hdiv
  have huS : u∈((onNodes A).erase 1).erase 0 := by
    by_contra h
    exact nodalHull_eval_ne_zero_of_notMem h (hS.symm ▸ lobatto_isRoot_of_linear hfac)
  have huO := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huS)
  exact lobatto_physical_factor_impossible (s:=9) ha hF hPd hP
    (single_profile_on_unique hv hi hc) (on_root_or_endpoints hS) huO ht hfac

/-- Seven or more off states cannot meet the order-eight moment budget,
including when the individual or aggregate off weights are not zero. -/
theorem order8_off_nodes_lt_seven {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    (supportedNodes A (qdef A)).card < 7 := by
  by_contra! hN
  obtain ⟨_,_,hc,hE,_,h3,h4,_,_,_,_⟩ := order8_ten_stage_chart ha ho
  obtain ⟨P,hPd,hPn,_,hF,hP⟩ := two_curve_head h3 h4 (by omega)
  have hCard := on_off_card_le A
  let T := onNodes A
  let H := nodalHull T
  have hH : H.natDegree=T.card := natDegree_nodalHull _
  have hHn : H≠0 := (monic_nodalHull T).ne_zero
  have hT0 : (0:K)∈T := zero_mem_onNodes (s:=9) ha
  change T.card+(supportedNodes A (qdef A)).card ≤ 10 at hCard
  have hM : T.card=3 := by
    by_contra! hM'
    have hd : (P*H).natDegree≤4 := by
      rw [natDegree_mul hPn hHn,hH]; omega
    have hz : (P*H).eval 0=0 := by rw [eval_mul,nodalHull_eval_of_mem hT0,mul_zero]
    have hMom (k : Fin 4) : probe A b k.val (evalNodes A (P*H))=0 := by
      have hp : k.val+T.card+3≤8 := by have := k.isLt; omega
      exact on_hull_times_head_probes ho hP k.val hp
    exact mul_ne_zero hPn hHn (zero_of_anchored_profile_probes ho 4 (by decide) (P*H) hd hz hMom)
  obtain ⟨Q,R,hQd,hRd,hv⟩ := treeSpace_four_profile hE hF
  have hi := terminal_on_of_six_off (s:=9) hv hP hPd hQd hRd (by omega)
  have h1 : (1:K)∈T := mem_onNodes.mpr ⟨Fin.last 9,hi,hc⟩
  let S := (T.erase 1).erase 0
  have hc1 : (T.erase 1).card+1=T.card := Finset.card_erase_add_one h1
  have hc0 : S.card+1=(T.erase 1).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one,hT0⟩)
  obtain ⟨u,huS⟩ := Finset.card_eq_one.mp (by omega : S.card=1)
  have hHull : H=(X^2-X)*(X-C u) := by
    rw [show H=nodalHull T from rfl,nodalHull_two_endpoint_factor T hT0 h1]
    change (X^2-X)*nodalHull S=_
    rw [huS]
    simp [nodalHull]
  let L := P*(X-C u)
  have hEq : (X^2-X)*L=P*H := by rw [hHull]; dsimp [L]; ring
  have hLd : L.natDegree≤3 := natDegree_mul_le_of_le hPd (natDegree_X_sub_C_le u)
  have hL := beta_cubic_from_actual_probes ho (by decide) L hLd (fun k => by
    rw [hEq]
    have hp : k.val+T.card+3≤8 := by have := k.isLt; omega
    exact on_hull_times_head_probes ho hP k.val hp)
  let a := L.coeff 3
  have ha0 : a≠0 := by
    intro h
    change L=C a*lobattoCubic at hL
    rw [h,map_zero,zero_mul] at hL
    exact mul_ne_zero hPn (X_sub_C_ne_zero u) hL
  have hfac : lobattoCubic = (X-C u)*(C a⁻¹*P) := by
    calc
      _ = C a⁻¹*(C a*lobattoCubic) := by rw [←mul_assoc,←map_mul,inv_mul_cancel₀ ha0,map_one,one_mul]
      _ = C a⁻¹*L := by rw [←hL]
      _ = _ := by dsimp [L]; ring
  have huS' : u∈S := by rw [huS]; simp
  have huO := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huS')
  have hOn (x : K) (hx : x∈onNodes A) : x=0 ∨ x=1 ∨ lobattoCubic.eval x=0 := by
    by_cases h0 : x=0
    · exact Or.inl h0
    by_cases h1 : x=1
    · exact Or.inr (Or.inl h1)
    have hx' : x∈S := Finset.mem_erase.mpr ⟨h0,Finset.mem_erase.mpr ⟨h1,hx⟩⟩
    rw [huS,Finset.mem_singleton] at hx'
    rw [hx']
    exact Or.inr (Or.inr (lobatto_isRoot_of_linear hfac))
  exact lobatto_physical_factor_impossible (s:=9) ha hF hPd hP
    (single_profile_on_unique hv hi hc) hOn huO (inv_ne_zero ha0) hfac

theorem order8_off_count_one_or_four {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8) :
    let n := (supportedNodes A (qdef A)).card
    n=1 ∨ n=4 := by
  have h := order8_off_count_chart ha ho
  dsimp only at h ⊢
  have h5 := order8_no_five_off_nodes ha ho
  have h7 := order8_off_nodes_lt_seven ha ho
  omega

end RKCert.Paired

