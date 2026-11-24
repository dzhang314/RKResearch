module

public import RKCert.ERKOrderNineHighOffHead

@[expose] public section

/-! # The actual terminal and two ordinary clean nodes of the high-off chart

At grade five the pair profile is already injective. This gives the
terminal column without any weighted contrast or degree-seven rank
argument. Both nonendpoint clean nodes are physically before the last row.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
theorem gradeFiveState_injective_many_off {A : Fin s → Fin s → K}
    (M : 4≤(onNodes A).card) (N : 6≤(supportedNodes A (qdef A)).card)
    (P : K[X]) (dp : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (pn : ∀ x∈onNodes A,P.eval x≠0) :
    Function.Injective (gradeFiveStateMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  have dq : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dr : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  change evalNodes A Q+diag (qdef A) (evalNodes A R)=0 at hz
  have e : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (supportedNodes A (qdef A)) (fun x hx => by
      obtain ⟨i,di,rfl⟩ := mem_supportedNodes.mp hx
      simpa using profile_off_eval hz fit di)
    (by have := natDegree_add_le_of_degree_le dq (natDegree_mul_le_of_le dp dr); omega)
  have r0 : R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R (onNodes A) (fun x hx=>by
    obtain ⟨i,di,rfl⟩ := mem_onNodes.mp hx
    have q0 : Q.eval (nodes A i)=0 := by simpa using profile_on_eval Q R hz di
    have eq := congrArg (fun F : K[X] => F.eval (nodes A i)) e
    simp [q0,eval_add,eval_mul] at eq
    exact eq.resolve_left (pn _ hx)) (by omega)
  have q0 : Q=0 := by simpa [r0] using e
  exact Prod.ext (injective_ofFn 6 (q0.trans (ofFn_zero _).symm))
    (injective_ofFn 4 (r0.trans (ofFn_zero _).symm))

omit [CharZero K] in
theorem profile_terminal_on_of_large_off {A : Fin (s+1) → Fin (s+1) → K}
    {P Q R : K[X]}
    (rank : (Q+P*R).natDegree+1<(supportedNodes A (qdef A)).card)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (profile : evalNodes A Q+diag (qdef A) (evalNodes A R)=Pi.single (Fin.last s) 1) :
    qdef A (Fin.last s)=0 := by
  by_contra hn
  let i := Fin.last s
  let T := endpointErase (supportedNodes A (qdef A)) (nodes A i)
  have card : T.card+1=(supportedNodes A (qdef A)).card :=
    Finset.card_erase_add_one (mem_supportedNodes.mpr ⟨i,hn,rfl⟩)
  have eq : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T (fun x hx=>by
    obtain ⟨hxi,hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,hxj⟩ := mem_supportedNodes.mp hx
    have ji : j≠i := fun e => hxi (hxj.symm.trans (congrArg (nodes A) e))
    rw [←hxj,profile_off_eval profile fit hj]
    simp [ji,i]) (by omega)
  have h := profile_off_eval profile fit hn
  simp [eq] at h

theorem order9_high_off_terminal {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (M : (onNodes A).card=4) (N : (supportedNodes A (qdef A)).card=8)
    (P : K[X]) (dp : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (pn : ∀ x∈onNodes A,P.eval x≠0) :
    qdef A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      ∀ j, qdef A j=0 → nodes A j=1 → j=Fin.last 11 := by
  obtain ⟨_,_,_,_,_,_,cap,_⟩ := order9_twelve_stage_chart ha ho
  have dr : finrank K (gradeFiveStateSpace A)=10 := by
    rw [gradeFiveStateSpace,LinearMap.finrank_range_of_inj
      (gradeFiveState_injective_many_off M.ge (by omega) P dp fit pn),
      Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]
  have eq : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  obtain ⟨_,hc,he,_,_,_⟩ := order9_rank_five_full ha ho (by rw [←eq,dr])
  obtain ⟨z,hz⟩ : Pi.single (Fin.last 11) 1∈gradeFiveStateSpace A := eq ▸ he
  rw [gradeFiveStateMap_eq_eval] at hz
  have d1 : (ofFn 6 z.1).natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have d2 : (ofFn 4 z.2).natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have d3 := natDegree_add_le_of_degree_le d1 (natDegree_mul_le_of_le dp d2)
  have hi := profile_terminal_on_of_large_off (by omega) fit hz
  exact ⟨hi,hc,fun j hj hj' => single_profile_on_unique hz hi hc j hj hj'⟩

/-- The exact two-endpoint product and chronological first-node primitive,
with the leading coefficient normalized once and used in both degree cases. -/
theorem order9_high_off_two_root_tests {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (M : (onNodes A).card=4) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (P : K[X]) (dP : P.natDegree≤2) (p0 : P≠0)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hq : qdef A (Fin.last 11)=0) (hc : nodes A (Fin.last 11)=1)
    (last : ∀ j,qdef A j=0 → nodes A j=1 → j=Fin.last 11) :
    ∃ h d : K, h≠0 ∧ d≠h ∧ (primitive (X*P)).eval h=0 ∧
      ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*
        ((X-C h)*((X-C d)*(C (P.leadingCoeff)⁻¹*P)))))=0 := by
  let T := endpointErase (onNodes A) 1
  let S := endpointErase T 0
  have one : (1:K)∈onNodes A := mem_onNodes.mpr ⟨Fin.last 11,hq,hc⟩
  have zero : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  have dT : T.card+1=(onNodes A).card := Finset.card_erase_add_one one
  have dS : S.card+1=T.card := Finset.card_erase_add_one zero
  have cS : S.card=2 := by omega
  let U : Set (Fin 12) := {j | qdef A j=0 ∧ nodes A j∈S}
  have hU : U.Nonempty := by
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<S.card by omega)
    have hOn := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    obtain ⟨j,hj,rfl⟩ := mem_onNodes.mp hOn
    exact ⟨j,hj,hx⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  obtain ⟨di,hiS⟩ := (show qdef A i=0 ∧ nodes A i∈S from hi)
  let h := nodes A i
  change h∈S at hiS
  have hn : h≠0 := (Finset.mem_erase.mp hiS).1
  let W := endpointErase S h
  have dW : W.card+1=S.card := Finset.card_erase_add_one hiS
  obtain ⟨d,hd⟩:=Finset.card_pos.mp (show 0<W.card by omega)
  obtain ⟨hdh,hdS⟩ := Finset.mem_erase.mp hd
  have eS : ({h,d}:Finset K)=S := Finset.eq_of_subset_of_card_le (fun x hx => by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact hiS
    · exact hdS) (by simp [cS,Ne.symm hdh])
  have qHull : nodalHull (onNodes A)=(X^2-X)*((X-C h)*(X-C d)) := by
    rw [nodalHull_two_endpoint_factor _ (zero_mem_onNodes ha) one]
    change (X^2-X)*nodalHull S=(X^2-X)*((X-C h)*(X-C d))
    rw [←eS,nodalHull,Finset.prod_insert (by simpa using hdh.symm),Finset.prod_singleton]
  refine ⟨h,d,hn,hdh,?_,?_⟩
  · apply on_primitive_zero_of_prefix ha hF di _ (natDegree_mul_le_of_le (by simp) dP)
      (diag (nodes A) (qdef A)) (on_row_quartic_conditions hF di).2.2
    intro j hj
    by_cases qj : qdef A j=0
    · have j1 : nodes A j≠1 :=
        fun e => (ne_of_lt (hj.trans_le (Fin.le_last i))) (last j qj e)
      have j0 : nodes A j=0 := by
        by_contra jn
        have js : nodes A j∈S := Finset.mem_erase.mpr ⟨jn,
          Finset.mem_erase.mpr ⟨j1,mem_onNodes.mpr ⟨j,qj,rfl⟩⟩⟩
        exact hmin j ⟨qj,js⟩ hj
      simp [qj,j0]
    · simp [fit j qj]
  · intro k
    have mom := on_hull_times_head_probes ho fit k.val (by have := k.isLt; omega)
    let a := P.leadingCoeff
    have an : a≠0 := leadingCoeff_ne_zero.mpr p0
    have eq : P*nodalHull (onNodes A) =
          C a * ((X^2-X)*((X-C h)*((X-C d)*(C a⁻¹*P)))) := by
      calc
        P*nodalHull (onNodes A) =
          (X^2-X)*((X-C h)*((X-C d)*(C a*(C a⁻¹*P)))) := by
            rw [qHull,←mul_assoc (C a) (C a⁻¹) P,←map_mul,mul_inv_cancel₀ an,map_one,one_mul]
            ring
        _ = _ := by ring
    rw [eq] at mom
    have sc (R : K[X]) : evalNodes A (C a*R)=a • evalNodes A R := by ext j; simp
    rw [sc,map_smul,smul_eq_mul] at mom
    exact (mul_eq_zero.mp mom).resolve_left an

end RKCert.Paired
