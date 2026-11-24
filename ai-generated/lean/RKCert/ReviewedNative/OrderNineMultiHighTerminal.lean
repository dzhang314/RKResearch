module
public import RKCert.ReviewedNative.OrderNineMultiHighHead

@[expose] public section

/-! # The fully occupied eight-off/four-clean chart has a clean terminal. -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem profile_on_eval {A : Matrix (Fin s) (Fin s) K} (Q R : K[X]) {v : (Fin s→K)}
    (hv : evalNodes A Q + diag (g A) (evalNodes A R)=v) {i : Fin s}
    (hi : g A i=0) : Q.eval (nodes A i)=v i := by
  simpa [hi] using congrFun hv i

omit [CharZero K] in
theorem profile_off_eval {A : Matrix (Fin s) (Fin s) K} {P Q R : K[X]} {v : (Fin s→K)}
    (hv : evalNodes A Q + diag (g A) (evalNodes A R)=v)
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    {i : Fin s} (hi : g A i≠0) : (Q+P*R).eval (nodes A i)=v i := by
  simpa [hP i hi] using congrFun hv i

omit [CharZero K] in
theorem single_profile_on_unique {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {Q R : K[X]}
    (he : evalNodes A Q + diag (g A) (evalNodes A R) = Pi.single (Fin.last s) 1)
    (hdi : g A (Fin.last s)=0) (hc : nodes A (Fin.last s)=1) (j : Fin (s+1))
    (hj : g A j=0) (h1 : nodes A j=1) : j=Fin.last s := by
  by_contra hne
  have h := (profile_on_eval Q R he hj).symm.trans ((congrArg (fun x => Q.eval x)
    (h1.trans hc.symm)).trans (profile_on_eval Q R he hdi))
  simp [hne] at h

omit [CharZero K] in
theorem on_hull_times_head_probes {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) {P : K[X]} (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (k : ℕ) (pay : k+(cleanKnots A).card+3≤p) :
    probe A b k (evalNodes A (P*nodalHull (cleanKnots A)))=0 :=
  probe_head_product_zero ho fit _ (fun _ hx=>by rw [nodalHull_eval_of_mem hx,mul_zero])
    k (by rwa [natDegree_nodalHull])

omit [CharZero K] in
theorem gradeFiveState_injective_many_off {A : Matrix (Fin s) (Fin s) K}
    (M : 4≤(cleanKnots A).card) (N : 6≤(offKnots A).card)
    (P : K[X]) (dp : P.natDegree≤2)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (pn : ∀ x∈cleanKnots A,P.eval x≠0) :
    Function.Injective (gradeFiveStateMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  have dq : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dr : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  change evalNodes A Q+diag (g A) (evalNodes A R)=0 at hz
  have e : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (offKnots A) (fun x hx => by
      obtain ⟨i,di,rfl⟩ := mem_offKnots.mp hx
      simpa using profile_off_eval hz fit di)
    (by have := natDegree_add_le_of_degree_le dq (natDegree_mul_le_of_le dp dr); omega)
  have r0 : R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R (cleanKnots A) (fun x hx=>by
    obtain ⟨i,di,rfl⟩ := mem_cleanKnots.mp hx
    have q0 : Q.eval (nodes A i)=0 := by simpa using profile_on_eval Q R hz di
    have eq := congrArg (fun F : K[X] => F.eval (nodes A i)) e
    simp [q0,eval_add,eval_mul] at eq
    exact eq.resolve_left (pn _ hx)) (by omega)
  have q0 : Q=0 := by simpa [r0] using e
  exact Prod.ext (injective_ofFn 6 (q0.trans (ofFn_zero _).symm))
    (injective_ofFn 4 (r0.trans (ofFn_zero _).symm))

omit [CharZero K] in
theorem profile_terminal_on_of_large_off {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {P Q R : K[X]}
    (rank : (Q+P*R).natDegree+1<(offKnots A).card)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (profile : evalNodes A Q+diag (g A) (evalNodes A R)=Pi.single (Fin.last s) 1) :
    g A (Fin.last s)=0 := by
  by_contra hn
  let i := Fin.last s
  let T := RKCert.Paired.endpointErase (offKnots A) (nodes A i)
  have card : T.card+1=(offKnots A).card :=
    Finset.card_erase_add_one (mem_offKnots.mpr ⟨i,hn,rfl⟩)
  have eq : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T (fun x hx=>by
    obtain ⟨hxi,hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,hxj⟩ := mem_offKnots.mp hx
    have ji : j≠i := fun e => hxi (hxj.symm.trans (congrArg (nodes A) e))
    rw [←hxj,profile_off_eval profile fit hj]
    simp [ji,i]) (by omega)
  have h := profile_off_eval profile fit hn
  simp [eq] at h

omit [CharZero K] in
theorem order9_high_off_terminal {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (M : (cleanKnots A).card=4) (N : (offKnots A).card=8)
    (P : K[X]) (dp : P.natDegree≤2)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (pn : ∀ x∈cleanKnots A,P.eval x≠0) :
    g A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      ∀ j, g A j=0 → nodes A j=1 → j=Fin.last 11 := by
  have cap := order9_grade_five_upper ha ho
  have dr : finrank K (gradeFiveStateSpace A)=10 := by
    rw [gradeFiveStateSpace,LinearMap.finrank_range_of_inj
      (gradeFiveState_injective_many_off M.ge (by omega) P dp fit pn),
      Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]
  have eq : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  obtain ⟨_,hc,he,_⟩ := order9_rank_five_full_terminal ha ho (by rw [←eq,dr])
  obtain ⟨z,hz⟩ : Pi.single (Fin.last 11) 1∈gradeFiveStateSpace A := by
    rw [eq,←coordinate_as_single]; exact he
  rw [gradeFiveStateMap_eq_eval] at hz
  have d1 : (ofFn 6 z.1).natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have d2 : (ofFn 4 z.2).natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have d3 := natDegree_add_le_of_degree_le d1 (natDegree_mul_le_of_le dp d2)
  have hi := profile_terminal_on_of_large_off (by omega) fit hz
  exact ⟨hi,hc,fun j hj hj' => single_profile_on_unique hz hi hc j hj hj'⟩

theorem order9_high_off_two_root_tests {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (M : (cleanKnots A).card=4) (hF : zeroSpace A 4=band A 2)
    (P : K[X]) (dP : P.natDegree≤2) (p0 : P≠0)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (hq : g A (Fin.last 11)=0) (hc : nodes A (Fin.last 11)=1)
    (last : ∀ j,g A j=0 → nodes A j=1 → j=Fin.last 11) :
    ∃ h d : K, h≠0 ∧ d≠h ∧ (primitive (X*P)).eval h=0 ∧
      ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*
        ((X-C h)*((X-C d)*(C (P.leadingCoeff)⁻¹*P)))))=0 := by
  let T := RKCert.Paired.endpointErase (cleanKnots A) 1
  let S := RKCert.Paired.endpointErase T 0
  have one : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 11,hq,hc⟩
  have zero : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  have dT : T.card+1=(cleanKnots A).card := Finset.card_erase_add_one one
  have dS : S.card+1=T.card := Finset.card_erase_add_one zero
  have cS : S.card=2 := by omega
  let U : Set (Fin 12) := {j | g A j=0 ∧ nodes A j∈S}
  have hU : U.Nonempty := by
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (show 0<S.card by omega)
    have hOn := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    obtain ⟨j,hj,rfl⟩ := mem_cleanKnots.mp hOn
    exact ⟨j,hj,hx⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  obtain ⟨di,hiS⟩ := (show g A i=0 ∧ nodes A i∈S from hi)
  let h := nodes A i
  change h∈S at hiS
  have hn : h≠0 := (Finset.mem_erase.mp hiS).1
  let W := RKCert.Paired.endpointErase S h
  have dW : W.card+1=S.card := Finset.card_erase_add_one hiS
  obtain ⟨d,hd⟩:=Finset.card_pos.mp (show 0<W.card by omega)
  obtain ⟨hdh,hdS⟩ := Finset.mem_erase.mp hd
  have eS : ({h,d}:Finset K)=S := Finset.eq_of_subset_of_card_le (fun x hx => by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact hiS
    · exact hdS) (by simp [cS,Ne.symm hdh])
  have qHull : nodalHull (cleanKnots A)=(X^2-X)*((X-C h)*(X-C d)) := by
    rw [RKCert.Paired.nodalHull_two_endpoint_factor _ (zero_mem_cleanKnots ha) one]
    change (X^2-X)*nodalHull S=(X^2-X)*((X-C h)*(X-C d))
    rw [←eS,nodalHull,Finset.prod_insert (by simpa using hdh.symm),Finset.prod_singleton]
  refine ⟨h,d,hn,hdh,?_,?_⟩
  · apply on_primitive_zero_of_prefix ha hF di _ (natDegree_mul_le_of_le (by simp) dP)
      (diag (nodes A) (g A)) (clean_mixed_defect hF di)
    intro j hj
    by_cases qj : g A j=0
    · have j1 : nodes A j≠1 :=
        fun e => (ne_of_lt (hj.trans_le (Fin.le_last i))) (last j qj e)
      have j0 : nodes A j=0 := by
        by_contra jn
        have js : nodes A j∈S := Finset.mem_erase.mpr ⟨jn,
          Finset.mem_erase.mpr ⟨j1,mem_cleanKnots.mpr ⟨j,qj,rfl⟩⟩⟩
        exact hmin j ⟨qj,js⟩ hj
      simp [qj,j0]
    · simp [fit j qj]
  · intro k
    have mom := on_hull_times_head_probes ho fit k.val (by have := k.isLt; omega)
    let a := P.leadingCoeff
    have an : a≠0 := leadingCoeff_ne_zero.mpr p0
    have eq : P*nodalHull (cleanKnots A) =
          C a * ((X^2-X)*((X-C h)*((X-C d)*(C a⁻¹*P)))) := by
      calc
        P*nodalHull (cleanKnots A) =
          (X^2-X)*((X-C h)*((X-C d)*(C a*(C a⁻¹*P)))) := by
            rw [qHull,←mul_assoc (C a) (C a⁻¹) P,←map_mul,mul_inv_cancel₀ an,map_one,one_mul]
            ring
        _ = _ := by ring
    rw [eq] at mom
    have sc (R : K[X]) : evalNodes A (C a*R)=a • evalNodes A R := by ext j; simp
    rw [sc,map_smul,smul_eq_mul] at mom
    exact (mul_eq_zero.mp mom).resolve_left an
end RKResearch.Certified.Graded.MultiOff
