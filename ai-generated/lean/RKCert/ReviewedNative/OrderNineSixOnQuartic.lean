module
public import RKCert.ReviewedNative.OrderNineSixOnEarly

@[expose] public section

/-! # Two quartic native null-profile remainders at the early physical rows -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s : ℕ}

theorem degree_three_kernel_on_five_rows {A : Matrix (Fin s) (Fin s) K} (e : Fin 5→Fin s)
    {i j : Fin 5} (gi : g A (e i)≠0) (gj : g A (e j)≠0)
    (ne : nodes A (e i)≠nodes A (e j)) :
    ∃ Q R : K[X], Q≠0 ∧ Q.natDegree≤3 ∧ R.natDegree≤1 ∧
      ∀ k : Fin 5, (evalNodes A Q+diag (g A) (evalNodes A R)) (e k)=0 := by
  let f : ((Fin 4→K)×(Fin 2→K)) →ₗ[K] (Fin 5→K) :=
    (RKCert.Paired.restrictCol e).comp ((coeffEval A 3).coprod ((diag (g A)).comp (coeffEval A 1)))
  have hI : ¬Function.Injective f := by
    intro h
    have dim := LinearMap.finrank_le_finrank_of_injective h
    norm_num [Module.finrank_prod,Module.finrank_fin_fun ] at dim
  have nn : ¬ ∀z, f z=0 → z=0 := fun he =>
    hI ((injective_iff_map_eq_zero f).mpr he)
  push Not at nn
  obtain ⟨z,hz,zn⟩ := nn
  let Q := ofFn 4 z.1
  let R := ofFn 2 z.2
  have dQ : Q.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dR : R.natDegree≤1 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have vv (k : Fin 5) : (evalNodes A Q+diag (g A) (evalNodes A R)) (e k)=0 := by
    have h := congrFun hz k
    rw [ofFn_eval A 3,ofFn_eval A 1]
    exact h
  refine ⟨Q,R,?_,dQ,dR,vv⟩
  intro q0
  have h1 : R.eval (nodes A (e i))=0 := (mul_eq_zero.mp (by simpa [q0] using vv i)).resolve_left gi
  have h2 : R.eval (nodes A (e j))=0 := (mul_eq_zero.mp (by simpa [q0] using vv j)).resolve_left gj
  have r0 : R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R
    ({nodes A (e i),nodes A (e j)} : Finset K) (fun x hx => by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl <;> assumption) (by rw [Finset.card_pair ne]; omega)
  exact zn (Prod.ext (injective_ofFn 4 (q0.trans (ofFn_zero _).symm))
    (injective_ofFn 2 (r0.trans (ofFn_zero _).symm)))

theorem four_off_residue_of_paid_primitive [CharZero K] {A : Matrix (Fin s) (Fin s) K}
    (hF : zeroSpace A 4=band A 2) {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (Q R : K[X]) (dQ : Q.natDegree≤3) (dR : R.natDegree≤1)
    (n : ¬P∣primitive Q) (S : Finset K) (card : S.card=4)
    (off : ∀ x∈S, ∃ i, g A i≠0 ∧ nodes A i=x ∧
      mat A (evalNodes A Q+diag (g A) (evalNodes A R)) i=0) :
    ∃ a : K,a≠0 ∧ P∣primitive Q-C a*nodalHull S := by
  obtain ⟨T,dT,h⟩ := degree_three_actual_mat_profile hF Q R dQ dR
  have dq : (primitive Q).natDegree≤4 := primitive_natDegree_le dQ
  have dt : (P*T).natDegree≤4 := by have e := natDegree_mul_le_of_le dP dT; exact e
  obtain ⟨a,ea⟩ := RKCert.Paired.polynomial_scalar_hull S (primitive Q+P*T)
    ((natDegree_add_le_of_degree_le dq dt).trans_eq card.symm) (fun x hx=>by
      obtain ⟨i,g,rfl,z⟩ := off x hx
      rw [profile_off_eval h.symm fit g]
      exact z)
  have an : a≠0 := by
    intro z
    rw [z,map_zero,zero_mul] at ea
    exact n ⟨-T,by rw [mul_neg,eq_neg_iff_add_eq_zero]; exact ea⟩
  exact ⟨a,an,⟨-T,by linear_combination ea⟩⟩


variable [LinearOrder K] [IsStrictOrderedRing K]
def firstSixPrefix (i : Fin 6) : Fin 10 := Fin.castLE (by decide) i

noncomputable def firstSixOff (A : Matrix (Fin 12) (Fin 12) K) : Finset K :=
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  ((Finset.univ : Finset (Fin 6)).filter fun i => OneOff.g A (lowPrefix10 (firstSixPrefix i))≠0).image
    (fun i=>nodes A (lowPrefix10 (firstSixPrefix i)))

/-- The first six literal stages have four distinct off abscissas. Their
hull has the exact indicated primitive remainder, in both of the
chronological placements of the physical first nonzero clean row. -/
theorem order9_actual_five_six_quartic_remainders
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=6)
    (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (dP : P.natDegree=2) (pn : P≠0)
    (fit : ∀ i,OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i)
    (fg : ActualSixOnFG A P) :
    let h := nodes A (lowPrefix10 fg.first)
    let R := nodalHull (firstSixOff A)
    (firstSixOff A).card=4 ∧
      ((fg.first.val=4 ∧ ∃ a : K,a≠0 ∧ P∣R-C a*(X^2*(X-C h)^2)) ∨
       (fg.first.val=5 ∧ ∃ a : K,a≠0 ∧ P∣R-C a*primitive (X*P))) := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  dsimp only
  let c := nodes A∘lowPrefix10
  let g := OneOff.g A∘lowPrefix10
  let h := c fg.first
  have h0 : h≠0 := fg.first_nonzero
  have hOn : g fg.first=0 := fg.first_clean
  have zD : g 0=0 := origin_zeroSpace ha 2 (mDef_mem A 1)
  have zC : c 0=0 := by
    change (∑ j,A (0:Fin 12) j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  obtain ⟨_,_,_,_,_,_,last⟩ := order9_five_six_stage_chart ha ho hN hM fit
  obtain ⟨bij,_,_,_⟩ := order9_five_six_ten_distinct_prefix ha ho hN hM
  change Function.Bijective (fun i : Fin 10=>lowNonterminalStateAt ha (lowPrefix10 i)) at bij
  have clean1 (i : Fin 10) (hi:g i=0) : c i≠1 :=
    first_prefix_clean_value_ne_one last i hi
  have eqOn {i j : Fin 10} (gi : g i=0) (gj : g j=0) (e:c i=c j) : i=j :=
    bij.1 ((lowNonterminalState_eq_iff ha (clean1 i) (clean1 j)).mpr
      (lowState_eq_iff.mpr ⟨by change (g i=0 ↔ g j=0); rw [gi,gj],e⟩))
  have eqOff {i j : Fin 10} (gi : g i≠0) (gj : g j≠0) (e:c i=c j) : i=j :=
    bij.1 ((lowNonterminalState_eq_iff ha (clean1 i) (clean1 j)).mpr
      (lowState_eq_iff.mpr ⟨by change (g i=0 ↔ g j=0); simp [gi,gj],e⟩))
  have earlier (i : Fin 10) (hi : i<fg.first) (i0 : i≠0) : g i≠0 :=
    fun gi => i0 (eqOn gi zD ((fg.first_min i hi gi).trans zC.symm))
  have p0 := (first_nonzero_on_forces_head_shape ha hF dP.le pn fit
    ⟨_,fg.first_clean,fg.first_nonzero⟩).1
  obtain ⟨_,non⟩ := order9_five_six_remainder ha ho hN hM hF P dP.le fit
  have ph : P.eval h≠0 :=
    non _ (Finset.mem_erase.mpr ⟨clean1 _ hOn,mem_cleanKnots.mpr ⟨_,hOn,rfl⟩⟩)
  have places := order9_actual_quadratic_first_on_fifth_or_sixth ha ho hM hN hF dP pn fit fg
  let M := (Finset.univ : Finset (Fin 6)).filter (fun j=>g (firstSixPrefix j)≠0)
  let S := firstSixOff A
  have cardEq (shape : ∀j : Fin 6,g (firstSixPrefix j)=0 ↔ firstSixPrefix j=0 ∨ firstSixPrefix j=fg.first) :
      S.card=4 := by
    have hLt : fg.first.val<6 := by omega
    let hf : Fin 6 := ⟨fg.first.val,hLt⟩
    have he : firstSixPrefix hf=fg.first := Fin.ext rfl
    have hn : (0:Fin 6)≠hf := by
      intro x
      have v := congrArg Fin.val x
      change 0=fg.first.val at v
      omega
    have filt : Finset.univ.filter (fun j : Fin 6=>g (firstSixPrefix j)=0)={0,hf} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,shape,Finset.mem_insert,Finset.mem_singleton]
      rw [←he]
      constructor
      · rintro (e|e)
        · exact Or.inl (Fin.ext (congrArg (fun x : Fin 10=>x.val) e))
        · exact Or.inr (Fin.ext (congrArg (fun x : Fin 10=>x.val) e))
      · rintro (rfl|rfl) <;> simp [firstSixPrefix]
    have nM : M.card=4 := by
      have e := Finset.card_filter_add_card_filter_not
        (s:=(Finset.univ : Finset (Fin 6))) (p:=fun i=>g (firstSixPrefix i)=0)
      change (Finset.univ.filter (fun j : Fin 6=>g (firstSixPrefix j)=0)).card+M.card=6 at e
      rw [filt,Finset.card_pair hn] at e
      omega
    have ij : Set.InjOn (fun i : Fin 6=>c (firstSixPrefix i)) (M:Set (Fin 6)) := by
      intro i hi j hj eq
      have hi' : i∈Finset.univ.filter (fun x : Fin 6=>g (firstSixPrefix x)≠0) := hi
      have hj' : j∈Finset.univ.filter (fun x : Fin 6=>g (firstSixPrefix x)≠0) := hj
      have e := eqOff (Finset.mem_filter.mp hi').2 (Finset.mem_filter.mp hj').2 eq
      exact Fin.ext (congrArg (fun x : Fin 10=>x.val) e)
    change (M.image (fun i=>c (firstSixPrefix i))).card=4
    rw [Finset.card_image_of_injOn ij,nM]
  have runResidue (Q R : K[X]) (dQ : Q.natDegree≤3) (dR : R.natDegree≤1)
      (n : ¬P∣primitive Q) (card : S.card=4)
      (vz : ∀ j : Fin 12,j.val<5 → (evalNodes A Q+diag (OneOff.g A) (evalNodes A R)) j=0) :
      ∃ a : K,a≠0 ∧ P∣primitive Q-C a*nodalHull S := by
    apply four_off_residue_of_paid_primitive hF dP.le fit Q R dQ dR n S card
    intro x hx
    change x∈M.image (fun i=>c (firstSixPrefix i)) at hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    let idx := lowPrefix10 (firstSixPrefix j)
    refine ⟨idx,(Finset.mem_filter.mp hj).2,rfl,?_⟩
    exact causal_mat ha idx _ (fun k hk=>vz k (by have v:j.val<6:=j.isLt; change k.val<j.val at hk; omega))
  rcases places with p4|p5
  · let f (j : Fin 5) : Fin 10 := Fin.castLE (by decide) j
    let e (j : Fin 5) : Fin 12 := lowPrefix10 (f j)
    have g1 : OneOff.g A (e 1)≠0 := earlier (f 1) (by change 1<fg.first.val; omega) (by decide)
    have g2 : OneOff.g A (e 2)≠0 := earlier (f 2) (by change 2<fg.first.val; omega) (by decide)
    have d12 : nodes A (e 1)≠nodes A (e 2) := fun v =>
      (by decide : f 1≠f 2) (eqOff g1 g2 v)
    obtain ⟨Q,R,qn,dQ,dR,z⟩ := degree_three_kernel_on_five_rows e g1 g2 d12
    let V := evalNodes A Q+diag (OneOff.g A) (evalNodes A R)
    have zV (j : Fin 12) (hj : j.val<5) : V j=0 := by
      let k : Fin 5 := ⟨j.val,hj⟩
      have he : e k=j := Fin.ext rfl
      simpa only [he] using z k
    have Q0 : Q.eval 0=0 := by
      have x := z 0
      change Q.eval (c 0)+g 0*R.eval (c 0)=0 at x
      simpa [zC,zD] using x
    have Qh : Q.eval h=0 := by
      have x := zV (lowPrefix10 fg.first) (by change fg.first.val<5; omega)
      change Q.eval h+g fg.first*R.eval h=0 at x
      simpa [hOn] using x
    obtain ⟨U,_,m⟩ := degree_three_actual_mat_profile hF Q R dQ dR
    have hp : (primitive Q).eval h=0 := by
      let j := lowPrefix10 fg.first
      have w : mat A V j=0 := causal_mat ha j V (fun k hk=>zV k (by change k.val<fg.first.val at hk; omega))
      have eq := profile_on_eval (primitive Q) U m.symm hOn
      exact eq.trans w
    rw [←scalar_primitive Q] at hp
    obtain ⟨a,an,eP⟩ := RKCert.Paired.cubic_zero_at_origin_and_node_primitive Q dQ qn h0 Q0 Qh hp
    rw [scalar_primitive Q] at eP
    have no5 : g 5≠0 := by
      intro gn
      have nh : c 5≠h := fun e => (show (5:Fin 10)≠fg.first from by
        intro v; have x:=congrArg Fin.val v; change 5=fg.first.val at x; omega) (eqOn gn hOn e)
      have n0 : c 5≠0 := fun e => (by decide : (5:Fin 10)≠0) (eqOn gn zD (e.trans zC.symm))
      have eq := profile_on_eval (primitive Q) U m.symm gn
      have mz : mat A V (lowPrefix10 5)=0 := causal_mat ha _ V (fun j hj=>zV j hj)
      have hz := eq.trans mz
      rw [eP,eval_mul,eval_C,eval_mul,eval_pow,eval_X,eval_pow,eval_sub,eval_X,eval_C] at hz
      exact (mul_ne_zero an (mul_ne_zero (pow_ne_zero _ n0) (pow_ne_zero _ (sub_ne_zero.mpr nh)))) hz
    have shape (j : Fin 6) : g (firstSixPrefix j)=0 ↔ firstSixPrefix j=0 ∨ firstSixPrefix j=fg.first := by
      constructor
      · intro q
        by_cases z0 : firstSixPrefix j=0
        · exact Or.inl z0
        · by_cases zf : firstSixPrefix j=fg.first
          · exact Or.inr zf
          · have v4 : j.val≠4 := fun v => zf (Fin.ext (v.trans p4.symm))
            have vv : j.val<6 := j.isLt
            by_cases v5 : j.val=5
            · exact False.elim (no5 ((show firstSixPrefix j=(5:Fin 10) from Fin.ext v5) ▸ q))
            · exact False.elim (earlier _ (by change j.val<fg.first.val; omega) z0 q)
      · rintro (e0|ef)
        · rwa [e0]
        · rwa [ef]
    have cs := cardEq shape
    have nd : ¬P∣primitive Q := by
      rw [eP]
      exact RKCert.Paired.positive_degree_head_not_dvd_double_square (by omega) an p0 ph
    obtain ⟨k,kn,ev⟩ := runResidue Q R dQ dR nd cs zV
    rw [eP] at ev
    exact ⟨cs,Or.inl ⟨p4,RKCert.Paired.normalize_quartic_residue an kn ev⟩⟩
  · have shape (j : Fin 6) : g (firstSixPrefix j)=0 ↔ firstSixPrefix j=0 ∨ firstSixPrefix j=fg.first := by
      constructor
      · intro q
        by_cases z0 : firstSixPrefix j=0
        · exact Or.inl z0
        · by_cases zf : firstSixPrefix j=fg.first
          · exact Or.inr zf
          · have v5 : j.val≠5 := fun v=>zf (Fin.ext (v.trans p5.symm))
            have vv := j.isLt
            exact False.elim (earlier _ (by change j.val<fg.first.val; omega) z0 q)
      · rintro (e0|ef)
        · rwa [e0]
        · rwa [ef]
    have cs := cardEq shape
    let Q := -(X*P)
    let V := evalNodes A Q+diag (OneOff.g A) (evalNodes A X)
    have eqJ : primitive Q=C (-1:K)*primitive (X*P) := by simp [Q]
    have zv (j : Fin 12) (hj : j.val<5) : V j=0 := by
      by_cases off : OneOff.g A j=0
      · let k : Fin 10 := ⟨j.val,by omega⟩
        have e : lowPrefix10 k=j := Fin.ext rfl
        have prije : k<fg.first := by change j.val<fg.first.val; omega
        have z0 : nodes A j=0 := e ▸ fg.first_min k prije (e ▸ off)
        simp [V,Q,off,z0]
      · simp [V,Q,fit _ off,mul_comm]
    have dq : Q.natDegree≤3 := by
      dsimp only [Q]
      rw [natDegree_neg]
      exact natDegree_mul_le_of_le (by simp) dP.le
    have nd : ¬P∣primitive Q := by
      change ¬P∣primitive (-(X*P))
      rw [map_neg,dvd_neg]
      exact quadratic_head_not_dvd_own_weighted_primitive dP p0
    obtain ⟨k,kn,ev⟩ := runResidue Q X dq (by simp) nd cs zv
    rw [eqJ] at ev
    exact ⟨cs,Or.inr ⟨p5,RKCert.Paired.normalize_quartic_residue (by norm_num) kn ev⟩⟩
end RKResearch.Certified.Graded.MultiOff
