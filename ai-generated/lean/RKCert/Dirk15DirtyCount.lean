module

public import RKCert.Dirk15SupportRefinement

@[expose] public section

/-! # True physical reverse-cubic support count in the non-C(2) chart
If any nodal mass survives, the paid probes impose thirteen sites. If
every nodal mass cancels, use the true reflected incoming budget on the
invariant hull, not an assertion that the hull is entirely marked. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial Module
open RKCert.Paired.ReverseHermite
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s→Fin s→K} {b : Vec K s}

theorem reverse_failures_of_zero_sum (ho : HasTreeOrderAtLeast A b p)
    {U : Submodule K (Vec K s)}
    (h0 : ∀ v∈U,row v 1=0) (inv : U.map (diag (mirror A))≤U) :
    p/2≤(failedNodes (rev (mirror A)) (rev b) (flipSpace U) s).card+1 := by
  classical
  let S := activeNonzero (nodes A) b
  have inc : (S.erase 1).image (fun x : K => 1-x)⊆
      failedNodes (rev (mirror A)) (rev b) (flipSpace U) s := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have a1 := Finset.ne_of_mem_erase ha
    have hav := Finset.mem_of_mem_erase ha
    obtain ⟨_,_,hnet⟩ := Finset.mem_filter.mp hav
    apply mem_failedNodes.mpr
    refine ⟨sub_ne_zero.mpr (Ne.symm a1),?_⟩
    rintro ⟨_,⟨w,hw,rfl⟩,rows⟩
    have eqb (i : Fin s) (hi : nodes A i=a) : w i=b i := by
      have hy : rev (mirror A) i.rev=1-a := by simp [mirror,hi]
      simpa using rows i.rev i.rev.isLt hy
    have hz := h0 _ (Clock.fiber_mem inv (1-a) hw)
    have hsum : row (Clock.fiber (mirror A) (1-a) w) 1=combinedMass (nodes A) b a := by
      rw [row_apply,combinedMass,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : nodes A i=a
      · simp [Clock.fiber,mirror,hi,eqb i hi]
      · simp [Clock.fiber,mirror,hi]
    exact hnet (hsum.symm.trans hz)
  have card := Finset.card_le_card inc
  have inj : Function.Injective (fun x : K => 1-x) := by
    intro x y e
    linear_combination -e
  rw [Finset.card_image_of_injective _ inj] at card
  have old := activeNonzero_card_of_treeOrder ho
  change p/2≤S.card at old
  by_cases h : 1∈S
  · rw [Finset.card_erase_of_mem h] at card; omega
  · rw [Finset.erase_eq_of_notMem h] at card; omega

variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

def dirtyRows (A : Fin 20→Fin 20→K) (b : Vec K 20) : Finset (Fin 20) :=
  Finset.univ.filter (fun i => reverseCubic A b i≠0)

private theorem no_fiber_mass {n : ℕ} (c w : Vec K s)
    (hS : (Clock.headSites c w).card≤n+1)
    (hpay : ∀ P : K[X], P.natDegree≤n → ∑ i,w i*P.eval (c i)=0)
    (a : K) : combinedMass c w a=0 := by
  classical
  let S := Clock.headSites c w
  change S.card≤n+1 at hS
  rw [combinedMass,Finset.sum_filter]
  by_cases ha : a∈S
  · let f (z : K) := if z=a then 1 else (0:K)
    let P := Lagrange.interpolate S id f
    have atSite (z : K) (hz : z∈S) : P.eval z=f z :=
      Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hz
    have hP : P≠0 := by
      intro e
      have zz := atSite a ha
      rw [e] at zz
      simp [f] at zz
    have deg : P.natDegree < S.card := (natDegree_lt_iff_degree_lt hP).mpr
      (Lagrange.degree_interpolate_lt (s:=S) f (Set.injOn_id _))
    calc
      _ = ∑ i,w i*P.eval (c i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : w i=0
        · simp [hi]
        · rw [atSite _ (Clock.headSites_mem i hi)]
          by_cases hz : c i=a <;> simp [f,hz]
      _ = 0 := hpay P (by omega)
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hi : c i=a
    · have he : w i=0 := by
        by_contra hn
        apply ha
        rw [←hi]
        exact Clock.headSites_mem i hn
      simp [hi,he]
    · simp [hi]

omit [CharZero K] in
private theorem paid_cubic_moments (ho : HasTreeOrderAtLeast A b 15)
    (P : K[X]) (deg : P.natDegree≤11) :
    ∑ i, reverseCubic A b i*P.eval (mirror A i)=0 := by
  have hτ : reverseCubic A b∈marked A 15 3 := seed3_marked ho (by decide : 4≤15)
  change reverseCubic A b∈annih (treeSpace A 11) at hτ
  have hf : (reflectPolynomial P).natDegree≤11 := (reflectPolynomial_degree P).trans deg
  have hE : evalNodes A (reflectPolynomial P) ∈ treeSpace A 11 :=
    evalNodes_mem_treeSpace A _ hf
  have hh := mem_annih.mp hτ _ hE
  rw [row_apply] at hh
  simpa only [evalNodes_apply,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X,mirror,Pi.sub_apply,Pi.one_apply] using hh

theorem cubic_nodal_mass_zero_of_small_sites (ho : HasTreeOrderAtLeast A b 15)
    (hS : (Clock.headSites (mirror A) (reverseCubic A b)).card≤12) :
    ∀ a : K, combinedMass (mirror A) (reverseCubic A b) a=0 :=
  no_fiber_mass (n:=11) (mirror A) (reverseCubic A b) hS (paid_cubic_moments ho)

private theorem rank_hull_of_zero_mass (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15NonC2Chart A b) (m0 : ∀ a : K, combinedMass (mirror A) (reverseCubic A b) a=0) :
    7≤(Clock.headSites (mirror A) (reverseCubic A b)).card := by
  classical
  let c := mirror A
  let τ := reverseCubic A b
  let S := Clock.headSites c τ
  let T := S.image (fun x => Clock.fiber c x τ)
  let U := Submodule.span K (T:Set (Vec K 20))
  have sub (a : K) (ha : a∈S) : Clock.fiber c a τ∈U :=
    Submodule.subset_span (Finset.mem_image_of_mem _ ha)
  have inv : U.map (diag c)≤U := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    intro v hv
    change v∈T at hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    have eq : diag c (Clock.fiber c z τ)=z • Clock.fiber c z τ := by
      ext i
      by_cases h : c i=z <;> simp [Clock.fiber,h]
    change (diag c) (Clock.fiber c z τ)∈U
    rw [eq]
    exact U.smul_mem _ (sub z hz)
  have hsum : ∀ v∈U,row v 1=0 := by
    intro v hv
    have Ule : U≤LinearMap.ker (row (1:Vec K 20)) := by
      apply Submodule.span_le.mpr
      intro v hv
      change v∈T at hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      apply LinearMap.mem_ker.mpr
      rw [row_symmetric,row_apply]
      simp only [Clock.fiber,Pi.one_apply,mul_one]
      rw [←Finset.sum_filter]
      exact m0 z
    exact (row_symmetric _ _).trans (LinearMap.mem_ker.mp (Ule hv))
  have whole (j : ℕ) (hl : 3≤j) (hu : j≤7) : marked A 15 j≤U := by
    rw [order15_nonC2_reverse_orbit ha ho H j hl hu]
    apply (chain_le_iff _).mpr
    refine ⟨bot_le,fun k hk => ?_⟩
    have e : (diag c ^ k) τ = ∑ z∈S,z^k • Clock.fiber c z τ := by
      ext i
      rw [Clock.pow_diag_apply,Finset.sum_apply]
      by_cases hi : τ i≠0
      · rw [Finset.sum_eq_single_of_mem (c i) (Clock.headSites_mem i hi)]
        · simp [Clock.fiber]
        · intro z _ hne
          simp [Clock.fiber,Ne.symm hne]
      · have he : τ i=0 := not_not.mp hi
        simp [Clock.fiber,he]
    rw [e]
    exact U.sum_mem (fun z hz => U.smul_mem _ (sub z hz))
  have hD := reverse_failures_of_zero_sum ho hsum inv
  have count : 3≤(failedNodes (rev c) (rev b) (flipSpace U) 20).card := by
    change (15:ℕ)/2≤(failedNodes (rev c) (rev b) (flipSpace U) 20).card+1 at hD
    omega
  have rank : finrank K (flipSpace (marked A 15 6))+3≤finrank K (flipSpace U) := by
    refine incoming_inclusive_gain (rev c) (rev b) (flipSpace (marked A 15 6)) (flipSpace U)
      (revN A) (revN_causal ha) (flip_mask c U inv) (Submodule.map_mono (whole 6 (by decide) (by decide)))
      ?_ 3 count ?_
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨transMat A v,whole 7 (by decide) (by decide) (marked_mat (by decide : 6+2≤15) hv),
        (revN_rev A v).symm⟩
    · intro P hp
      have h0 := weighted_reverse_primitive ho (n:=6) (by omega : P.natDegree≤6) (by decide)
      refine ⟨_,whole 7 (by decide) (by decide) h0,?_⟩
      change rev (transMat A (weightedEval c b P)-weightedEval c b (formalPrimitive P))= _
      have e := revN_rev A (weightedEval c b P)
      rw [rev_weighted] at e
      rw [map_sub,rev_weighted,e]
  rw [flip_rank,flip_rank,H.marked_rank_exact 6 (by decide) (by decide)] at rank
  exact rank.trans ((finrank_span_finset_le_card T).trans Finset.card_image_le)

omit [CharZero K] in
private theorem cancel_mass_needs_two (m0 : ∀ a : K, combinedMass (mirror A) (reverseCubic A b) a=0) :
    2*(Clock.headSites (mirror A) (reverseCubic A b)).card≤(dirtyRows A b).card := by
  classical
  let D := dirtyRows A b
  let c := mirror A
  let τ := reverseCubic A b
  let S := D.image c
  change 2*S.card≤D.card
  rw [Finset.card_eq_sum_card_image c D]
  have two (a : K) (ha : a∈S) : 2≤(D.filter (fun i => c i=a)).card := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
    let G := D.filter (fun j => c j=a)
    have gi : i∈G := Finset.mem_filter.mpr ⟨hi,he⟩
    by_contra! ht
    have cg : G.card≤1 := by change G.card<2 at ht; omega
    have eg : G={i} := (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr gi) (by rw [Finset.card_singleton]; exact cg)).symm
    let all := Finset.univ.filter (fun j : Fin 20 => c j=a)
    have sum : ∑ j∈G,τ j=0 := by
      calc
        ∑ j∈G,τ j = ∑ j∈all,τ j := by
          apply Finset.sum_subset
          · intro j hj
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,(Finset.mem_filter.mp hj).2⟩
          · intro j hj hn
            by_contra hh
            apply hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j,hh⟩,
              (Finset.mem_filter.mp hj).2⟩
        _ = _ := m0 a
    rw [eg,Finset.sum_singleton] at sum
    exact (Finset.mem_filter.mp hi).2 sum
  have he : ∑ a∈S,(2:ℕ) ≤ ∑ a∈S,(D.filter (fun i => c i=a)).card :=
    Finset.sum_le_sum two
  rw [Finset.sum_const,nsmul_eq_mul] at he
  change S.card*2≤_ at he
  rw [mul_comm S.card] at he
  exact he

/-- The actual twenty-stage non-C(2) boundary needs at least thirteen
physical cubic-dirty rows, occupying at least seven numerical sites. -/
theorem order15_nonC2_dirty_count (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) :
    13≤(dirtyRows A b).card ∧ 7≤(Clock.headSites (mirror A) (reverseCubic A b)).card := by
  let H := order15_nonC2_rank_chart ha ho hq
  let S := Clock.headSites (mirror A) (reverseCubic A b)
  change 13≤(dirtyRows A b).card ∧ 7≤S.card
  by_cases h : S.card≤12
  · have zero := cubic_nodal_mass_zero_of_small_sites ho h
    have hn := rank_hull_of_zero_mass ha ho H zero
    have rows := cancel_mass_needs_two zero
    exact ⟨by omega,hn⟩
  · have le : S.card≤(dirtyRows A b).card :=
      Finset.card_image_le
    exact ⟨by omega,by omega⟩

end
end RKCert.Paired
