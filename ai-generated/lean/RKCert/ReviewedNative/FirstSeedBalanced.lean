module

public import RKCert.ReviewedNative.FirstSeedWideTrace
public import RKCert.ReviewedNative.NativeLiveOutput
public import RKCert.ReviewedNative.BalancedSeedRepresentatives

@[expose] public section

/-! # Finite balanced first-seed coalescing, with explicit grade costs

The chronology lemmas and exact representative count below consume the
sealed p19 interfaces, but their hypotheses here are independent of
order or width. The missing degree of an ordinary reverse carrier is
paid by a live off-seed coordinate, not by a new scalar calculation. -/
namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p m h j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

abbrev originalCarrier (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) :=
  (weightedEval (nodes A) (firstSeed A b)).range

theorem Cover.original_represent (B : Cover A b m h) {v : Fin s→K}
    (hv : v∈annih (treeSpace A m)) : v∈originalCarrier A b := by
  obtain ⟨P,_,eq⟩ := B.represent v hv
  refine ⟨P.comp (1-X),?_⟩
  ext i
  have e := congrFun eq i
  simpa only [weightedEval_apply,eval_comp,eval_sub,eval_one,eval_X,reflectedClock,
    Pi.sub_apply,Pi.one_apply] using e

theorem originalCarrier_rank :
    finrank K (originalCarrier A b)=(weightedSites (nodes A) (firstSeed A b)).card := by
  let n := (weightedSites (nodes A) (firstSeed A b)).card
  change finrank K (weightedEval (nodes A) (firstSeed A b)).range=n
  rw [←weightedBand_eq_range (nodes A) (firstSeed A b) n le_rfl]
  exact weightedBand_rank _ _ _ le_rfl

theorem originalCarrier_fibre_agreement {v : Fin s→K}
    (hv : firstSeed A b*v∈originalCarrier A b) {i k : Fin s}
    (di : firstSeed A b i≠0) (dk : firstSeed A b k≠0) (same : nodes A i=nodes A k) :
    v i=v k := by
  obtain ⟨P,e⟩ := hv
  have paidEval (l : Fin s) (dl : firstSeed A b l≠0) : v l=P.eval (nodes A l) := by
    have z := congrFun e l
    exact (mul_right_inj' dl).mp (by simpa only [weightedEval_apply,Pi.mul_apply,mul_comm] using z.symm)
  rw [paidEval i di,paidEval k dk,same]

theorem Cover.balanced_carrier_le_annih (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : j+m+2 ≤ p) (bal : ∀ a,clockMass (nodes A) (firstSeed A b) a=0) :
    originalCarrier A b ≤ annih (treeSpace A j) := by
  rintro _ ⟨P,rfl⟩
  refine mem_annih.mpr fun v hv => ?_
  obtain ⟨Q,e⟩ := B.original_represent (seed_times_tree_annih ho pay hv)
  calc
    row (weightedEval (nodes A) (firstSeed A b) P) v =
       ∑ i,firstSeed A b i*(P.eval (nodes A i)*Q.eval (nodes A i)) := by
      simp only [row_apply,dotProduct,weightedEval_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hx := congrFun e i
      simp only [weightedEval_apply,Pi.mul_apply] at hx
      calc
        _ = P.eval (nodes A i)*(firstSeed A b i*v i) := by ring
        _ = _ := by rw [←hx]; ring
    _ = 0 := by
      rw [weighted_sum_by_clock (nodes A) (firstSeed A b) (fun x => P.eval x*Q.eval x)]
      simp only [bal,zero_mul,Finset.sum_const_zero]

/-- If the balanced carrier fills the preceding annihilator, or misses
only a paid live coordinate outside its support, the whole middle
forward grade agrees on the original seed clock fibres. -/
theorem Cover.balanced_middle_trace (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : j+m+2 ≤ p) (outPay : 2*j+3 ≤ p)
    (bal : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (room : finrank K (annih (treeSpace A j))=(weightedSites (nodes A) (firstSeed A b)).card ∨
      (finrank K (annih (treeSpace A j))=(weightedSites (nodes A) (firstSeed A b)).card+1 ∧
       ∃ i,firstSeed A b i=0 ∧ b i≠0))
    {v : Fin s→K} (hv : v∈zeroSpace A m) : firstSeed A b*v∈originalCarrier A b := by
  have rowBand := seed_times_tree_annih ho (j:=m) (q:=j) (by omega) (zeroSpace_le_treeSpace A m hv)
  have inc := B.balanced_carrier_le_annih ho pay bal
  have dim := originalCarrier_rank (A:=A) (b:=b)
  rcases room with eq|⟨eq,i,di,bi⟩
  · have e := Submodule.eq_of_le_of_finrank_le inc (by omega)
    exact e.symm ▸ rowBand
  · have out := live_coordinate_out_treeSpace ho outPay i bi
    have cout := finrank_zeroAt_annih (treeSpace A j) i out
    have sub : originalCarrier A b ≤ zeroAt (annih (treeSpace A j)) i := by
      rintro _ ⟨P,rfl⟩
      exact mem_zeroAt.mpr ⟨inc ⟨P,rfl⟩,by simp [di]⟩
    have e := Submodule.eq_of_le_of_finrank_le sub (by omega)
    rw [e]
    exact mem_zeroAt.mpr ⟨rowBand,by simp [di]⟩

theorem live_aggregate_clock_count (ho : HasOrder p A b) {q : ℕ} (pay : 2*q+1 ≤ p) :
    q+1 ≤ (activeClockSites (nodes A) b).card := by
  by_contra! small
  let c := nodes A
  let T := activeClockSites c b
  change T.card<q+1 at small
  let H := nodalHull T
  have d : H.natDegree ≤ q := (natDegree_nodalHull T).le.trans (by omega)
  let a : Fin (q+1)→K := fun j=>H.coeff j.val
  have e : coeffEval A q a = evalNodes A H := (evalNodes_eq_coeffEval A H d).symm
  have z (i : Fin (q+1)) : (∑ j : Fin (q+1),a j/((i.val+j.val+1:ℕ):K))=0 := by
    rw [←probe_coeffEval ho (q:=q) (by have :=i.isLt; omega) a,e]
    change (∑ j, (b j * (c j)^i.val) * H.eval (c j))=0
    simp only [mul_assoc]
    rw [weighted_sum_by_clock c b (fun x=>x^i.val * H.eval x)]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases mem : x∈T
    · rw [nodalHull_eval_of_mem mem,mul_zero,mul_zero]
    · have x0 : clockMass c b x=0 := by
        by_contra nz
        exact mem (Finset.mem_filter.mpr ⟨hx,nz⟩)
      rw [x0,zero_mul]
  have van := moments_detect ho (n:=q+1) (d:=1) (by decide) (by omega)
    (fun i j => by have :=i.isLt; have :=j.isLt; omega) a z
  apply (monic_nodalHull T).ne_zero
  ext r
  rw [coeff_zero]
  by_cases r' : r<q+1
  · exact van ⟨r,r'⟩
  · exact coeff_eq_zero_of_natDegree_lt (show H.natDegree<r by omega)

theorem originalCarrier_mass_zero {v : Fin s→K} (hv : v∈originalCarrier A b)
    (bal : ∀ x,clockMass (nodes A) (firstSeed A b) x=0) (a : K) :
    clockMass (nodes A) v a=0 := by
  obtain ⟨P,rfl⟩ := hv
  have e : clockMass (nodes A) (weightedEval (nodes A) (firstSeed A b) P) a =
      P.eval a*clockMass (nodes A) (firstSeed A b) a := by
    rw [clockMass,clockMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [weightedEval_apply,(Finset.mem_filter.mp hi).2]
  rw [e,bal,mul_zero]

theorem Cover.clean_of_off_seed (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : j+m+1 ≤ p) (i : Fin s) (di : firstSeed A b i=0) (bi : b i≠0) :
    ∀ f∈zeroSpace A j,f i=0 := by
  intro f hf
  have z := B.support (weight_times_defect_annih ho pay hf) di
  exact (mul_eq_zero.mp (show b i*f i=0 from z)).resolve_left bi

theorem Cover.clean_of_active_seed (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : j+m+1 ≤ p) (bal : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (trace : ∀ f∈zeroSpace A j,firstSeed A b*f∈originalCarrier A b)
    (i : Fin s) (di : firstSeed A b i≠0) (active : clockMass (nodes A) b (nodes A i)≠0)
    (on : ∀ k,nodes A k=nodes A i → b k≠0 → firstSeed A b k≠0) :
    ∀ f∈zeroSpace A j,f i=0 := by
  intro f hf
  have cf := B.original_represent (weight_times_defect_annih ho pay hf)
  have zero := originalCarrier_mass_zero cf bal (nodes A i)
  have conv : clockMass (nodes A) (b*f) (nodes A i) =
      clockMass (nodes A) b (nodes A i)*f i := by
    rw [clockMass,clockMass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have same := (Finset.mem_filter.mp hk).2
    change b k*f k=b k*f i
    by_cases bk : b k=0
    · rw [bk,zero_mul,zero_mul]
    · rw [originalCarrier_fibre_agreement (trace f hf) (on k same bk) di same]
  rw [conv] at zero
  exact (mul_eq_zero.mp zero).resolve_left active

theorem Cover.clean_at_active_clock (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : j+m+1 ≤ p) (bal : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (trace : ∀ f∈zeroSpace A j,firstSeed A b*f∈originalCarrier A b)
    {a : K} (active : a∈activeClockSites (nodes A) b) :
    ∃ i,nodes A i=a ∧ ∀ f∈zeroSpace A j,f i=0 := by
  by_cases off : ∃ i,nodes A i=a ∧ firstSeed A b i=0 ∧ b i≠0
  · obtain ⟨i,ci,di,bi⟩ := off
    exact ⟨i,ci,B.clean_of_off_seed ho pay i di bi⟩
  have on (i : Fin s) (ci : nodes A i=a) (bi : b i≠0) : firstSeed A b i≠0 :=
    fun di => off ⟨i,ci,di,bi⟩
  obtain ⟨i,bi,ci⟩ := mem_weightedSites.mp (activeClockSites_in_weightedSites _ _ active)
  exact ⟨i,ci,B.clean_of_active_seed ho pay bal trace i (on i ci bi)
    (ci.symm ▸ clockMass_ne_of_active active) (fun k e => on k (e.trans ci))⟩


/-- Pay the compressed causal prefix, every truly active nonzero clean
clock, and one removed row per balanced seed clock, in the same width.
The cost of the smaller exact receiver is supplied as a checked floor. -/
theorem Cover.coalesced_clean_prefix_budget (B : Cover A b m h) (ho : HasOrder p A b)
    (ha : ∀ i j,i ≤ j → A i j=0) (pay : j+m+2 ≤ p)
    (bal : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (clean : ∀ a∈activeClockSites (nodes A) b, ∃ i,nodes A i=a ∧ ∀ f∈zeroSpace A (j+1),f i=0)
    (trace : ∀ f∈zeroSpace A (j+1),firstSeed A b*f∈originalCarrier A b)
    (hasClock : 1 ≤ ((activeClockSites (nodes A) b).erase 0).card)
    (lower : ℕ) (receiverFloor : ∀ {n} {P : Matrix (Fin n) (Fin n) K} {w : Fin n→K},
      (∀ i k,i ≤ k → P i k=0) → HasOrder (j+1) P w → lower ≤ n) :
    lower+((activeClockSites (nodes A) b).erase 0).card+
      (weightedSites (nodes A) (firstSeed A b)).card ≤ s := by
  let c := nodes A
  let d := firstSeed A b
  let R := seedRepresentatives c d
  let n := R.card
  let E := R.orderIsoOfFin (rfl : R.card=n)
  let e : Fin n→Fin s := fun i=>(E i).val
  let r (i : Fin s) : Fin n :=
    E.symm ⟨seedRep c d i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have es (i : Fin s) : e (r i)=seedRep c d i := by
    dsimp only [e,r]
    rw [E.apply_symm_apply]
  have order : Monotone e := fun _ _ h => E.monotone h
  have earlier (i : Fin s) : e (r i) ≤ i := (es i).symm ▸ seedRep_le c d i
  have agree (v : Fin s→K) (hv : v∈treeSpace A j) (i : Fin s) : v (e (r i))=v i := by
    rw [es]
    by_cases z : d i=0
    · rw [seedRep_of_dead z]
    · have rep := seedRep_live (c:=c) z
      have band := B.original_represent (seed_times_tree_annih ho pay hv)
      exact originalCarrier_fibre_agreement band rep.1 z rep.2
  let P := causalMergeMatrix A e r
  have strict := causalMerge_strict ha order earlier
  let T := (activeClockSites c b).erase 0
  let L := Finset.univ.filter (fun i : Fin n =>
    nodes P i≠0 ∧ ∀ v∈zeroSpace P (j+1),v i=0)
  have cover : T ⊆ L.image (nodes P) := by
    intro a aT
    have a0 := (Finset.mem_erase.mp aT).1
    have ax := (Finset.mem_erase.mp aT).2
    obtain ⟨i,ci,cl⟩ := clean a ax
    have atRep : nodes A (e (r i))=a ∧ ∀ f∈zeroSpace A (j+1),f (e (r i))=0 := by
      rw [es]
      by_cases z : d i=0
      · rw [seedRep_of_dead z]
        exact ⟨ci,cl⟩
      · have rp := seedRep_live (c:=c) z
        refine ⟨rp.2.trans ci,fun f hf=>?_⟩
        exact (originalCarrier_fibre_agreement (trace f hf) rp.1 z rp.2).trans (cl f hf)
    obtain ⟨clock,isClean⟩ := clean_causalMerge agree (r i) atRep.2
    exact Finset.mem_image.mpr
      ⟨r i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(clock.trans atRep.1).symm ▸ a0,isClean⟩,
        clock.trans atRep.1⟩
  have many : T.card ≤ L.card := (Finset.card_le_card cover).trans Finset.card_image_le
  have nonempty : L.Nonempty := Finset.card_pos.mp (by change 1 ≤ T.card at hasClock; omega)
  let i := L.min' nonempty
  have hi : i∈L := Finset.min'_mem _ _
  have paid : nodes P i≠0 ∧ ∀ v∈zeroSpace P (j+1),v i=0 := (Finset.mem_filter.mp hi).2
  have receiver := exact_receiver_prefix_order strict i (j+1) paid.1 paid.2
  have hd (k l : Fin i.val) (kl : k ≤ l) :
      ((nodes P i)⁻¹ • prefixMatrix P i.isLt.le) k l=0 := by
    rw [Matrix.smul_apply,prefix_strict_lower strict i.isLt.le k l kl,smul_zero]
  have lo := receiverFloor hd receiver
  let v (u : L) : Fin (n-i.val) := ⟨u.val.val-i.val,by
    have le := Finset.min'_le _ _ u.property
    have := u.val.isLt
    change i.val ≤ u.val.val at le
    omega⟩
  have inject : Function.Injective v := by
    intro u t equal
    apply Subtype.ext
    apply Fin.ext
    have eu := congrArg Fin.val equal
    change u.val.val-i.val=t.val.val-i.val at eu
    have uBefore := Finset.min'_le _ _ u.property
    have tBefore := Finset.min'_le _ _ t.property
    change i.val ≤ u.val.val at uBefore
    change i.val ≤ t.val.val at tBefore
    omega
  have cap : L.card ≤ n-i.val := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective v inject
  have compressed := balanced_seed_representative_count bal
  change n+(weightedSites c d).card ≤ s at compressed
  change lower+T.card+(weightedSites c d).card ≤ s
  omega

end
end RKResearch.Certified.Graded.Reverse.FirstWide
