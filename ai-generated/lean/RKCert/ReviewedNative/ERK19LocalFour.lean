module

public import RKCert.ReviewedNative.ERK19LocalHiddenRank
public import RKCert.ReviewedNative.LocalLinearDegreeDrop

@[expose] public section

/-! # The rank-four branch of the actual local ERK19 hidden kernel -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ : Fin 29→K}

def localEnlarged (A : Matrix (Fin 29) (Fin 29) K) (M : Submodule K (Fin 29→K)) (j : ℕ) :=
  zeroSpace A j ⊔ M

structure LocalCore (A : Matrix (Fin 29) (Fin 29) K) (M : Submodule K (Fin 29→K)) : Prop where
  stable : M.map (diag (nodes A))≤M
  inside : M≤zeroSpace A 9
  maximal : ∀ V : Submodule K (Fin 29→K), V.map (diag (nodes A))≤V → V≤zeroSpace A 9 → V≤M
  rankCap : finrank K M≤5
  fiveOut : ¬zeroSpace A 5≤M
  fiveRank : 5≤finrank K (zeroSpace A 5)
  sixCap : finrank K (zeroSpace A 6)≤7
  supGrow : ∀ j,5≤j → j<9 → finrank K (localEnlarged A M j)<finrank K (localEnlarged A M (j+1))
  nineRank : finrank K (localEnlarged A M 9)=10

set_option maxHeartbeats 900000 in
theorem width29_local_core (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) : ∃ M, LocalCore A M := by
  let C := diag (nodes A)
  obtain ⟨n,_,e⟩ := exists_plateau C (zeroSpace A 9)
  let M := core C (zeroSpace A 9) n
  have inv : M.map C≤M := invariant_of_plateau e
  have inn : M≤zeroSpace A 9 := fun _ h=>by
    simpa only [pow_zero,one_apply_eq_self] using mem_core.mp h 0 (Nat.zero_le _)
  have maxM (V : Submodule K (Fin 29→K)) (st : V.map C≤V) (le : V≤zeroSpace A 9) : V≤M :=
    invariant_le_core le st n
  have fr := (ordered_width29_frame ha ho).1
  have ten := (nonzero_seed_grade_ten ha ho nz).1
  have sep : PolySeparated A 9 := PolySeparated.of_coeff fr.separated
  have cap : finrank K M≤5 := invariant_core_cap_of_rank (q:=9) ha (by decide)
    fr.separated fr.middleDefects (by change finrank K (zeroSpace A 10)≤12; omega) M inn inv
  have five := grade_five_surplus ha (sep.mono (by decide : 5≤9))
  have six := zeroSpace_rank_interval_of_separation ha fr.separated (j:=6) (d:=3) (by decide) (by decide)
  change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 9) at six
  rw [fr.middleDefects] at six
  have sixCap : finrank K (zeroSpace A 6)≤7 := by omega
  have outside : ¬zeroSpace A 5≤M := by
    intro h
    have eq := Submodule.eq_of_le_of_finrank_le h (show finrank K M≤finrank K (zeroSpace A 5) by omega)
    have growth := clock_invariant_outgoing ha (sep.mono (by decide : 5≤9)) (le_of_eq eq.symm) inv
    change finrank K M+3≤finrank K (zeroSpace A 6) at growth
    have ge : 5≤finrank K M := by rwa [eq] at five
    omega
  have entry (j:ℕ) (a:5≤j) : ¬localEnlarged A M j≤M := by
    intro le
    exact outside ((zeroSpace_mono A a).trans (le_sup_left.trans le))
  refine ⟨M,⟨inv,inn,maxM,cap,outside,five,sixCap,?_,?_⟩⟩
  · intro j lo hi
    apply Submodule.finrank_lt_finrank_of_lt
    have nst : ¬(localEnlarged A M j).map C≤localEnlarged A M j := by
      intro st
      exact entry j lo (maxM _ st (sup_le (zeroSpace_mono A hi.le) inn))
    have mon : localEnlarged A M j≤localEnlarged A M (j+1) :=
      sup_le_sup_right (zeroSpace_mono A (Nat.le_succ _)) M
    refine lt_of_le_of_ne mon (fun eq=>nst ?_)
    have image : (localEnlarged A M j).map C≤localEnlarged A M (j+1) := by
      change ((zeroSpace A j ⊔ M).map C)≤zeroSpace A (j+1)⊔M
      rw [Submodule.map_sup]
      apply sup_le _ (inv.trans le_sup_right)
      exact (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)).trans le_sup_left
    exact image.trans (le_of_eq eq.symm)
  · change finrank K (zeroSpace A 9⊔M : Submodule K (Fin 29→K))=10
    rw [sup_eq_left.mpr inn]
    exact fr.middleDefects

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflected_invariant_of_clock {M : Submodule K (Fin 29→K)}
    (stable : M.map (diag (nodes A))≤M) : M.map (diag (reflectedClock A))≤M := by
  rintro _ ⟨u,hu,rfl⟩
  have t : diag (reflectedClock A) u=u-diag (nodes A) u := by
    ext i
    simp only [diag_apply,Pi.sub_apply,reflectedClock,Pi.one_apply]
    ring
  rw [t]
  exact M.sub_mem hu (stable (Submodule.mem_map_of_mem hu))

set_option maxHeartbeats 750000 in
omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem single_extra_core_clock {M : Submodule K (Fin 29→K)}
    (stable : M.map (diag (nodes A))≤M) (inc : hiddenKernel b τ U≤M)
    (d : finrank K M=finrank K (hiddenKernel b τ U)+1) :
    ∃ a, ∀ v∈M, ∀ i,reflectedClock A i≠a → τ i*v i=0 := by
  let J := hiddenKernel b τ U
  let y := reflectedClock A
  change finrank K M=finrank K J+1 at d
  have notle : ¬M≤J := by
    intro h
    have u : finrank K M≤finrank K J := Submodule.finrank_mono h
    omega
  obtain ⟨v,hv,out⟩ : ∃ v : Fin 29→K, v∈M ∧ v∉J := IsConcreteLE.not_le_iff_exists.mp notle
  have projections : MaskInvariant y M := clock_mask_invariant
    (fun _ hw=>reflected_invariant_of_clock stable (Submodule.mem_map_of_mem hw))
  let S : Finset K := Finset.univ.image y
  have summed : (∑ a∈S,blockMask y a v)=v := by
    funext i
    rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (y i) (Finset.mem_image_of_mem y (Finset.mem_univ i))]
    · simp [blockMask]
    · intro j _ hj; simp [blockMask,Ne.symm hj]
  have find : ∃ a∈S,blockMask y a v∉J := by
    by_contra! h
    exact out (summed ▸ J.sum_mem h)
  obtain ⟨a,_,outside⟩ := find
  let w := blockMask y a v
  let L := Submodule.span K {w}
  have wm : w∈M := projections a v hv
  have triv : J<J⊔L := by
    refine lt_of_le_of_ne le_sup_left (fun eq=>outside ?_)
    have h : w∈J⊔L := (show L≤J⊔L from le_sup_right)
      (Submodule.mem_span_singleton_self w)
    rwa [←eq] at h
  have oneIn : L≤M := by
    change Submodule.span K ({w} : Set (Fin 29→K))≤M
    apply Submodule.span_le.mpr
    intro z hz
    have e : z=w := Set.mem_singleton_iff.mp hz
    exact e.symm ▸ wm
  have sumle : J⊔L≤M := sup_le inc oneIn
  have e : J⊔L=M := Submodule.eq_of_le_of_finrank_le sumle (by
    have grow:=Submodule.finrank_lt_finrank_of_lt triv
    omega)
  refine ⟨a,fun x hx i other=>?_⟩
  rw [←e] at hx
  obtain ⟨f,hf,g,hg,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨aScalar,rfl⟩ := Submodule.mem_span_singleton.mp hg
  have fz : τ i*f i=0 := congrFun (mem_hiddenKernel.mp hf).1 i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,y,blockMask,ite_eq_right other,
    mul_zero,add_zero,fz]

private theorem partners_core_le_hidden
    (ha : ∀ i k,i≤k→A i k=0) (ho : HasOrder 19 A b) (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) {j l : ℕ}
    (lim : j≤6) (lpay : j≤4+l) :
    core (diag (nodes A)) (localEnlarged A (hiddenKernel b τ U) j) l≤hiddenKernel b τ U := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  intro z hz
  have ex (k : ℕ) : ∃ f∈zeroSpace A j, k≤l → (C^k) z-f∈J := by
    by_cases paid : k≤l
    · obtain ⟨f,hf,u,hu,s⟩ := Submodule.mem_sup.mp (mem_core.mp hz k paid)
      exact ⟨f,hf,fun _=>by rw [←s,add_comm,add_sub_cancel_right];exact hu⟩
    · exact ⟨0,(zeroSpace A j).zero_mem,fun e=>(paid e).elim⟩
  choose fs fin fit using ex
  have ret := hiddenKernel_of_same_grade_partners ha ho F full (by decide) lim lpay fs fin
  have h : fs 0∈J := by
    apply ret
    intro a pay
    have c : C ((C^a) z-fs a)∈J :=
      hiddenKernel_forward_clock F (Submodule.mem_map_of_mem (fit a (by omega)))
    have e : C (fs a)-fs (a+1)=((C^(a+1)) z-fs (a+1))-C ((C^a) z-fs a) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub];abel
    rw [e]
    exact J.sub_mem (fit (a+1) (by omega)) c
  have nn := fit 0 (Nat.zero_le l)
  rw [pow_zero,one_apply_eq_self] at nn
  simpa only [sub_add_cancel] using J.add_mem nn h

set_option maxHeartbeats 1300000 in
theorem width29_local_hidden_rank_four_impossible
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 8 r U τ) (full : primitiveBack A b 8=annih (treeSpace A 9))
    (four : finrank K (hiddenKernel b τ U)=4) : False := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  have j9 : J≤zeroSpace A 9 := hiddenKernel_le_midpoint ho F full
  have clock : J.map C≤J := hiddenKernel_forward_clock F
  have sep : PolySeparated A 9 := PolySeparated.of_coeff (coeff_separated ho (by decide))
  obtain ⟨M,L⟩ := width29_local_core ha ho nz
  have inc : J≤M := L.maximal _ clock j9
  have mlo := Submodule.finrank_mono inc
  change finrank K J≤finrank K M at mlo
  change finrank K J=4 at four
  let W := localEnlarged A M
  have wg5 : finrank K (W 5)<finrank K (W 6) := L.supGrow 5 (by decide) (by decide)
  have wg6 : finrank K (W 6)<finrank K (W 7) := L.supGrow 6 (by decide) (by decide)
  have wg7 : finrank K (W 7)<finrank K (W 8) := L.supGrow 7 (by decide) (by decide)
  have wg8 : finrank K (W 8)<finrank K (W 9) := L.supGrow 8 (by decide) (by decide)
  have wn : finrank K (W 9)=10 := L.nineRank
  have MW : finrank K M<finrank K (W 5) := by
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne le_sup_right (fun eq=>L.fiveOut ?_)
    exact le_sup_left.trans (le_of_eq eq.symm)
  have capM := L.rankCap
  have f5 := L.fiveRank
  have f6 := L.sixCap
  have sameCore : M=J := by
    by_cases same : finrank K M=4
    · exact (Submodule.eq_of_le_of_finrank_le inc (by omega)).symm
    exfalso
    have md : finrank K M=finrank K J+1 := by omega
    obtain ⟨a,onNode⟩ := single_extra_core_clock L.stable inc md
    have small (j : ℕ) (le : j≤6) : zeroSpace A j⊓M≤J :=
      fun _ v=>hiddenKernel_of_one_clock ho F full (by decide) le v.1 a (onNode _ v.2)
    have w5 : finrank K (W 5)=6 := by omega
    have w6 : finrank K (W 6)=7 := by omega
    have ic5 := Submodule.finrank_sup_add_finrank_inf_eq (zeroSpace A 5) M
    change finrank K (W 5)+_=_ at ic5
    have eq5 : zeroSpace A 5⊓M=J := Submodule.eq_of_le_of_finrank_le (small 5 (by decide)) (by omega)
    have j5 : J≤zeroSpace A 5 := by rw [←eq5]; exact inf_le_left
    have cost := clock_invariant_outgoing ha (sep.mono (by decide : 5≤9)) j5 clock
    change finrank K J+3≤finrank K (zeroSpace A 6) at cost
    have ic6:= Submodule.finrank_sup_add_finrank_inf_eq (zeroSpace A 6) M
    change finrank K (W 6)+_=_ at ic6
    have ic := Submodule.finrank_mono (small 6 (by decide))
    change finrank K (zeroSpace A 6⊓M : Submodule K (Fin 29→K))≤finrank K J at ic
    omega
  have step (j : ℕ) : W j ⊔ (W j).map C≤W (j+1) := by
    apply sup_le (sup_le_sup_right (zeroSpace_mono A (Nat.le_succ _)) M)
    change (zeroSpace A j⊔M).map C≤zeroSpace A (j+1)⊔M
    rw [Submodule.map_sup]
    exact sup_le ((Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)).trans le_sup_left)
      (L.stable.trans le_sup_right)
  have w5 : finrank K (W 5)=5 ∨ finrank K (W 5)=6 := by
    have e : finrank K M=4 := sameCore ▸ four
    omega
  have cut (j l : ℕ) (a:j≤6) (bb:j≤4+l) : finrank K (core C (W j) l)≤4 := by
    have z:=Submodule.finrank_mono (partners_core_le_hidden ha ho F full (l:=l) a bb)
    rw [four] at z
    change finrank K (core C (localEnlarged A J j) l)≤4 at z
    rwa [←sameCore] at z
  rcases w5 with w5|w5
  · have fiveEq : zeroSpace A 5=W 5 := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have j5 : J≤zeroSpace A 5 := by
      rw [fiveEq]; exact inc.trans le_sup_right
    have cost := clock_invariant_outgoing ha (sep.mono (by decide : 5≤9)) j5 clock
    change finrank K J+3≤finrank K (zeroSpace A 6) at cost
    have low : finrank K (zeroSpace A 6)≤finrank K (W 6) := Submodule.finrank_mono le_sup_left
    have w6 : finrank K (W 6)=7 := by omega
    have w7 : finrank K (W 7)=8 := by omega
    have up:=Submodule.finrank_mono (step 6)
    have c0 := core_rank_step C (W 6) 0
    have c1 := core_rank_step C (W 6) 1
    rw [core_zero] at c0
    change finrank K (W 6⊔(W 6).map C : Submodule K (Fin 29→K))≤finrank K (W 7) at up
    change finrank K (W 6)+finrank K (W 6)≤finrank K (core C (W 6) 1)+_ at c0
    change _+_≤finrank K (core C (W 6) 2)+_ at c1
    have strict := cut 6 2 (by decide) (by decide)
    omega
  · have w6 : finrank K (W 6)=7 := by omega
    have up:=Submodule.finrank_mono (step 5)
    have c0:=core_rank_step C (W 5) 0
    rw [core_zero] at c0
    change finrank K (W 5⊔(W 5).map C : Submodule K (Fin 29→K))≤finrank K (W 6) at up
    change finrank K (W 5)+finrank K (W 5)≤finrank K (core C (W 5) 1)+_ at c0
    have strict:=cut 5 1 (by decide) (by decide)
    omega

/-- The rank-five route is now the only remaining localized nonzero branch. -/
theorem width29_nonzero_small_hidden_rank_five (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) :
    ∃ r U τ, LocalLinearBand A b 8 r U τ ∧ primitiveBack A b 8=annih (treeSpace A 9) ∧
      zeroSpace A 4≤hiddenKernel b τ U ∧ hiddenKernel b τ U≤zeroSpace A 9 ∧
      finrank K (hiddenKernel b τ U)=5 := by
  obtain ⟨r,U,τ,F,full,f4,f9,lo,hi⟩ := width29_nonzero_small_hidden_rank ha ho nz
  have four : finrank K (hiddenKernel b τ U)≠4 :=
    width29_local_hidden_rank_four_impossible ha ho nz F full
  exact ⟨r,U,τ,F,full,f4,f9,by omega⟩

end
end RKResearch.Certified.ERK19
