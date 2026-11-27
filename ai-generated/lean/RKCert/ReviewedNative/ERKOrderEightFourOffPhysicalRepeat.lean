module

public import RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalRank

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual unique repeated tag, at the penultimate row

The proof uses the rank-one annihilator of the actual tag space and the
rank-two reverse flag. The only reverse row paid beyond the seed here
is J₁. This is not a row merge or a replacement tableau.
-/
namespace RKResearch.Certified.Graded.FourOffPhysical

open RKResearch Module Polynomial Reverse OneOff ERKTaggedHorizon
open scoped Matrix Classical

section LinearTools
variable {K : Type*} [Field K]

/-- Literal physical contrast, later coordinate minus earlier coordinate. -/
noncomputable def contrast (K : Type*) [Field K] {s : ℕ} (i j : Fin s) : Fin s → K :=
  coordinate (K:=K) j-coordinate (K:=K) i

theorem contrast_early {s : ℕ} {i j : Fin s} (ne : i≠j) :
    contrast K i j i = -1 := by simp [contrast,coordinate_as_single,ne,Ne.symm ne]

theorem contrast_late {s : ℕ} {i j : Fin s} (ne : i≠j) :
    contrast K i j j = 1 := by simp [contrast,coordinate_as_single,ne,Ne.symm ne]

theorem contrast_other {s : ℕ} {i j k : Fin s} (ki : k≠i) (kj : k≠j) :
    contrast K i j k=0 := by
  simp [contrast,coordinate_as_single,ki,kj,Ne.symm ki,Ne.symm kj]

theorem contrast_ne_zero {s : ℕ} {i j : Fin s} (ne : i≠j) : contrast K i j≠0 := by
  intro h
  have e := congrFun h j
  rw [contrast_late ne] at e
  exact one_ne_zero e

theorem contrast_row {s : ℕ} (i j : Fin s) (v : Fin s → K) :
    row (contrast K i j) v=v j-v i := by
  have evalCoord (k : Fin s) : row (coordinate (K:=K) k) v=v k := by
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
  rw [contrast,row_apply,sub_dotProduct,←row_apply,←row_apply]
  simp only [evalCoord]

theorem contrast_annih_tag {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (same : SameTag A i j) : contrast K i j∈annih (onOffSpace A) := by
  apply mem_annih.mpr
  intro v hv
  rw [contrast_row,onOffSpace_apply_eq hv same,sub_self]

/-- Interpolating a singleton detects its coefficient in a finite
weighted sum of degree-d polynomial probes. -/
theorem weights_zero_of_poly {S : Finset K} {w : K → K} {d : ℕ}
    (cap : S.card≤d+1)
    (paid : ∀ V : K[X], V.natDegree≤d → ∑ x ∈ S, w x * V.eval x=0) :
    ∀ x∈S, w x=0 := by
  classical
  intro x hx
  let f : K → K := fun y => if y=x then 1 else 0
  let V := Lagrange.interpolate S id f
  have hd : V.natDegree≤d := by
    by_cases z : V=0
    · simp [z]
    · have t := (natDegree_lt_iff_degree_lt z).mpr
          (Lagrange.degree_interpolate_lt f (Set.injOn_id _) (s:=S))
      omega
  have he (y : K) (hy : y∈S) : V.eval y=f y :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have p := paid V hd
  rw [Finset.sum_eq_single x] at p
  · simpa [he x hx,f] using p
  · intro y hy yx
    simp [he _ hy,f,yx]
  · intro e
    exact (e hx).elim

theorem annih_tag_of_zero_masses {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {w : Fin s → K}
    (hc : ∀ x∈cleanKnots A, cleanMass A w x=0) (ho : ∀ x∈offKnots A, offMass A w x=0) :
    w∈annih (onOffSpace A) := by
  apply mem_annih.mpr
  intro v hv
  obtain ⟨z,rfl⟩ := hv
  let f (x : K) := if p : x∈cleanKnots A then z.1 ⟨x,p⟩ else 0
  let t (x : K) := if p : x∈offKnots A then z.2 ⟨x,p⟩ else 0
  have ev : onOffEval A z=taggedValue A f t := by
    ext i
    by_cases hi : g A i=0
    · rw [onOffEval_on A z hi]
      simp only [taggedValue,if_pos hi,f,dif_pos (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)]
    · rw [onOffEval_off A z hi]
      simp only [taggedValue,if_neg hi,t,dif_pos (mem_offKnots.mpr ⟨i,hi,rfl⟩)]
  rw [ev,row_taggedValue]
  have c : (∑ x ∈ cleanKnots A, cleanMass A w x*f x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [hc x hx,zero_mul])
  have o : (∑ x ∈ offKnots A, offMass A w x*t x)=0 :=
    Finset.sum_eq_zero (fun x hx => by rw [ho x hx,zero_mul])
  rw [c,o,add_zero]

end LinearTools

section RankOne

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]}

private noncomputable def tagOf (A : Matrix (Fin 10) (Fin 10) K) (i : Fin 10) :
    (cleanKnots A) ⊕ (offKnots A) :=
  if h : g A i=0 then Sum.inl ⟨nodes A i,mem_cleanKnots.mpr ⟨i,h,rfl⟩⟩
  else Sum.inr ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩

private theorem same_of_tagOf {i j : Fin 10} (e : tagOf A i=tagOf A j) : SameTag A i j := by
  by_cases hi : g A i=0 <;> by_cases hj : g A j=0
  · simp only [tagOf,dif_pos hi,dif_pos hj,Sum.inl.injEq,Subtype.mk.injEq] at e
    exact ⟨e,iff_of_true hi hj⟩
  · simp [tagOf,hi,hj] at e
  · simp [tagOf,hi,hj] at e
  · simp only [tagOf,dif_neg hi,dif_neg hj,Sum.inr.injEq,Subtype.mk.injEq] at e
    exact ⟨e,iff_of_false hi hj⟩

private theorem has_repeat (D : RankData A b P) : ∃ i j : Fin 10, i<j ∧ SameTag A i j := by
  by_contra no
  have inj : Function.Injective (tagOf A) := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt|lt
    · exact no ⟨i,j,lt,same_of_tagOf eq⟩
    · exact no ⟨j,i,lt,(same_of_tagOf eq).symm⟩
  have c := Fintype.card_le_of_injective (tagOf A) inj
  rw [Fintype.card_fin,Fintype.card_sum,Fintype.card_coe,Fintype.card_coe,D.cleanCard,D.offCard] at c
  omega

theorem annih_five_eq_span (D : RankData A b P) {i j : Fin 10}
    (ij : i<j) (same : SameTag A i j) :
    annih (treeSpace A 5) = K ∙ contrast K i j := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply (Submodule.span_singleton_le_iff_mem _ _).2
    rw [D.treeFive]
    exact contrast_annih_tag same
  have a := finrank_annih (treeSpace A 5)
  rw [D.rankFive,Fintype.card_fin] at a
  rw [finrank_span_singleton (contrast_ne_zero (ne_of_lt ij))]
  omega

theorem repeat_pair_unique (D : RankData A b P) {i j : Fin 10}
    (ij : i<j) (same : SameTag A i j) :
    ∀ {u v : Fin 10}, u<v → SameTag A u v → u=i ∧ v=j := by
  intro u v uv suv
  have m : contrast K u v ∈ K ∙ contrast K i j := by
    rw [←annih_five_eq_span D ij same,D.treeFive]
    exact contrast_annih_tag suv
  obtain ⟨scale,e⟩ := Submodule.mem_span_singleton.mp m
  have inpair (k : Fin 10) (nz : contrast K u v k≠0) : k=i ∨ k=j := by
    by_contra! no
    have z := congrFun e k
    change scale*contrast K i j k=contrast K u v k at z
    rw [contrast_other no.1 no.2,mul_zero] at z
    exact nz z.symm
  have U := inpair u (by rw [contrast_early (ne_of_lt uv)]; exact neg_ne_zero.mpr one_ne_zero)
  have V := inpair v (by rw [contrast_late (ne_of_lt uv)]; exact one_ne_zero)
  rcases U with rfl|rfl <;> rcases V with rfl|rfl
  · exact (lt_irrefl _ uv).elim
  · exact ⟨rfl,rfl⟩
  · exact ((not_lt_of_ge ij.le) uv).elim
  · exact (lt_irrefl _ uv).elim

theorem transpose_contrast_apply (A : Matrix (Fin 10) (Fin 10) K) (i j k : Fin 10) :
    mat A.transpose (contrast K i j) k=A j k-A i k := by
  have evalCoord (q : Fin 10) : mat A.transpose (coordinate (K:=K) q) k=A q k := by
    change row (A.transpose k) (coordinate (K:=K) q)=A q k
    simp only [row_coordinate,Matrix.transpose_apply]
  simp only [contrast,map_sub,Pi.sub_apply,evalCoord]

private theorem back_one_eq_quad (D : RankData A b P) :
    back A b 1=K ∙ quadraticSeed A b := by
  have b0 : back A b 0=⊥ := by
    change K ∙ firstSeed A b=⊥
    rw [D.horizon.firstZero,Submodule.span_zero_singleton]
  change back A b 0 ⊔ (back A b 0).map (mat A.transpose) ⊔
    (back A b 0).map (diag (reflectedClock A)) ⊔ K ∙ quadraticSeed A b=_
  simp [b0]

theorem back_one_eq_contrast (D : RankData A b P) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    back A b 1=K ∙ contrast K i j := by
  have eq := annih_five_eq_span D ij same
  rw [←eq]
  apply Submodule.eq_of_le_of_finrank_le (back_annih ho 5 1 (by decide))
  rw [eq,finrank_span_singleton (contrast_ne_zero (ne_of_lt ij)),(D.horizon.flagExact 1 (by decide)).1]

theorem quadraticSeed_is_contrast (D : RankData A b P) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    ∃ ρ : K, ρ≠0 ∧ quadraticSeed A b=ρ • contrast K i j := by
  have m : quadraticSeed A b ∈ back A b 1 := by
    rw [back_one_eq_quad D]
    exact Submodule.mem_span_singleton_self _
  rw [back_one_eq_contrast D ho ij same] at m
  obtain ⟨ρ,e⟩ := Submodule.mem_span_singleton.mp m
  refine ⟨ρ,?_,e.symm⟩
  intro z
  have quad0 : quadraticSeed A b=0 := e.symm.trans (by simp [z])
  have d := (D.horizon.flagExact 1 (by decide)).1
  rw [back_one_eq_quad D,quad0,Submodule.span_zero_singleton] at d
  simp at d

private theorem clock_contrast {i j : Fin 10} (same : SameTag A i j) :
    diag (reflectedClock A) (contrast K i j)=reflectedClock A j • contrast K i j := by
  ext k
  by_cases ki : k=i
  · subst k
    have eq : reflectedClock A i=reflectedClock A j := by
      simp only [reflectedClock,Pi.sub_apply,Pi.one_apply,same.1]
    simp [eq]
  · by_cases kj : k=j
    · subst k
      simp
    · simp [contrast_other ki kj]

theorem annih_four_eq_two (D : RankData A b P) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    annih (treeSpace A 4)=K ∙ contrast K i j ⊔ K ∙ mat A.transpose (contrast K i j) := by
  rw [←D.horizon.full]
  have b1 := back_one_eq_contrast D ho ij same
  have s1 : K ∙ quadraticSeed A b=K ∙ contrast K i j :=
    (back_one_eq_quad D).symm.trans b1
  change back A b 1 ⊔ (back A b 1).map (mat A.transpose) ⊔
    (back A b 1).map (diag (reflectedClock A)) ⊔ K ∙ quadraticSeed A b=_
  rw [b1,s1,Submodule.map_span,Set.image_singleton,Submodule.map_span,Set.image_singleton,
    clock_contrast same]
  have s : (K ∙ (reflectedClock A j • contrast K i j)) ≤
      K ∙ contrast K i j :=
    (Submodule.span_singleton_le_iff_mem _ _).2
      ((K ∙ contrast K i j).smul_mem _ (Submodule.mem_span_singleton_self _))
  let U : Submodule K (Fin 10 → K) := K ∙ contrast K i j
  let V : Submodule K (Fin 10 → K) := K ∙ mat A.transpose (contrast K i j)
  let S : Submodule K (Fin 10 → K) := K ∙ (reflectedClock A j • contrast K i j)
  change ((U ⊔ V) ⊔ S) ⊔ U=U ⊔ V
  have hSU : S ≤ U := s
  have hU : U ≤ U ⊔ V := le_sup_left
  rw [sup_eq_left.mpr (hSU.trans hU),sup_eq_left.mpr hU]

theorem transpose_contrast_not_in_annih_five (D : RankData A b P) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    mat A.transpose (contrast K i j) ∉ annih (treeSpace A 5) := by
  intro w
  rw [annih_five_eq_span D ij same] at w
  have e := annih_four_eq_two D ho ij same
  rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).2 w)] at e
  have r := finrank_annih (treeSpace A 4)
  rw [D.horizon.treeRank,e,finrank_span_singleton (contrast_ne_zero (ne_of_lt ij)),Fintype.card_fin] at r
  omega

theorem transpose_contrast_offMass_ne (D : RankData A b P) (ho : HasOrder 8 A b)
    {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    ∀ x∈offKnots A, offMass A (mat A.transpose (contrast K i j)) x ≠ 0 := by
  classical
  let δ := mat A.transpose (contrast K i j)
  have m : δ∈annih (treeSpace A 4) := by
    rw [annih_four_eq_two D ho ij same]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  intro x hx one0
  let S := (offKnots A).erase x
  have size := Finset.card_erase_add_one hx
  have offCard := D.offCard
  have cap : S.card≤2+1 := by change ((offKnots A).erase x).card≤3; omega
  have off0 : ∀ y∈offKnots A, offMass A δ y=0 := by
    have wc : ∀ V : K[X], V.natDegree≤2 →
        ∑ y ∈ S, (offMass A δ y * P.eval y) * V.eval y=0 := by
      intro V hd
      have fb : diag (g A) (evalNodes A V) ∈ zeroSpace A 4 := by
        rw [D.bandFour]
        exact band_iff.mpr ⟨V,hd,rfl⟩
      have w := mem_annih.mp m _ (zeroSpace_le_treeSpace A 4 fb)
      rw [row_g_profile_tag_sum δ D.fit V] at w
      have er : (∑ y ∈ S, offMass A δ y * (P.eval y * V.eval y)) =
          ∑ y ∈ offKnots A, offMass A δ y * (P.eval y * V.eval y) := by
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro y hy n
        have e : y=x := by by_contra ne; exact n (Finset.mem_erase.mpr ⟨ne,hy⟩)
        subst y
        have z : offMass A δ x = 0 := one0
        rw [z,zero_mul]
      rw [←er] at w
      simpa only [mul_assoc] using w
    have all := weights_zero_of_poly cap wc
    intro y hy
    by_cases e : y=x
    · simpa only [e] using one0
    have W := all y (Finset.mem_erase.mpr ⟨e,hy⟩)
    obtain ⟨k,hk,ck⟩ := mem_offKnots.mp hy
    have pn : P.eval y≠0 := by rw [←ck,D.fit k hk]; exact hk
    exact (mul_eq_zero.mp W).resolve_right pn
  have clean0 : ∀ y∈cleanKnots A, cleanMass A δ y=0 := by
    have cleanCard := D.cleanCard
    apply weights_zero_of_poly (d:=4) (by omega : (cleanKnots A).card≤4+1)
    intro V hd
    have w := mem_annih.mp m _ (evalNodes_mem_treeSpace A V hd)
    rw [row_evalNodes_tag_sum] at w
    have z : (∑ y ∈ offKnots A, offMass A δ y * V.eval y)=0 :=
      Finset.sum_eq_zero (fun y hy => by rw [off0 _ hy,zero_mul])
    simpa only [z,add_zero] using w
  apply transpose_contrast_not_in_annih_five D ho ij same
  rw [D.treeFive]
  exact annih_tag_of_zero_masses clean0 off0

theorem off_tags_before_repeat (D : RankData A b P) (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) {i j : Fin 10} (ij : i<j) (same : SameTag A i j) :
    ∀ x∈offKnots A, ∃ k : Fin 10, k<j ∧ g A k≠0 ∧ nodes A k=x := by
  classical
  intro x hx
  by_contra none
  have nz := transpose_contrast_offMass_ne D ho ij same x hx
  apply nz
  unfold offMass
  apply Finset.sum_eq_zero
  intro k _
  by_cases hit : g A k≠0 ∧ nodes A k=x
  · have jle : j≤k := le_of_not_gt (fun e => none ⟨k,e,hit.1,hit.2⟩)
    rw [if_pos hit,transpose_contrast_apply,ha j k jle,ha i k (ij.le.trans jle),sub_zero]
  · simp [hit]

end RankOne

section Penultimate

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]}

private theorem exists_latest_weighted (ho : HasOrder 8 A b) :
    ∃ t : Fin 10, b t*reflectedClock A t≠0 ∧
      ∀ k : Fin 10, t<k → b k*reflectedClock A k=0 := by
  classical
  let S : Finset (Fin 10) := Finset.univ.filter (fun i => b i*reflectedClock A i≠0)
  have sn : S.Nonempty := by
    by_contra no
    have z : diag (reflectedClock A) b=0 := by
      ext i
      have q : b i*reflectedClock A i=0 := by
        by_contra ni
        exact no ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ni⟩⟩
      simpa [diag_apply,mul_comm] using q
    apply reflected_target_ne_zero ho (by decide)
    rw [z]
    simp [row_apply,dotProduct]
  refine ⟨S.max' sn,(Finset.mem_filter.mp (S.max'_mem sn)).2,?_⟩
  intro k lt
  by_contra nk
  exact (not_le_of_gt lt) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,nk⟩))

/-- Literal reverse row at and after the latest nonzero reflected-weight
coordinate. For any positive exponent its integration term has vanished. -/
theorem reflected_row_tail (ha : ∀ i j, i≤j → A i j=0)
    {t : Fin 10} (after : ∀ l : Fin 10, t<l → b l*reflectedClock A l=0)
    {k : Fin 10} (le : t≤k) {m : ℕ} (hm : 0<m) :
    reflectedStageRow A b m k= -(b k*(reflectedClock A k)^(m+1)) := by
  have tail (l : Fin 10) (lt : t<l) : reflectedStageWeight A b m l=0 := by
    rcases mul_eq_zero.mp (after l lt) with u|v
    · simp [reflectedStageWeight,u]
    · simp [reflectedStageWeight,v,ne_of_gt hm]
  have q := transpose_tail_zero ha tail le
  change (A.transpose *ᵥ reflectedStageWeight A b m) k=0 at q
  simp [reflectedStageRow,Pi.smul_apply,reflectedStageWeight,q]

/-- The second occurrence of the unique repeat is literal physical row 8.
All off tags have a physical representative before it. -/
structure RepeatAtEight (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K)
    (i : Fin 10) : Prop where
  before : i<8
  same : SameTag A i 8
  unique : ∀ {u v : Fin 10}, u<v → SameTag A u v → u=i ∧ v=8
  kernel : annih (treeSpace A 5)=K ∙ contrast K i 8
  reverseSpace : annih (treeSpace A 4)=K ∙ contrast K i 8 ⊔ K ∙ mat A.transpose (contrast K i 8)
  transposeResidues : ∀ x∈offKnots A, offMass A (mat A.transpose (contrast K i 8)) x≠0
  earlierOff : ∀ x∈offKnots A, ∃ k : Fin 10, k<8 ∧ g A k≠0 ∧ nodes A k=x
  liveEight : b 8≠0
  reflEight : reflectedClock A 8≠0
  quad : quadraticSeed A b = (-(b 8*(reflectedClock A 8)^2)) • contrast K i 8

theorem repeatAtEight_of_rankData (D : RankData A b P)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) :
    ∃ i, RepeatAtEight A b i := by
  obtain ⟨i,j,ij,same⟩ := has_repeat D
  obtain ⟨ρ,ρn,seed⟩ := quadraticSeed_is_contrast D ho ij same
  obtain ⟨t,tLive,tAfter⟩ := exists_latest_weighted (A:=A) (b:=b) ho
  have jn : quadraticSeed A b j≠0 := by
    rw [seed]
    simpa [Pi.smul_apply,smul_eq_mul,contrast_late (ne_of_lt ij)] using ρn
  have bu : b t≠0 := fun z => tLive (by simp [z])
  have yu : reflectedClock A t≠0 := fun z => tLive (by simp [z])
  have tn : quadraticSeed A b t≠0 := by
    change reflectedStageRow A b 1 t≠0
    rw [reflected_row_tail ha tAfter le_rfl (by decide)]
    exact neg_ne_zero.mpr (mul_ne_zero bu (pow_ne_zero _ yu))
  have jle : j≤t := by
    apply le_of_not_gt
    intro tj
    apply jn
    change reflectedStageRow A b 1 j=0
    rw [reflected_row_tail ha tAfter tj.le (by decide)]
    have z := tAfter j tj
    rw [show (1+1:ℕ)=2 by decide,pow_two,←mul_assoc,z,zero_mul,neg_zero]
  have tle : t≤j := by
    apply le_of_not_gt
    intro jt
    apply tn
    rw [seed,Pi.smul_apply,contrast_other (ne_of_gt (ij.trans jt)) (ne_of_gt jt),smul_zero]
  have te : t=j := le_antisymm tle jle
  subst t
  have uj : ∀ {u v : Fin 10}, u<v → SameTag A u v → u=i ∧ v=j := by
    intro u v uv tag
    exact repeat_pair_unique D ij same uv tag
  have early := off_tags_before_repeat D ha ho ij same
  have only_last (k : Fin 10) (jk : j<k) : k=9 := by
    have kg : g A k=0 := by
      by_contra ko
      obtain ⟨l,lj,lo,lc⟩ := early _ (mem_offKnots.mpr ⟨k,ko,rfl⟩)
      have T : SameTag A l k := ⟨lc,iff_of_false lo ko⟩
      exact (ne_of_gt jk) (uj (lj.trans jk) T).2
    have one_tag (l : Fin 10) (lg : g A l=0) (lc : nodes A l=nodes A k) : l=k := by
      by_contra ne
      have T : SameTag A l k := ⟨lc,iff_of_true lg kg⟩
      rcases lt_or_gt_of_ne ne with lt|lt
      · exact (ne_of_gt jk) (uj lt T).2
      · have e : k=i := (uj lt T.symm).1
        exact (ne_of_gt (ij.trans jk)) e
    have nonzero := D.cleanMassNe _ (mem_cleanKnots.mpr ⟨k,kg,rfl⟩)
    rw [cleanMass_singleton b kg one_tag] at nonzero
    have zy : reflectedClock A k=0 := (mul_eq_zero.mp (tAfter k jk)).resolve_left nonzero
    have c1 : nodes A k=1 := (sub_eq_zero.mp zy).symm
    exact D.uniqueOne k kg c1
  have y9 : reflectedClock A 9=0 := by
    change (1:K)-nodes A 9=0
    simp [D.clockNine]
  have jlt : j<(9:Fin 10) := by
    apply lt_of_le_of_ne (Fin.le_last j)
    intro e
    exact yu (e ▸ y9)
  have jge : ¬ j<(8:Fin 10) := by
    intro e
    exact (by decide : (8:Fin 10)≠9) (only_last 8 e)
  have j8 : j=(8:Fin 10) := by
    apply Fin.ext
    change j.val=8
    change j.val<9 at jlt
    change ¬ j.val<8 at jge
    omega
  subst j
  have q8 : quadraticSeed A b 8=-(b 8*(reflectedClock A 8)^2) := by
    change reflectedStageRow A b 1 8=_
    exact reflected_row_tail ha tAfter le_rfl (by decide)
  have rho : ρ=-(b 8*(reflectedClock A 8)^2) := by
    have e := congrFun seed 8
    rw [q8,Pi.smul_apply,smul_eq_mul,contrast_late (ne_of_lt ij),mul_one] at e
    exact e.symm
  refine ⟨i,ij,same,uj,annih_five_eq_span D ij same,annih_four_eq_two D ho ij same,
    transpose_contrast_offMass_ne D ho ij same,early,bu,yu,?_⟩
  rw [←rho,seed]

/-- Independently consumable upstream producer for the actual repeat;
no chronology result about rows 6 or 7 is assumed. -/
theorem rank_and_repeat_of_order8_four_off (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (off : (offKnots A).card=4) :
    ∃ P : K[X], RankData A b P ∧ ∃ i : Fin 10, RepeatAtEight A b i := by
  obtain ⟨P,D⟩ := rankData_of_order8_four_off ha ho off
  exact ⟨P,D,repeatAtEight_of_rankData D ha ho⟩

end Penultimate
end RKResearch.Certified.Graded.FourOffPhysical
