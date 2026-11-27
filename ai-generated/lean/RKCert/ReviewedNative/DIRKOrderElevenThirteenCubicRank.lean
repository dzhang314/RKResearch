module

public import RKCert.ReviewedNative.DIRKOrderTenSaturation
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! # Native rank inputs for the normalized DIRK11/13 cubic census

The D(1), D(2), C(2) representative and ordinary grade-six surplus
are explicit inputs. No claim that the preceding mathematical
normalization or surplus proof has already been ported is made. -/

namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The actual tree-space flag cannot stall while the two reflected
seeds are both paid at the specified grade. -/
theorem dirk_treeSpace_lt_succ_paidSeeds (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {j : ℕ} (pay : j+4 ≤ p) :
    treeSpace A j < treeSpace A (j+1) := by
  refine lt_of_le_of_ne (treeSpace_mono A (Nat.le_succ j)) ?_
  intro equal
  let W := annih (treeSpace A j)
  have m := mat_treeSpace A j
  have c := reflectedClock_treeSpace A j
  rw [← equal] at m c
  have h := reverse_dirk_seeds_force_clock ha W
    (fun _ hx => annih_map_transpose m (Submodule.mem_map_of_mem hx))
    (fun _ hx => annih_map_diag c (Submodule.mem_map_of_mem hx))
    (reflectedStageRow_annih ho j 1 (by omega))
    (reflectedStageRow_annih ho j 2 pay)
  exact reflected_target_ne_zero ho (by omega)
    (mem_annih.mp h _ (one_mem_treeSpace A j))

/-- At paid order at least two the genuine cubic reflected defect is
not zero if the genuine quadratic reflected defect is zero. -/
theorem reflectedCubic_ne_zero_of_quadraticZero
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 2≤p)
    (d2 : reflectedStageRow A b 1=0) : reflectedStageRow A b 2≠0 := by
  intro g
  let U : Submodule K (Fin s → K) := ⊥
  have z (v : Fin s → K) (hv : v∈U) : v=0 := by simpa [U] using hv
  have h : diag (reflectedClock A) b∈U := reverse_dirk_seeds_force_clock ha U
    (fun v hv => by rw [z v hv,map_zero]; exact U.zero_mem)
    (fun v hv => by rw [z v hv,map_zero]; exact U.zero_mem)
    (by rw [d2]; exact U.zero_mem) (by rw [g]; exact U.zero_mem)
  exact reflected_target_ne_zero ho pay (by rw [z _ h,row_apply,zero_dotProduct])

end RKResearch.Certified.Graded.Reverse

namespace RKResearch.Certified.Graded.OrderElevenThirteen

open RKResearch FiniteRootedTree Module Reverse
open scoped Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 13) (Fin 13) K} {b : Fin 13 → K}

structure Normalized (A : Matrix (Fin 13) (Fin 13) K) (b : Fin 13 → K) : Prop where
  c2 : monomialStageDefect A 1=0
  d1 : reflectedStageRow A b 0=0
  d2 : reflectedStageRow A b 1=0
  surplus : 5≤finrank K (zeroSpace A 6)

private theorem last_live (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b) :
    b (Fin.last 12)≠0 := by
  intro dead
  let U := A.submatrix (@Fin.castSucc 12) (@Fin.castSucc 12)
  let w := fun i : Fin 12 => b i.castSucc
  have hl : U.IsLowerTriangular := fun i j h => ha (show i.castSucc < j.castSucc from h)
  have f (t : FiniteRootedTree) (i : Fin 12) : Φ t U i=Φ t A i.castSucc := by
    induction t generalizing i with
    | leaf => rfl
    | butcherProduct t u ht hu =>
      simp only [Φ,Pi.mul_apply,ht i]
      congr 1
      have z : A i.castSucc (Fin.last 12)=0 := ha (Fin.castSucc_lt_last i)
      simp only [Matrix.mulVec_apply_eq_sum]
      rw [Fin.sum_univ_castSucc (fun j : Fin 13 => A i.castSucc j*Φ u A j),
        z,zero_mul,add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [hu j]
      rfl
  have hon : HasOrder 11 U w := by
    intro t ht
    have e := ho t ht
    rw [dotProduct,Fin.sum_univ_castSucc,dead,zero_mul,add_zero] at e
    simpa only [w,dotProduct,f] using e
  have n := hon.dirk_uniform_stages hl (by decide)
  omega

structure RankCensus (A : Matrix (Fin 13) (Fin 13) K) (b : Fin 13 → K) : Prop where
  origin : ∀ j, A 0 j=0
  terminalWeight : b (Fin.last 12)≠0
  terminalClock : nodes A (Fin.last 12)=1
  terminalColumn : ∀ i, A i (Fin.last 12)=0
  f4 : finrank K (zeroSpace A 4)=2
  f5 : finrank K (zeroSpace A 5)=3
  f6 : finrank K (zeroSpace A 6)=5
  e5 : finrank K (treeSpace A 5)=9
  e6 : finrank K (treeSpace A 6)=11
  e7 : finrank K (treeSpace A 7)=12
  terminalInSix : coordinate (K:=K) (Fin.last 12)∈treeSpace A 6
  terminalOutFive : coordinate (K:=K) (Fin.last 12)∉treeSpace A 5
  terminalCubicClean : monomialStageDefect A 2 (Fin.last 12)=0

/-- The exact paid ranks and live endpoint data used in the paper census. -/
theorem rank_census (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (N : Normalized A b) : RankCensus A b := by
  let t := Fin.last 12
  have live := last_live ha ho
  have ht : LastActive b t := ⟨live,fun j hj => False.elim ((not_lt_of_ge (Fin.le_last j)) hj)⟩
  have hr : ∀ j, A 0 j=0 :=
    dirk_first_row_of_zero_quadratic ha (congrFun N.c2 0)
  have yt := ht.dirk_reflected_zero ha N.d1 N.d2
  have nt : nodes A t=1 := (sub_eq_zero.mp yt).symm
  have lastDiag : A t t=0 := by
    have q := ht.dirk_seed_value ha 0
    rw [N.d1] at q
    simp only [Pi.zero_apply,Nat.reduceAdd,Nat.cast_one,pow_zero,pow_one,mul_one,one_mul,yt,
      mul_zero,sub_zero] at q
    exact (mul_eq_zero.mp q.symm).resolve_right live
  have col (i : Fin 13) : A i t = 0 := by
    rcases lt_or_eq_of_le (Fin.le_last i) with h | h
    · exact ha h
    · rwa [h]
  have eq5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide) (coeff_separated ho (by decide))
  have l4 := (dirk_forward_zeroSpace_rank_floor ha ho (q:=4) (by decide) (by decide)).1
  have l5 := (dirk_forward_zeroSpace_rank_floor ha ho (q:=5) (by decide) (by decide)).1
  have u5 := dirk_terminal_rank_budget ha ho (q:=5) (n:=4) (by decide) (by decide) (by decide)
    hr N.d1 N.d2
  have f5 : finrank K (zeroSpace A 5)=3 := by omega
  have e5 : finrank K (treeSpace A 5)=9 := by omega
  have g4 := Submodule.finrank_lt_finrank_of_lt
    (dirk_forward_zeroSpace_lt_succ ha ho (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at g4
  have f4 : finrank K (zeroSpace A 4)=2 := by omega
  have lo6 := coeff_defect_tree_rank (A:=A) (q:=5) (j:=6) (by decide)
    (coeff_defect_separated_zero_row ho hr (by decide) (by decide))
  have hi6 := dirk_reverse_rank_budget ha ho (q:=6) (n:=3) (by decide) (by decide)
  have sf := N.surplus
  have f6 : finrank K (zeroSpace A 6)=5 := by omega
  have e6 : finrank K (treeSpace A 6)=11 := by omega
  have lo7 := Submodule.finrank_lt_finrank_of_lt
    (dirk_treeSpace_lt_succ_paidSeeds ha ho (j:=6) (by decide))
  change finrank K (treeSpace A 6)<finrank K (treeSpace A 7) at lo7
  have hi7 := dirk_reverse_rank_budget ha ho (q:=7) (n:=2) (by decide) (by decide)
  have e7 : finrank K (treeSpace A 7)=12 := by omega
  have rbinc := primitiveBack_annih ho 6 3 (by decide)
  have rbgain := dirk_primitiveBack_rank_gain ha ho (r:=1) (n:=3) (by decide) (by decide) (by decide)
  have rbcap := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin,e6] at rbcap
  have rbfull : primitiveBack A b 3=annih (treeSpace A 6) := by
    apply Submodule.eq_of_le_of_finrank_le rbinc
    omega
  have et : coordinate (K:=K) t∈treeSpace A 6 := by
    rw [←annih_annih (treeSpace A 6),←rbfull]
    apply mem_annih.mpr
    intro v hv
    have z := mem_tailZero.mp (ht.dirk_primitiveBack_tail ha N.d1 N.d2 3 hv) t le_rfl
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,z]
  have ex := endpoint_coordinate_out_of_zero_row ho (q:=5) (by decide) hr live nt
  let g := monomialStageDefect A 2
  have hG := zeroSpace_mul_treeSpace ho (by decide) (monomialStageDefect_mem A 2) et
  have out := probe_zeroSpace ho (k:=0) (by decide) hG
  have pro : g*coordinate t=g t • coordinate t := by
    classical
    ext i
    by_cases e : i=t
    · subst i; simp [coordinate]
    · simp [coordinate,e]
  change probe A b 0 (g*coordinate t)=0 at out
  rw [pro,map_smul,smul_eq_mul] at out
  change g t*row _ (coordinate t)=0 at out
  rw [row_coordinate,pow_zero,mul_one] at out
  exact ⟨hr,live,nt,col,f4,f5,f6,e5,e6,e7,et,ex,(mul_eq_zero.mp out).resolve_right live⟩

/-- A genuine cubic defect times the literal output weights kills the
paid grade-seven rooted columns. -/
theorem weighted_cubic_annih_seven (ho : HasOrder 11 A b) :
    b * monomialStageDefect A 2∈annih (treeSpace A 7) := by
  apply mem_annih.mpr
  intro v hv
  have h := zeroSpace_mul_treeSpace ho (by decide) (monomialStageDefect_mem A 2) hv
  have z := probe_zeroSpace ho (k:=0) (by decide) h
  rw [←z]
  simp only [row_apply,probe,dotProduct,Pi.mul_apply,pow_zero,mul_one,mul_assoc]

/-- Every nonzero active ordinary cubic gives the entire grade-seven
annihilator, so the genuine reflected cubic has precisely its support. -/
theorem reflected_cubic_proportional (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (N : Normalized A b) (nz : b*monomialStageDefect A 2≠0) :
    ∃ a : K, a≠0 ∧ reflectedStageRow A b 2 = a • (b*monomialStageDefect A 2) := by
  let w := b*monomialStageDefect A 2
  have u := rank_census ha ho N
  have cap := finrank_annih (treeSpace A 7)
  rw [Fintype.card_fin,u.e7] at cap
  have H : (K ∙ w) = annih (treeSpace A 7) := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem w _).mpr (weighted_cubic_annih_seven ho)
    · rw [finrank_span_singleton nz]
      omega
  have M := reflectedStageRow_annih ho 7 2 (by decide)
  rw [←H,Submodule.mem_span_singleton] at M
  obtain ⟨a,e⟩ := M
  refine ⟨a,?_,e.symm⟩
  intro az
  exact (reflectedCubic_ne_zero_of_quadraticZero ha ho (by decide) N.d2) (by rw [←e,az,zero_smul])

/-- Two live cubic-defect labels give exactly the whole grade-six
annihilator. Only the two indicated individual weighted values must be
nonzero; no global weight hypothesis is used. -/
theorem annih_six_eq_cubic_pair (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (N : Normalized A b) {i j : Fin 13}
    (hi : (b*monomialStageDefect A 2) i≠0)
    (hj : (b*monomialStageDefect A 2) j≠0) (diff : nodes A i≠nodes A j) :
    let w := b*monomialStageDefect A 2
    let f : Fin 2 → (Fin 13 → K) := Fin.cases (diag (nodes A) w) (fun _ => w)
    Submodule.span K (Set.range f) = annih (treeSpace A 6) := by
  let w := b*monomialStageDefect A 2
  let f : Fin 2 → (Fin 13 → K) := Fin.cases (diag (nodes A) w) (fun _ => w)
  change Submodule.span K (Set.range f)=annih (treeSpace A 6)
  have hg := weighted_cubic_annih_seven ho
  have hg6 := annih_antitone (treeSpace_mono A (show 6≤7 by decide)) hg
  have hc6 : diag (nodes A) w∈annih (treeSpace A 6) :=
    annih_map_diag (diag_treeSpace A 6) (Submodule.mem_map_of_mem hg)
  have inc : Submodule.span K (Set.range f) ≤ annih (treeSpace A 6) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact Fin.cases hc6 (fun _ => hg6) k
  have independent : LinearIndependent K f := by
    apply linearIndependent_fin2.mpr
    constructor
    · change w≠0
      intro z
      exact hi (congrFun z i)
    · intro a same
      change a • w=diag (nodes A) w at same
      have cancel (u : Fin 13) (hu : w u≠0) : a=nodes A u := by
        apply mul_right_cancel₀ hu
        exact congrFun same u
      exact diff ((cancel i hi).symm.trans (cancel j hj))
  have fd := finrank_span_eq_card independent
  have R := rank_census ha ho N
  have cap := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin,R.e6] at cap
  rw [Fintype.card_fin] at fd
  exact Submodule.eq_of_le_of_finrank_le inc (by omega)

end RKResearch.Certified.Graded.OrderElevenThirteen
