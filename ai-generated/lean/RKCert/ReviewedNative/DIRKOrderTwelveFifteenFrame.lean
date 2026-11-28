module

public import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! Actual paid HasOrder 12 equality data for fifteen DIRK stages.
The grade-six surplus and the live physical final weight are explicit
inputs. The latter follows in the mathematical application by trimming
against the already proved global fifteen-stage floor. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen

open RKResearch Module Reverse
open scoped Matrix

set_option maxHeartbeats 5000000

variable {K : Type*} [Field K]
    {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}

structure EqualityFrame (A : Matrix (Fin 15) (Fin 15) K) (b : Fin 15 → K) : Prop where
  t6 : finrank K (treeSpace A 6) = 12
  t7 : finrank K (treeSpace A 7) = 13
  t8 : finrank K (treeSpace A 8) = 14
  t9 : finrank K (treeSpace A 9) = 15
  f5_upper : finrank K (zeroSpace A 5) ≤ 4
  firstSeeds : reflectedStageRow A b 0 = 0 ∧ reflectedStageRow A b 1 = 0
  lastClock : nodes A (Fin.last 14) = 1
  lastColumn : ∀ i, A i (Fin.last 14) = 0
  lastInSix : coordinate (K:=K) (Fin.last 14) ∈ treeSpace A 6
  lastOutFive : coordinate (K:=K) (Fin.last 14) ∉ treeSpace A 5
  lastClean : ∀ f ∈ zeroSpace A 5, f (Fin.last 14) = 0
  quadraticInvisible : ∀ i, b i * monomialStageDefect A 1 i = 0
  C2_ranks : monomialStageDefect A 1 = 0 →
    finrank K (zeroSpace A 3) = 1 ∧ finrank K (zeroSpace A 6) = 5
  nonC2_ranks : monomialStageDefect A 1 ≠ 0 →
    finrank K (zeroSpace A 3) = 2 ∧ finrank K (zeroSpace A 4) = 3 ∧
    finrank K (zeroSpace A 5) = 4 ∧ finrank K (zeroSpace A 6) = 6
  nonC2_noZeroRow : monomialStageDefect A 1 ≠ 0 → ¬ ∃ i, ∀ j, A i j = 0

theorem equality_frame (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (surplus : finrank K (zeroSpace A 3) + 4 ≤ finrank K (zeroSpace A 6))
    (live : b (Fin.last 14) ≠ 0) : EqualityFrame A b := by
  let t : Fin 15 := Fin.last 14
  have L : LastActive b t :=
    ⟨live, fun i hi => False.elim ((not_lt_of_ge (Fin.le_last i)) hi)⟩
  have f3 := dirk_forward_rank_three ha ho (by decide)
  have q5 := coeff_defect_separated_paid (q:=5) (j:=6) ho (by decide) (by decide)
  have n6 := coeff_defect_tree_rank (A:=A) (q:=5) (j:=6) (by decide) q5
  have u6 := dirk_reverse_rank_budget ha ho (q:=6) (n:=4) (by decide) (by decide)
  have l6 : 12 ≤ finrank K (treeSpace A 6) := by
    by_cases c2 : monomialStageDefect A 1 = 0
    · have zrow : ∀ j, A 0 j=0 :=
        dirk_first_row_of_zero_quadratic ha (congrFun c2 0)
      have a6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide)
        (coeff_defect_separated_zero_row ho zrow (by decide) (by decide))
      omega
    · have hi := f3.2 c2
      omega
  have t6 : finrank K (treeSpace A 6)=12 := by omega
  have s0 : finrank K (primitiveBack A b 1)=0 := by omega
  obtain ⟨d1,d2⟩ := dirk_primitiveBack_one_zero s0
  have e7lo := Submodule.finrank_lt_finrank_of_lt
    (dirk_treeSpace_lt_succ_paidSeeds ha ho (j:=6) (by decide))
  have e8lo := Submodule.finrank_lt_finrank_of_lt
    (dirk_treeSpace_lt_succ_paidSeeds ha ho (j:=7) (by decide))
  have e9lo := Submodule.finrank_lt_finrank_of_lt
    (dirk_treeSpace_lt_succ_paidSeeds ha ho (j:=8) (by decide))
  change finrank K (treeSpace A 6)<finrank K (treeSpace A 7) at e7lo
  change finrank K (treeSpace A 7)<finrank K (treeSpace A 8) at e8lo
  change finrank K (treeSpace A 8)<finrank K (treeSpace A 9) at e9lo
  have e7hi := dirk_reverse_rank_budget ha ho (q:=7) (n:=3) (by decide) (by decide)
  have e8hi := dirk_reverse_rank_budget ha ho (q:=8) (n:=2) (by decide) (by decide)
  have e9hi := dirk_reverse_rank_budget ha ho (q:=9) (n:=1) (by decide) (by decide)
  have t7 : finrank K (treeSpace A 7)=13 := by omega
  have t8 : finrank K (treeSpace A 8)=14 := by omega
  have t9 : finrank K (treeSpace A 9)=15 := by omega
  have nt0 := L.dirk_reflected_zero ha d1 d2
  have nt : nodes A t=1 := (sub_eq_zero.mp nt0).symm
  have lastDiag : A t t=0 := by
    have q := L.dirk_seed_value ha 0
    rw [d1] at q
    simp only [Pi.zero_apply,Nat.reduceAdd,Nat.cast_one,pow_zero,pow_one,mul_one,one_mul,nt0,
      mul_zero,sub_zero] at q
    exact (mul_eq_zero.mp q.symm).resolve_right live
  have col (i : Fin 15) : A i t=0 := by
    rcases lt_or_eq_of_le (Fin.le_last i) with hi | hi
    · exact ha hi
    · rwa [hi]
  have inc := primitiveBack_annih ho 6 4 (by decide)
  have lo := dirk_primitiveBack_rank_gain ha ho (r:=1) (n:=4) (by decide) (by decide) (by decide)
  have cap := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin,t6] at cap
  have same : primitiveBack A b 4=annih (treeSpace A 6) := by
    apply Submodule.eq_of_le_of_finrank_le inc
    omega
  have tin : coordinate (K:=K) t∈treeSpace A 6 := by
    rw [←annih_annih (treeSpace A 6),←same]
    apply mem_annih.mpr
    intro v hv
    have z := mem_tailZero.mp (L.dirk_primitiveBack_tail ha d1 d2 4 hv) t le_rfl
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,z]
  have tout := endpoint_coordinate_out_unanchored ho (q:=5) (by decide) live nt
  have clean (f : Fin 15 → K) (hf : f∈zeroSpace A 5) : f t=0 := by
    have z : probe A b 0 (f * coordinate (K:=K) t)=0 := probe_zeroSpace (j:=11) (k:=0) ho (by decide)
      (zeroSpace_mul_treeSpace ho (by decide) hf tin)
    have eq : f * coordinate (K:=K) t=f t • coordinate (K:=K) t := by
      ext i
      by_cases hi : i=t <;> simp [hi,coordinate]
    rw [eq,map_smul,smul_eq_mul] at z
    have unit : probe A b 0 (coordinate (K:=K) t)=b t := by
      change row (fun j => b j * (nodes A j)^0) (coordinate t)=b t
      rw [row_coordinate,pow_zero,mul_one]
    rw [unit] at z
    exact (mul_eq_zero.mp z).resolve_right live
  have all : treeSpace A 9=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_fin_fun,Fintype.card_fin] using t9
  have invis (i : Fin 15) : b i * monomialStageDefect A 1 i = 0 := by
    have q : coordinate (K:=K) i ∈ treeSpace A 9 := by rw [all]; trivial
    have h : probe A b 0 (monomialStageDefect A 1 * coordinate (K:=K) i)=0 :=
      probe_zeroSpace (j:=11) (k:=0) ho (by decide)
      (zeroSpace_mul_treeSpace ho (by decide) (monomialStageDefect_mem A 1) q)
    have eq : monomialStageDefect A 1 * coordinate (K:=K) i =
        monomialStageDefect A 1 i • coordinate (K:=K) i := by
      ext j
      by_cases hj : j=i <;> simp [hj,coordinate]
    rw [eq,map_smul,smul_eq_mul] at h
    have unit : probe A b 0 (coordinate (K:=K) i)=b i := by
      change row (fun j => b j * (nodes A j)^0) (coordinate i)=b i
      rw [row_coordinate,pow_zero,mul_one]
    rwa [unit,mul_comm] at h
  have eq5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide) (coeff_separated ho (by decide))
  have bound5 := dirk_reverse_room_unanchored ha ho (q:=5) (n:=5) (by decide) (by decide) (by decide)
  have f5up : finrank K (zeroSpace A 5) ≤ 4 := by omega
  have g3 := Submodule.finrank_lt_finrank_of_lt
    (dirk_forward_zeroSpace_lt_succ ha ho (j:=3) (by decide) (by decide))
  have g4 := Submodule.finrank_lt_finrank_of_lt
    (dirk_forward_zeroSpace_lt_succ ha ho (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at g3
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at g4
  refine ⟨t6,t7,t8,t9,f5up,⟨d1,d2⟩,nt,col,tin,tout,clean,invis,?_,?_,?_⟩
  · intro c2
    have zrow : ∀ j, A 0 j=0 :=
      dirk_first_row_of_zero_quadratic ha (congrFun c2 0)
    have q6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide)
      (coeff_defect_separated_zero_row ho zrow (by decide) (by decide))
    omega
  · intro nc2
    have hi := f3.2 nc2
    omega
  · intro nc2 ⟨o,hrow⟩
    have hi := f3.2 nc2
    have eq6 := treeSpace_rank_eq_of_separation ho (q:=6) (by decide)
      (coeff_defect_separated_zero_row ho hrow (by decide) (by decide))
    omega

#print axioms equality_frame

end RKResearch.Certified.Graded.OrderTwelveFifteen
