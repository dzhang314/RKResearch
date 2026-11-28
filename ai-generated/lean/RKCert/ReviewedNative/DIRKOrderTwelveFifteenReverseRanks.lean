module

public import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFrame

@[expose] public section

/-! Paid terminal-zero reverse closure through grade six on the order-12
equality face with forward defect rank four through grade five. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen

open RKResearch Module Reverse
open scoped Matrix

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K]
    {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}

structure ReverseFourFrame (A : Matrix (Fin 15) (Fin 15) K) (b : Fin 15 → K) : Prop where
  gradeThreeRank : finrank K (primitiveBack A b 2) = 1
  gradeFourRank : finrank K (primitiveBack A b 3) = 2
  gradeFiveRank : finrank K (primitiveBack A b 4) = 3
  gradeSixRank : finrank K (primitiveBack A b 5) = 4
  gradeThree : primitiveBack A b 2 = annih (treeSpace A 8)
  gradeFour : primitiveBack A b 3 = annih (treeSpace A 7)
  gradeFive : primitiveBack A b 4 = annih (treeSpace A 6)
  gradeSix : primitiveBack A b 5 = zeroAt (annih (treeSpace A 5)) (Fin.last 14)

theorem equality_reverse_prefix (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) :
    (primitiveBack A b 2 = annih (treeSpace A 8) ∧
      finrank K (primitiveBack A b 2) = 1) ∧
    (primitiveBack A b 3 = annih (treeSpace A 7) ∧
      finrank K (primitiveBack A b 3) = 2) ∧
    (primitiveBack A b 4 = annih (treeSpace A 6) ∧
      finrank K (primitiveBack A b 4) = 3) := by
  have base (n q : ℕ) (hn : 1≤n) (pay : q+n+2≤12)
      (c : finrank K (treeSpace A q) + (n-1)=15) :
      primitiveBack A b n=annih (treeSpace A q) ∧
         finrank K (primitiveBack A b n)=n-1 := by
    have inc := primitiveBack_annih ho q n pay
    have hi := Submodule.finrank_mono inc
    have lo := dirk_primitiveBack_rank_gain ha ho (r:=1) (by decide) hn (by omega)
    have rc := finrank_annih (treeSpace A q)
    rw [Fintype.card_fin] at rc
    exact ⟨Submodule.eq_of_le_of_finrank_le inc (by omega),by omega⟩
  exact ⟨base 2 8 (by decide) (by decide) (by rw [H.t8]),
    base 3 7 (by decide) (by decide) (by rw [H.t7]),
    base 4 6 (by decide) (by decide) (by rw [H.t6])⟩

theorem equality_reverse_six_cap (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) (live : b (Fin.last 14) ≠ 0) :
    primitiveBack A b 5 ≤ zeroAt (annih (treeSpace A 5)) (Fin.last 14) ∧
      finrank K (primitiveBack A b 5) + finrank K (zeroSpace A 5) ≤ 8 := by
  let t : Fin 15 := Fin.last 14
  have L : LastActive b t :=
    ⟨live, fun i hi => False.elim ((not_lt_of_ge (Fin.le_last i)) hi)⟩
  obtain ⟨d1,d2⟩ := H.firstSeeds
  have inc : primitiveBack A b 5 ≤ zeroAt (annih (treeSpace A 5)) t := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho 5 5 (by decide) hv,
      mem_tailZero.mp (L.dirk_primitiveBack_tail ha d1 d2 5 hv) t le_rfl⟩
  have i := Submodule.finrank_mono inc
  have debit := finrank_zeroAt_annih (treeSpace A 5) t H.lastOutFive
  have cap := finrank_annih (treeSpace A 5)
  rw [Fintype.card_fin] at cap
  have t5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide) (coeff_separated ho (by decide))
  exact ⟨inc,by omega⟩

/-- Only q=5's 2q+2 budget is used for the last reverse stage of this flag. -/
theorem equality_reverse_four (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) (live : b (Fin.last 14) ≠ 0)
    (f5 : finrank K (zeroSpace A 5) = 4) : ReverseFourFrame A b := by
  let t : Fin 15 := Fin.last 14
  have L : LastActive b t :=
    ⟨live, fun i hi => False.elim ((not_lt_of_ge (Fin.le_last i)) hi)⟩
  obtain ⟨d1,d2⟩ := H.firstSeeds
  have min (n : ℕ) (hn : 1≤n) (pay : n+1≤12) :
      n-1 ≤ finrank K (primitiveBack A b n) :=
    (Nat.le_add_right _ _).trans (dirk_primitiveBack_rank_gain ha ho (r:=1) (by decide) hn pay)
  have base (n q : ℕ) (hn : 1≤n) (pay : q+n+2≤12)
      (c : finrank K (treeSpace A q) + (n-1)=15) :
      finrank K (primitiveBack A b n)=n-1 ∧ primitiveBack A b n=annih (treeSpace A q) := by
    have inc := primitiveBack_annih ho q n pay
    have hi := Submodule.finrank_mono inc
    have lo := min n hn (by omega)
    have rc := finrank_annih (treeSpace A q)
    rw [Fintype.card_fin] at rc
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  have ⟨r3,b3⟩ := base 2 8 (by decide) (by decide) (by rw [H.t8])
  have ⟨r4,b4⟩ := base 3 7 (by decide) (by decide) (by rw [H.t7])
  have ⟨r5,b5⟩ := base 4 6 (by decide) (by decide) (by rw [H.t6])
  have b6inc : primitiveBack A b 5 ≤ zeroAt (annih (treeSpace A 5)) t := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho 5 5 (by decide) hv,
      mem_tailZero.mp (L.dirk_primitiveBack_tail ha d1 d2 5 hv) t le_rfl⟩
  have zrank := finrank_zeroAt_annih (treeSpace A 5) t H.lastOutFive
  have cap := finrank_annih (treeSpace A 5)
  rw [Fintype.card_fin] at cap
  have t5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide) (coeff_separated ho (by decide))
  rw [f5] at t5
  have top := Submodule.finrank_mono b6inc
  have lower := min 5 (by decide) (by decide)
  have r6 : finrank K (primitiveBack A b 5)=4 := by omega
  have b6 := Submodule.eq_of_le_of_finrank_le b6inc (by omega)
  exact ⟨r3,r4,r5,r6,b3,b4,b5,b6⟩

/-- Every weighted genuine cubic-or-lower pure vector lies on the actual
one-dimensional reflected cubic line. No nonzero pointwise weights are assumed. -/
theorem weighted_grade_three_on_reflected_line (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (E : EqualityFrame A b) {f : Fin 15 → K}
    (hf : f ∈ zeroSpace A 3) : b*f ∈ K ∙ reflectedStageRow A b 2 := by
  have H := (equality_reverse_prefix ha ho E).1
  have gmem : reflectedStageRow A b 2 ∈ primitiveBack A b 2 :=
    adjointFlag_credit _ 1 (monomial_mem_credit 1 2 (by decide))
  have gnz := reflectedCubic_ne_zero_of_quadraticZero ha ho (by decide) E.firstSeeds.2
  have sub : K ∙ reflectedStageRow A b 2 ≤ primitiveBack A b 2 :=
    (Submodule.span_singleton_le_iff_mem ..).mpr gmem
  have line : K ∙ reflectedStageRow A b 2 = primitiveBack A b 2 := by
    apply Submodule.eq_of_le_of_finrank_le sub
    rw [H.2,finrank_span_singleton gnz]
  rw [line,H.1]
  apply mem_annih.mpr
  intro v hv
  have p : probe A b 0 (f*v)=0 :=
    probe_zeroSpace (j:=11) (k:=0) ho (by decide) (zeroSpace_mul_treeSpace ho (by decide) hf hv)
  calc
    row (b*f) v = row b (f*v) := by
      simp only [row_apply,dotProduct,Pi.mul_apply,mul_assoc]
    _ = probe A b 0 (f*v) := by simp [probe]
    _ = 0 := p

#print axioms equality_reverse_prefix
#print axioms equality_reverse_six_cap
#print axioms equality_reverse_four
#print axioms weighted_grade_three_on_reflected_line

end RKResearch.Certified.Graded.OrderTwelveFifteen
