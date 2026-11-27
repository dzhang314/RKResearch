module

public import RKCert.ReviewedNative.ERK8CharElevenFiveLatePlacement

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two literal five-off reflected equations, after balancing the
A-image of the early hull against the actual E5 cofactor annihilator. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven Reverse
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

noncomputable def fiveTailVector (A : Matrix (Fin 10) (Fin 10) K) : Fin 10→K :=
  fun i=>if i∈bulkRows then (earlyFourHull A).eval (nodes A i) else 0

theorem fiveTailVector_bulk (A : Matrix (Fin 10) (Fin 10) K) {i : Fin 10}
    (hi : i∈bulkRows) : fiveTailVector A i=(earlyFourHull A).eval (nodes A i) := by
  simp [fiveTailVector,hi]

theorem fiveTailVector_mem
    (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x : Fin 10} (T : FiveCleanTail A x 8) (g5 : g A 5≠0) :
    fiveTailVector A∈treeSpace A 4 := by
  let N := earlyFourHull A
  have Nd : N.natDegree=4 := (natDegree_nodalHull _).trans (early_n4_from_off_row_five five cleanFive S g5).2
  let coeffs (j : Fin 5) := N.coeff j.val
  have exactP : ofFn 5 coeffs=N := by
    ext j
    by_cases k : j < 5
    · rw [ofFn_coeff_eq_val_of_lt coeffs k]
    · rw [ofFn_coeff_eq_zero_of_ge coeffs (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]
  let w : (Fin 5→K)×(Fin 3→K) := (coeffs,0)
  have vec : fiveTailVector A=bulkProfile A 4 w := by
    ext i
    by_cases hi : i∈bulkRows
    · rw [fiveTailVector_bulk A hi,bulkProfile_bulk A 4 w hi]
      change N.eval (nodes A i)=(ofFn 5 coeffs).eval (nodes A i)
      rw [exactP]
    · have a : i∈anchorRows := by simpa [bulkRows] using hi
      simp only [anchorRows,Finset.mem_insert,Finset.mem_singleton] at a
      rcases a with rfl|rfl|rfl <;> simp [fiveTailVector,hi,bulkProfile,w]
  rw [vec]
  exact bulkProfile_mem ho p H S T (by decide) w

theorem fiveTailVector_zero_before (A : Matrix (Fin 10) (Fin 10) K) {i : Fin 10}
    (hi : i < 6) : fiveTailVector A i=0 := by
  by_cases m : i∈bulkRows
  · rw [fiveTailVector_bulk A m]
    apply nodalHull_eval_of_mem
    obtain ⟨n0,n4,n9⟩ := mem_bulkRows.mp m
    have z0 : i.val≠0 := fun h=>n0 (Fin.ext h)
    have z4 : i.val≠4 := fun h=>n4 (Fin.ext h)
    change i.val < 6 at hi
    have h : i.val=1∨i.val=2∨i.val=3∨i.val=5 := by omega
    rcases h with h|h|h|h
    · rw [show i=1 from Fin.ext h]
      simp [earlyFourClocks,earlyThreeClocks]
    · rw [show i=2 from Fin.ext h]
      simp [earlyFourClocks,earlyThreeClocks]
    · rw [show i=3 from Fin.ext h]
      simp [earlyFourClocks,earlyThreeClocks]
    · rw [show i=5 from Fin.ext h]
      simp [earlyFourClocks]
  · simp [fiveTailVector,m]

private theorem at_most_six {i : Fin 10} (i7 : i≠7) (i8 : i≠8) (i9 : i≠9) :
    i≤6 := by
  have n7 : i.val≠7 := fun h=>i7 (Fin.ext h)
  have n8 : i.val≠8 := fun h=>i8 (Fin.ext h)
  have n9 : i.val≠9 := fun h=>i9 (Fin.ext h)
  have bound := i.isLt
  change i.val≤6
  omega

/-- The two paid reflected equations use the same actual cofactor
scale of the two late A-images. The weights are not assumed given. -/
theorem five_tail_reflection_rows
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x : Fin 10} (T : FiveCleanTail A x 8) (g5 : g A 5≠0) :
    ∃ sigma : K, ∀ k : ℕ, 1≤k → k≤2 →
      ((k+1:ℕ):K)*sigma*(b 7*(1-nodes A 7)^k*bulkCofactor A (nodes A 7)-
        b 8*(nodes A x)^k*bulkCofactor A (nodes A 8)) =
      b 8*((nodes A 8)^(k+1)*(earlyFourHull A).eval (nodes A x)+
        (nodes A x)^(k+1)*(earlyFourHull A).eval (nodes A 8)) := by
  let V := fiveTailVector A
  let W := mat A V
  let N := earlyFourHull A
  let C7 := bulkCofactor A (nodes A 7)
  let C8 := bulkCofactor A (nodes A 8)
  let y (i : Fin 10) := 1-nodes A i
  let sigma := W 7/C7
  have tV : V∈treeSpace A 4 := fiveTailVector_mem ho p five cleanFive H S T g5
  have tW : W∈treeSpace A 5 := mat_treeSpace A 4 tV
  have W0 (i : Fin 10) (hi : i≤6) : W i=0 :=
    causal_mat ha i V (fun j hj=>fiveTailVector_zero_before A (hj.trans_le hi))
  have balance := mem_annih.mp (bulkReverse_mem_annih_five ha ho p five cleanFive H S T) _ tW
  rw [row_apply,dotProduct,
    sum_pair_of_support (by decide : (7:Fin 10)≠8) _ (fun j j7 j8 => by
      by_cases jj : j∈bulkRows
      · rw [W0 j (at_most_six j7 j8 (mem_bulkRows.mp jj).2.2),mul_zero]
      · simp [bulkReverse,jj])] at balance
  rw [bulkReverse_apply A (show (7:Fin 10)∈bulkRows by decide),
    bulkReverse_apply A (show (8:Fin 10)∈bulkRows by decide)] at balance
  change C7⁻¹*W 7+C8⁻¹*W 8=0 at balance
  have n7 : C7≠0 := bulkCofactor_ne A _
  have n8 : C8≠0 := bulkCofactor_ne A _
  have W7 : W 7=sigma*C7 := (div_mul_cancel₀ _ n7).symm
  have W8 : W 8= -sigma*C8 := by
    have eq : W 8/C8=-sigma := by simp only [sigma,div_eq_mul_inv]; linear_combination balance
    exact (div_eq_iff n8).mp eq
  have yx : y x=nodes A 8 := by dsimp only [y]; linear_combination -T.sum_one
  have y8 : y 8=nodes A x := by dsimp only [y]; linear_combination -T.sum_one
  have bEq := (clean_quadratic_weights_equal_nonzero ha ho p five H S T).1
  have left (k : ℕ) (kpos : 0<k) :
      (∑ i,b i*y i^k*W i)=b 7*y 7^k*(sigma*C7)+b 8*y 8^k*(-sigma*C8) := by
    rw [sum_pair_of_support (by decide : (7:Fin 10)≠8) _ (fun j j7 j8 => by
      by_cases j9 : j=9
      · rw [j9]
        change b 9*(1-nodes A 9)^k*W 9=0
        rw [show nodes A 9=1 from H.terminal_clock]
        simp [zero_pow (Nat.ne_of_gt kpos)]
      · rw [W0 j (at_most_six j7 j8 j9),mul_zero]),W7,W8]
  have right (k : ℕ) :
      (∑ i,b i*y i^k*V i) =
        b 8*((nodes A 8)^k*N.eval (nodes A x)+(nodes A x)^k*N.eval (nodes A 8)) := by
    rw [sum_pair_of_support (ne_of_lt T.xz) _ (fun j jx j8=>by
      by_cases gj : g A j=0
      · rcases (T.clean_iff j).mp gj with h|h|h
        · have nbulk : j∉bulkRows := fun e=>(Finset.mem_sdiff.mp e).2 h
          simp [V,fiveTailVector,nbulk]
        · exact (jx h).elim
        · exact (j8 h).elim
      · rw [five_off_weights_are_zero ha ho five H j gj,zero_mul,zero_mul])]
    rw [show V x=N.eval (nodes A x) from fiveTailVector_bulk A (lateRows_bulk T.x_late),
        show V 8=N.eval (nodes A 8) from fiveTailVector_bulk A (by decide),yx,y8,bEq]
    ring
  refine ⟨sigma,?_⟩
  intro k kp k2
  have e : row (reflectedStageRow A b k) V=0 :=
    reflectedStageRow_treeSpace ho 4 k (by omega) tV
  rw [reflectedStageRow_pair,sub_eq_zero] at e
  simp only [reflectedProbe,row_apply,dotProduct,pow_zero,mul_one,reflectedClock,
    Pi.sub_apply,Pi.one_apply] at e
  change ((k+1:ℕ):K)*(∑ j,b j*y j^k*W j)=∑ j,b j*y j^(k+1)*V j at e
  rw [left k (by omega),right (k+1),y8] at e
  change ((k+1:ℕ):K)*sigma*(b 7*y 7^k*C7-b 8*(nodes A x)^k*C8)=
    b 8*((nodes A 8)^(k+1)*N.eval (nodes A x)+(nodes A x)^(k+1)*N.eval (nodes A 8))
  linear_combination e

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_tail_reflection_rows
