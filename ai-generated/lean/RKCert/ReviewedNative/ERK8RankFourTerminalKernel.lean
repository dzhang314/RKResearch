module

public import RKCert.ReviewedNative.ERKUniform
public import RKCert.ReviewedNative.GradedProducts
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Terminal coordinate rigidity at the rank-four midpoint of a
strict eleven-stage order-eight tableau. All coordinate statements
refer to physical rows, not merged clock tags. -/
namespace RKResearch.Certified.Graded.Reverse

open Module
open scoped Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

theorem width11_rank_four_reverse_saturation
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (zeroSpace A 4) = 4) :
    firstSeed A b=0 ∧ back A b 2 = annih (treeSpace A 4) := by
  have rr : finrank K (treeSpace A 4)=9 := by
    rw [erk_midpoint_tree_rank ha ho (q:=4) (by decide) (by decide),rank]
  have upper := backward_count ha ho 4 2 (by decide)
  have hfirst : firstSeed A b=0 := by
    by_contra hz
    rw [rr,first_dim_one hz] at upper
    omega
  refine ⟨hfirst,?_⟩
  have inc := back_annih ho 4 2 (by decide)
  have count := finrank_annih (treeSpace A 4)
  rw [rr,Fintype.card_fin] at count
  have lower := back_finrank ha ho 2 (by decide)
  exact Submodule.eq_of_le_of_finrank_le inc (by omega)

/-- The rank-four window also forces the exact next tree rank, and
its annihilator is the single literal second reverse seed. -/
theorem width11_rank_four_next_profile
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (zeroSpace A 4) = 4) :
    finrank K (treeSpace A 5)=10 ∧ annih (treeSpace A 5)=K ∙ quadraticSeed A b := by
  obtain ⟨first,rev⟩ := width11_rank_four_reverse_saturation ha ho rank
  have r4 : finrank K (treeSpace A 4)=9 := by
    rw [erk_midpoint_tree_rank ha ho (q:=4) (by decide) (by decide),rank]
  have rdual := finrank_annih (treeSpace A 4)
  rw [r4,Fintype.card_fin] at rdual
  have growth : treeSpace A 4 < treeSpace A 5 := by
    refine lt_of_le_of_ne (treeSpace_mono A (by decide)) ?_
    intro heq
    have incA : (annih (treeSpace A 4)).map (mat A.transpose) ≤ annih (treeSpace A 4) := by
      apply annih_map_transpose
      intro v hv
      have h : mat A v∈treeSpace A 5 := mat_treeSpace A 4 hv
      change mat A v ∈ treeSpace A 4
      rw [heq]
      exact h
    have incC : (annih (treeSpace A 4)).map (diag (reflectedClock A)) ≤ annih (treeSpace A 4) := by
      apply annih_map_diag
      intro v hv
      have h : diag (reflectedClock A) v∈treeSpace A 5 := reflectedClock_treeSpace A 4 hv
      change diag (reflectedClock A) v ∈ treeSpace A 4
      rw [heq]
      exact h
    have inc3 : back A b 3 ≤ annih (treeSpace A 4) := by
      change back A b 2 ⊔ (back A b 2).map (mat A.transpose) ⊔
        (back A b 2).map (diag (reflectedClock A)) ⊔ pairCredit A b 0 ≤ _
      rw [rev]
      exact sup_le (sup_le (sup_le le_rfl incA) incC) (paid_pairCredit ho 4 0 (by decide))
    have h := Submodule.finrank_mono inc3
    have e := back_finrank ha ho 3 (by decide)
    omega
  have low := Submodule.finrank_lt_finrank_of_lt growth
  have cap := backward_count ha ho 5 1 (by decide)
  have r5 : finrank K (treeSpace A 5)=10 := by omega
  refine ⟨r5,?_⟩
  have one : back A b 1 = K ∙ quadraticSeed A b := by
    change (K ∙ firstSeed A b) ⊔ (K ∙ firstSeed A b).map (mat A.transpose) ⊔
      (K ∙ firstSeed A b).map (diag (reflectedClock A)) ⊔
      (K ∙ quadraticSeed A b) = K ∙ quadraticSeed A b
    simp [first]
  rw [←one]
  symm
  have rd := finrank_annih (treeSpace A 5)
  rw [r5,Fintype.card_fin] at rd
  have low₁ := back_finrank ha ho 1 (by decide)
  exact Submodule.eq_of_le_of_finrank_le (back_annih ho 5 1 (by decide)) (by omega)

theorem width11_rank_four_terminal_coordinate
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (zeroSpace A 4) = 4) (live : b (Fin.last 10) ≠ 0) :
    coordinate (K:=K) (Fin.last 10) ∈ treeSpace A 4 ∧ nodes A (Fin.last 10)=1 := by
  obtain ⟨first,rev⟩ := width11_rank_four_reverse_saturation ha ho rank
  have L : LastActive b (Fin.last 10) :=
    ⟨live, fun i h => (not_lt_of_ge (Fin.le_last i) h).elim⟩
  refine ⟨?_, L.node_eq_one ha first⟩
  rw [←annih_annih (treeSpace A 4)]
  apply mem_annih.mpr
  intro w hw
  rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
  rw [←rev] at hw
  exact mem_tailZero.mp (L.back_tail ha first 2 hw) _ le_rfl

/-- The mixed rooted-product budget makes an actual output-weighted
defect vector a genuine row annihilator. -/
theorem weighted_defect_in_annihilator {m n : Nat} (ho : HasOrder 8 A b)
    (pay : m+n+1≤8) {u : Fin 11 → K} (hu : u∈zeroSpace A m) :
    diag u b ∈ annih (treeSpace A n) := by
  apply mem_annih.mpr
  intro v hv
  rw [row_diag]
  have z : diag u v∈zeroSpace A (m+n) := zeroSpace_mul_treeSpace ho (by omega) hu hv
  have h := probe_zeroSpace (k:=0) ho (by omega) z
  change probe A b 0 (diag u v)=0 at h
  simpa only [probe,pow_zero,mul_one] using h

/-- The physical terminal stage is exact through size four, even if its
profile has a nonzero size-five defect. -/
theorem width11_rank_four_terminal_pure_four
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (rank : finrank K (zeroSpace A 4) = 4) (live : b (Fin.last 10) ≠ 0)
    {u : Fin 11 → K} (hu : u∈zeroSpace A 3) : u (Fin.last 10)=0 := by
  have ht := (width11_rank_four_terminal_coordinate ha ho rank live).1
  have h := mem_annih.mp (weighted_defect_in_annihilator (m:=3) (n:=4) ho (by decide) hu) _ ht
  rw [row_coordinate,diag_apply] at h
  exact (mul_eq_zero.mp h).resolve_right live

/-- Order-eight midpoint projection test through the four weighted
clock powers, with the explicit origin removing the constant part. -/
theorem width11_midpoint_zero_of_four_probes (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) {w : Fin 11 → K} (hw : w∈treeSpace A 4)
    (hzero : w 0=0) (hprobe : ∀ k < 4, probe A b k w=0) : w∈zeroSpace A 4 := by
  rw [treeSpace_coeff_sup ho (by decide)] at hw
  obtain ⟨_,⟨a,rfl⟩,v,hv,heq⟩ := Submodule.mem_sup.mp hw
  have a0 : a 0=0 := by
    have e := congrFun heq 0
    have hv0 : v 0=0 := origin_zeroSpace ha 4 hv
    rw [Pi.add_apply,coeffEval_origin ha, hv0, add_zero, hzero] at e
    exact e
  have moment (i : Fin 4) :
      (∑ j : Fin 4, a j.succ / ((i.val+j.val+2 : Nat) : K)) = 0 := by
    have e := hprobe i.val i.isLt
    rw [←heq,map_add,probe_zeroSpace ho (by omega) hv,add_zero,probe_coeffEval ho (by omega),
      Fin.sum_univ_succ,a0,zero_div,zero_add] at e
    simpa only [Fin.val_succ,Nat.add_assoc] using e
  have az := moments_detect ho (d:=2) (by decide) (by decide)
    (fun i j => by have := i.isLt; have := j.isLt; omega)
    (fun j : Fin 4=>a j.succ) moment
  have z : a=0 := by
    ext j
    exact Fin.cases a0 az j
  rw [←heq,z,map_zero,zero_add]
  exact hv

/-- Reproducing polynomial for the paid terminal coordinate. -/
def terminalEightKernel (x : ℚ) : ℚ := 20*x*(2*x-1)*(7*x^2-7*x+1)

private def terminalEightCoeffs : Fin 5 → ℚ := ![0,-20,180,-420,280]

private theorem terminalEightCoeffs_paid : ∀ i : Fin 4,
    (∑ j : Fin 5, terminalEightCoeffs j / ((i.val+j.val+1:Nat) : ℚ)) = 1 := by
  decide +kernel

private theorem terminalEightCoeffs_eval (T : Matrix (Fin 11) (Fin 11) ℚ) :
    coeffEval T 4 terminalEightCoeffs=fun i => terminalEightKernel (nodes T i) := by
  ext i
  simp only [coeffEval_apply,normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp [Fin.sum_univ_succ,terminalEightCoeffs,terminalEightKernel]
  ring

theorem width11_rank_four_terminal_polynomial {T : Matrix (Fin 11) (Fin 11) ℚ}
    {w : Fin 11 → ℚ} (ha : ∀ i j, i ≤ j → T i j = 0) (ho : HasOrder 8 T w)
    (rank : finrank ℚ (zeroSpace T 4)=4) (live : w (Fin.last 10)≠0) :
    (coordinate (K:=ℚ) (Fin.last 10) - w (Fin.last 10) •
      (fun i => terminalEightKernel (nodes T i))) ∈ zeroSpace T 4 := by
  obtain ⟨ht,hc⟩ := width11_rank_four_terminal_coordinate ha ho rank live
  rw [←terminalEightCoeffs_eval]
  apply width11_midpoint_zero_of_four_probes ha ho
  · exact (treeSpace T 4).sub_mem ht
      ((treeSpace T 4).smul_mem _ (coeffEval_mem_treeSpace _ _ _))
  · rw [Pi.sub_apply,Pi.smul_apply,coeffEval_origin ha]
    norm_num [coordinate,terminalEightCoeffs,Fin.ext_iff]
  · intro k hk
    rw [map_sub,map_smul,probe_coeffEval ho (by omega)]
    have hp := terminalEightCoeffs_paid ⟨k,hk⟩
    change (∑ j : Fin 5, terminalEightCoeffs j / ((k+j.val+1:Nat) : ℚ))=1 at hp
    rw [hp]
    change row (fun i => w i*(nodes T i)^k) (coordinate (Fin.last 10)) -
      w (Fin.last 10)*1=0
    rw [row_coordinate,hc,one_pow,mul_one,sub_self]

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem terminal_kernel_quadratic_nz (x : ℚ) : 7*x^2-7*x+1≠0 := by
  intro h
  have hn : (x.den : ℚ)≠0 := by exact_mod_cast x.den_nz
  have he : 7*x.num^2-7*x.num*(x.den:Int)+(x.den:Int)^2=0 := by
    apply Int.cast_injective (α:=ℚ)
    push_cast
    rw [←x.num_div_den] at h
    field_simp [hn] at h
    linear_combination h
  have z := congrArg (fun y : Int => (y:ZMod 7)) he
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast,Int.cast_zero] at z
  have hz7 : (7:ZMod 7)=0 := by decide
  simp only [hz7,zero_mul,sub_self,zero_add] at z
  have d₀ : (x.den:ZMod 7)=0 := by by_contra h; exact pow_ne_zero _ h z
  obtain ⟨d,hd⟩ := (ZMod.natCast_eq_zero_iff _ _).mp d₀
  rw [hd,Nat.cast_mul,Nat.cast_ofNat] at he
  have hz : (7:Int)*(x.num^2-7*x.num*(d:Int)+7*(d:Int)^2)=0 := by linear_combination he
  have hm := (mul_eq_zero.mp hz).resolve_left (by decide)
  have hmod := congrArg (fun y : Int => (y:ZMod 7)) hm
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_pow,Int.cast_ofNat,
    Int.cast_natCast,Int.cast_zero,hz7,zero_mul,sub_zero,add_zero] at hmod
  have num0 : (x.num:ZMod 7)=0 := by by_contra hm'; exact pow_ne_zero _ hm' hmod
  have div : 7 ∣ x.num.natAbs :=
    Int.natCast_dvd_natCast.mp
      ((Int.dvd_natAbs).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp num0))
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 7) div ⟨d,hd⟩ x.reduced

/-- Every nonterminal rational row exact through size five is at one of
two clocks, even if the other physical defect rows are dispersed. -/
theorem width11_rank_four_pure_node_zero_or_half {T : Matrix (Fin 11) (Fin 11) ℚ}
    {w : Fin 11 → ℚ} (ha : ∀ i j, i ≤ j → T i j = 0) (ho : HasOrder 8 T w)
    (rank : finrank ℚ (zeroSpace T 4)=4) (live : w (Fin.last 10)≠0)
    (i : Fin 11) (hi : i≠Fin.last 10)
    (pure : ∀ u ∈ zeroSpace T 4,u i=0) : nodes T i=0 ∨ nodes T i=1/2 := by
  have e := pure _ (width11_rank_four_terminal_polynomial ha ho rank live)
  have ht : coordinate (K:=ℚ) (Fin.last 10) i=0 := by
    have hi' : i ≠ (10 : Fin 11) := hi
    simp [coordinate,hi']
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ht,zero_sub,neg_eq_zero] at e
  have hk := (mul_eq_zero.mp e).resolve_left live
  unfold terminalEightKernel at hk
  have hL := (mul_eq_zero.mp hk).resolve_right (terminal_kernel_quadratic_nz _)
  rcases mul_eq_zero.mp hL with h₀|h₁
  · exact Or.inl ((mul_eq_zero.mp h₀).resolve_left (by decide))
  · right
    linear_combination (1/2:ℚ)*h₁

/-- If the terminal is itself pure through size five, its output weight
is the exact endpoint reproducing coefficient. -/
theorem width11_rank_four_pure_terminal_weight {T : Matrix (Fin 11) (Fin 11) ℚ}
    {w : Fin 11 → ℚ} (ha : ∀ i j, i ≤ j → T i j = 0) (ho : HasOrder 8 T w)
    (rank : finrank ℚ (zeroSpace T 4)=4) (live : w (Fin.last 10)≠0)
    (pure : ∀ u ∈ zeroSpace T 4,u (Fin.last 10)=0) : w (Fin.last 10)=1/20 := by
  have e := pure _ (width11_rank_four_terminal_polynomial ha ho rank live)
  have hc := (width11_rank_four_terminal_coordinate ha ho rank live).2
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,coordinate,Pi.single_eq_same,hc,
    terminalEightKernel] at e
  norm_num at e
  change w (10 : Fin 11) = 1/20
  linear_combination (-1/20:ℚ)*e

end RKResearch.Certified.Graded.Reverse

#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_terminal_coordinate
#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_terminal_pure_four
#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_terminal_polynomial
#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_next_profile
#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_pure_node_zero_or_half
#print axioms RKResearch.Certified.Graded.Reverse.width11_rank_four_pure_terminal_weight
