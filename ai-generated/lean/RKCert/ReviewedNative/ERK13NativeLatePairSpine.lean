module

public import RKCert.ReviewedNative.ERK13NativeLatePhysicalFold
public import RKCert.ReviewedNative.ERK13NativeMarkedStaircase
import RKCert.ReviewedNative.MergeEqualRows
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Earn the original reverse covers from the checked marked ranks

This leaf takes the already identified physical duplicate pair. It does
not identify the complete-intersection labels, nor assume the reverse
ranks of a shortened tableau. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse HyperplaneTerminal NativeFinalThree Module RKCert.OneEscape
open scoped Classical Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {e : Fin 18 → Fin 19} {r : Fin 19 → Fin 18} {m : Fin 19}

private theorem rho_at_m (ha : ∀ i j, i ≤ j → A i j = 0)
    (tail : ∀ i, m < i → b i * reflectedClock A i = 0) :
    reflectedStageRow A b 1 m = - (b m * reflectedClock A m ^ 2) := by
  have noTail : mat A.transpose (reflectedStageWeight A b 1) m = 0 := by
    change (∑ j : Fin 19, A j m * (b j * reflectedClock A j ^ 1)) = 0
    simp only [pow_one]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ≤ m
    · rw [ha j m hj, zero_mul]
    · rw [tail j (lt_of_not_ge hj), mul_zero]
  change (((1+1:ℕ):K) * mat A.transpose (reflectedStageWeight A b 1) m -
    b m * reflectedClock A m ^ 2) = _
  rw [noTail, mul_zero, zero_sub]

private theorem delta_at_m (chart : PairClasses e r m) (ha : ∀ i j, i ≤ j → A i j = 0) :
    rowDelta A e r m m = 0 := by
  simp only [rowDelta, ha m m le_rfl, ha _ m (chart.earlier m), sub_self]

private theorem delta_ne_zero (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) :
    rowDelta A e r m ≠ 0 := by
  intro d0
  have rows (j : Fin 19) : A (e (r m)) j = A m j :=
    (sub_eq_zero.mp (congrFun d0 j)).symm
  obtain ⟨T,u,hT,hO⟩ := exists_merge_equal_rows (n:=18) ha ho
    (lt_of_le_of_ne (chart.earlier m) chart.omitted) rows
  exact (by decide : ¬(19≤18)) (ERK13NativeFirst.stage_floor19 hT hO)

private theorem row_split_apply (chart : PairClasses e r m) (u : Fin 19 → K) (j : Fin 19)
    (hf : ∀ t, foldLinear r u t = 0) :
    mat A.transpose u j = u m * rowDelta A e r m j := by
  classical
  let D := rowDelta A e r m
  have split (i : Fin 19) : A i j = A (e (r i)) j + if i=m then D j else 0 := by
    by_cases h : i=m
    · subst i
      simp only [ite_true, D, rowDelta]
      ring
    · rw [chart.kept i h, if_neg h, add_zero]
  have repZero : (∑ i : Fin 19, A (e (r i)) j * u i)=0 := by
    have fzero : folded r u = 0 := funext hf
    have pair := folded_pair r u (fun t => A (e t) j)
    rw [fzero] at pair
    simpa only [row_apply,dotProduct,Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,mul_comm]
      using pair.symm
  have onlyM : (∑ i : Fin 19, (if i=m then D j else 0)*u i)= D j*u m := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hi
      simp only [if_neg hi,zero_mul]
    · simp
  change (∑ i : Fin 19,A i j*u i)=_
  calc
    _ = ∑ i : Fin 19, (A (e (r i)) j*u i + (if i=m then D j else 0)*u i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← add_mul, ← split i]
    _ = _ := by rw [Finset.sum_add_distrib,repZero,onlyM,zero_add,mul_comm]

private theorem zero_not_pair (chart : PairClasses e r m) {u : Fin 19 → K}
    (hf : ∀ t, foldLinear r u t = 0) {i : Fin 19}
    (hi : i≠m) (ha : i≠e (r m)) : u i=0 := by
  classical
  have single (j : Fin 19) (hj : r j=r i) : j=i := by
    by_cases jm : j=m
    · subst j
      exact (ha ((chart.kept i hi).symm.trans (congrArg e hj).symm)).elim
    · calc
        j = e (r j) := (chart.kept j jm).symm
        _ = e (r i) := congrArg e hj
        _ = i := chart.kept i hi
  have hh := hf (r i)
  change (∑ j ∈ Finset.univ.filter (fun j => r j=r i),u j)=0 at hh
  rw [Finset.sum_eq_single i] at hh
  · exact hh
  · intro j hj hji
    exact (hji (single j (Finset.mem_filter.mp hj).2)).elim
  · simp

private theorem clock_of_pair (chart : PairClasses e r m)
    (cy : ∀ i, reflectedClock A (e (r i))=reflectedClock A i)
    {u : Fin 19 → K} (hf : ∀ t, foldLinear r u t = 0) :
    diag (reflectedClock A) u = reflectedClock A m • u := by
  ext i
  change reflectedClock A i*u i=reflectedClock A m*u i
  by_cases im : i=m
  · rw [im]
  by_cases ia : i=e (r m)
  · rw [ia,cy]
  simp only [zero_not_pair chart hf im ia, mul_zero]

private theorem fill_span {V W : Submodule K (Fin 19 → K)} {x : Fin 19 → K}
    (inc : V≤W) (mem : x∈W) (fresh : x∉V)
    (ranks : finrank K W=finrank K V+1) : W=V⊔K∙x := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le inc ((Submodule.span_singleton_le_iff_mem x W).mpr mem)
  · rw [Submodule.finrank_sup_span_singleton fresh,ranks]

private theorem reverse_not_clock {n j : ℕ}
    (eqn : primitiveBack A b n=annih (markedTreeSpace A b j))
    (step : markedTreeSpace A b (j+1)=markedTreeSpace A b j ⊔
      (markedTreeSpace A b j).map (diag (nodes A)))
    (rank0 : finrank K (markedTreeSpace A b j)=j+8)
    (rank1 : finrank K (markedTreeSpace A b (j+1))=j+9) :
    ¬(primitiveBack A b n).map (diag (reflectedClock A))≤primitiveBack A b n := by
  intro inv
  rw [eqn] at inv
  let V := markedTreeSpace A b j
  have co : annih V ≤ (annih V).comap (diag (reflectedClock A)) :=
    Submodule.map_le_iff_le_comap.mp inv
  have dual := annih_map_diag co
  rw [annih_annih] at dual
  have clock : V.map (diag (nodes A))≤V := by
    rintro _ ⟨w,hw,rfl⟩
    have sw := dual (Submodule.mem_map_of_mem hw)
    have eq : diag (nodes A) w = w - diag (reflectedClock A) w := by
      ext i
      simp only [diag_apply,Pi.sub_apply,Pi.one_apply,reflectedClock]
      ring
    rw [eq]
    exact V.sub_mem hw sw
  change markedTreeSpace A b (j+1)=V⊔V.map (diag (nodes A)) at step
  rw [sup_eq_left.mpr clock] at step
  rw [step,show finrank K V=j+8 from rank0] at rank1
  omega

private theorem rank_of_exact {j n : ℕ}
    (h : j+n=11) (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b=0) (rank : finrank K (markedTreeSpace A b j)=j+8) :
    primitiveBack A b n=annih (markedTreeSpace A b j) ∧
      finrank K (primitiveBack A b n)=n := by
  have nj : 11-j=n := by omega
  obtain ⟨hEq,hRank⟩ := ERK13NativeFirst.exact_marked_reverse13 ha ho
    (ERK13NativeFirst.last_original_active ha ho) seed (by omega : j≤11) rank
  exact ⟨(congrArg (primitiveBack A b) nj).symm.trans hEq,
    (congrArg (fun d : ℕ => finrank K (primitiveBack A b d)) nj).symm.trans (hRank.trans nj)⟩

/-- The rank spaces, their clock noninvariance, literal clone deletion and
the first folded row now produce the exact reverse planes upstream of
the physical adjoint theorem. -/
theorem covers_of_marked_staircase {rad : ℕ}
    {U : Submodule K (Fin 19→K)} {w : Fin 19→K}
    (chart : PairClasses e r m) (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (head : ERK13NativeFirst.NativePaidHead A b rad U w)
    (cy : ∀ i, reflectedClock A (e (r i))=reflectedClock A i)
    (live : b m≠0) (offOne : reflectedClock A m≠0)
    (tail : ∀ i, m < i → b i*reflectedClock A i=0)
    (lifts : ∀ t : Fin 18,(fun i=>coordinate (K:=K) t (r i)) ∈
      treeSpace A 10⊔K∙coordinate (Fin.last 18)) :
    rowDelta A e r m∈primitiveBack A b 2 ∧ ReverseCover A b (rowDelta A e r m) := by
  let L := primitiveBack A b
  let N := diag (reflectedClock A)
  let D := rowDelta A e r m
  let rho := reflectedStageRow A b 1
  obtain ⟨ranks,steps⟩ := ERK13NativeFirst.marked_staircase_ranks13 ha ho head seed
  have rk (j : ℕ) (lo : 6≤j) (hi : j≤10) :
      finrank K (markedTreeSpace A b j)=j+8 := ranks j lo hi
  obtain ⟨E₁,d₁⟩ := rank_of_exact (j:=10) (n:=1) (by decide) ha ho seed (rk 10 (by decide) (by decide))
  obtain ⟨E₂,d₂⟩ := rank_of_exact (j:=9) (n:=2) (by decide) ha ho seed (rk 9 (by decide) (by decide))
  obtain ⟨E₃,d₃⟩ := rank_of_exact (j:=8) (n:=3) (by decide) ha ho seed (rk 8 (by decide) (by decide))
  obtain ⟨E₄,d₄⟩ := rank_of_exact (j:=7) (n:=4) (by decide) ha ho seed (rk 7 (by decide) (by decide))
  have unstable₂ : ¬ (L 2).map N ≤ L 2 :=
    reverse_not_clock E₂ (steps 9 (by decide) (by decide)) (rk 9 (by decide) (by decide))
      (rk 10 (by decide) (by decide))
  have unstable₃ : ¬ (L 3).map N ≤ L 3 :=
    reverse_not_clock E₃ (steps 8 (by decide) (by decide)) (rk 8 (by decide) (by decide))
      (rk 9 (by decide) (by decide))
  have Rm : rho m≠0 := by
    change reflectedStageRow A b 1 m≠0
    rw [rho_at_m ha tail]
    exact neg_ne_zero.mpr (mul_ne_zero live (pow_ne_zero _ offOne))
  have Rne : rho≠0 := fun h => Rm (congrFun h m)
  have Rmem : rho∈L 1 :=
    adjointFlag_credit _ 0 (monomial_mem_credit 0 1 le_rfl)
  have LR : L 1=K∙rho := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem rho (L 1)).mpr Rmem
    · rw [finrank_span_singleton Rne]
      exact d₁.le
  have RFold : ∀ t, foldLinear r rho t=0 := fold_first_paid ha ho seed lifts
  have Rclock : N rho=reflectedClock A m • rho := clock_of_pair chart cy RFold
  have Dmem : D∈L 2 := by
    have paid : mat A.transpose rho∈L 2 :=
      adjointFlag_transpose _ 1 (Submodule.mem_map_of_mem Rmem)
    have eqA : mat A.transpose rho=rho m • D :=
      funext (fun j => row_split_apply chart rho j RFold)
    have q := (L 2).smul_mem (rho m)⁻¹ paid
    rw [eqA,smul_smul,inv_mul_cancel₀ Rm,one_smul] at q
    exact q
  have Dfresh : D∉L 1 := by
    rw [LR]
    intro d
    obtain ⟨k,keq⟩ := Submodule.mem_span_singleton.mp d
    have mulZ : k*rho m=0 := by
      have hm := congrFun keq m
      change k*rho m=D m at hm
      exact hm.trans (delta_at_m chart ha)
    have kz := (mul_eq_zero.mp mulZ).resolve_right Rm
    exact delta_ne_zero chart ha ho (by simpa only [kz,zero_smul] using keq.symm)
  have L2 : L 2=(K∙rho)⊔K∙D := by
    have e := fill_span (adjointFlag_le_succ _ 1) Dmem Dfresh (by rw [d₂,d₁])
    change L 2 = L 1 ⊔ K ∙ D at e
    rwa [LR] at e
  have D1m : N D∈L 3 :=
    adjointFlag_clock _ 2 (Submodule.mem_map_of_mem Dmem)
  have D1f : N D∉L 2 := by
    intro h
    apply unstable₂
    rintro _ ⟨u,hu,rfl⟩
    rw [L2] at hu
    obtain ⟨v,hv,z,hz,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨g,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add,map_smul,map_smul,Rclock]
    exact (L 2).add_mem ((L 2).smul_mem _ ((L 2).smul_mem _ (adjointFlag_le_succ _ 1 Rmem)))
      ((L 2).smul_mem _ h)
  have L3 : L 3=L 2⊔K∙(N D) :=
    fill_span (adjointFlag_le_succ _ 2) D1m D1f (by rw [d₃,d₂])
  have D2m : N (N D)∈L 4 :=
    adjointFlag_clock _ 3 (Submodule.mem_map_of_mem D1m)
  have D2f : N (N D)∉L 3 := by
    intro h
    apply unstable₃
    rintro _ ⟨u,hu,rfl⟩
    rw [L3,L2] at hu
    obtain ⟨v,hv,z,hz,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨v₀,hv₀,v₁,hv₁,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv₀
    obtain ⟨g,rfl⟩ := Submodule.mem_span_singleton.mp hv₁
    obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add,map_add,map_smul,map_smul,map_smul,Rclock]
    have rm : rho∈L 3 := adjointFlag_le_succ _ 2 (adjointFlag_le_succ _ 1 Rmem)
    exact (L 3).add_mem
      ((L 3).add_mem ((L 3).smul_mem _ ((L 3).smul_mem _ rm)) ((L 3).smul_mem _ D1m))
      ((L 3).smul_mem _ h)
  have L4 : L 4=L 3⊔K∙(N (N D)) :=
    fill_span (adjointFlag_le_succ _ 3) D2m D2f (by rw [d₄,d₃])
  refine ⟨Dmem,⟨?_,?_,?_⟩⟩
  · intro v hv
    change v∈L 2 at hv
    rw [L2] at hv
    obtain ⟨a,ha',z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨h,rfl⟩ := Submodule.mem_span_singleton.mp ha'
    obtain ⟨p,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨h,p,fun i => by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring⟩
  · intro v hv
    change v∈L 3 at hv
    rw [L3,L2] at hv
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,ha',c,hc,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨h,rfl⟩ := Submodule.mem_span_singleton.mp ha'
    obtain ⟨p,rfl⟩ := Submodule.mem_span_singleton.mp hc
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨h,p,q,fun i => by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,N,diag_apply]; ring⟩
  · intro v hv
    change v∈L 4 at hv
    rw [L4,L3,L2] at hv
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨v',hv',d,hd,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,ha',c,hc,rfl⟩ := Submodule.mem_sup.mp hv'
    obtain ⟨h,rfl⟩ := Submodule.mem_span_singleton.mp ha'
    obtain ⟨p,rfl⟩ := Submodule.mem_span_singleton.mp hc
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hd
    obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨h,p,q,s,fun i => by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,N,diag_apply]; ring⟩

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
