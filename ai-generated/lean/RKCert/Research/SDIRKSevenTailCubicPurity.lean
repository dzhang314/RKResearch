module

public import RKCert.Research.SDIRKSevenTailCollisionIngress

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Six-stage paid-tail cubic purity at reviewed order seven

The actual second adjoint has a nonzero degree-four moment error forced
by the nonzero common diagonal and last weight. Its two consecutive
tests eliminate the entire cubic defect on the six active clocks. The
Hilbert normal form needs characteristic zero but no order or positivity
on the coefficient field. -/

namespace RKResearch.Certified.SDIRKSevenTailCubicPurity
open RKResearch Graded SDIRKSevenTailCollision
open scoped Matrix BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The first three physical coordinate columns are already paid by grade four. -/
def PaidHead (A : Matrix F F K) : Prop :=
  ∀ i, i ∉ tail → Pi.single i (1:K) ∈ zeroSpace A 4

private theorem head_rows {A : Matrix F F K} {b : F → K}
    (ho : HasOrder 7 A b) (head : PaidHead A) {i : F} (hi : i ∉ tail) :
      b i = 0 ∧ firstRow A b i = 0 ∧ secondRow A b i = 0 := by
  have e := head i hi
  have ae := mat_zeroSpace_charZero A 4 e
  have b0 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) e)
  have a0 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) ae)
  have a1 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 1) (by decide) ae)
  simp only [row_apply,pow_zero,mul_one] at b0 a0
  simp only [row_apply,pow_one] at a1
  change (b ⬝ᵥ (A *ᵥ Pi.single i 1)) = 0 at a0
  change ((b*x A) ⬝ᵥ (A *ᵥ Pi.single i 1)) = 0 at a1
  rw [Matrix.dotProduct_mulVec] at a0 a1
  refine ⟨?_,?_,?_⟩
  · simpa [dotProduct,Pi.single_apply] using b0
  · simpa [dotProduct,Pi.single_apply] using a0
  · simpa [dotProduct,Pi.single_apply] using a1

private theorem first_head {A : Matrix F F K} {b : F → K}
    (ho : HasOrder 7 A b) (head : PaidHead A) (i : F) (h : i ∉ tail) :
    firstError A b i=0 := by
  obtain ⟨h₀,h₁,_⟩ := head_rows ho head h
  change firstRow A b i-b i*(1-x A i)=0
  rw [h₀,h₁,zero_mul,sub_zero]

private theorem second_head {A : Matrix F F K} {b : F → K}
    (ho : HasOrder 7 A b) (head : PaidHead A) (i : F) (h : i ∉ tail) :
    secondError A b i=0 := by
  obtain ⟨h₀,_,h₁⟩ := head_rows ho head h
  change secondRow A b i-b i*((1-(x A i)^2)/2)=0
  rw [h₀,h₁,zero_mul,sub_zero]

omit [CharZero K] in
private theorem supported_moments_zero {c w : F → K} (S : Finset F)
    (injective : ∀ i j, i ∈ S → j ∈ S → c i=c j → i=j)
    (supp : ∀ i, i∉S → w i=0) {n : ℕ} (size : S.card ≤ n+1)
    (moment : ∀ j≤n, (∑ i,w i*(c i)^j)=0) (a : F) (ha : a∈S) :
    w a = 0 := by
  let sites := S.image c
  have sz : sites.card ≤ n+1 := Finset.card_image_le.trans size
  have covers (i : F) (hi : w i≠0) : c i ∈ sites := by
    have m : i∈S := by by_contra z; exact hi (supp i z)
    exact Finset.mem_image.mpr ⟨i,m,rfl⟩
  have h := fiber_zero moment sites sz covers (c a)
  have e : (∑ i ∈ ({a}:Finset F),w i) =
      (∑ i ∈ Finset.univ.filter (fun i => c i=c a),w i) := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      have eq := Finset.mem_singleton.mp hi
      simp [eq]
    · intro i hi hi'
      by_cases hs : i ∈ S
      · have eq : c i=c a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
        exact (hi' (Finset.mem_singleton.mpr (injective _ _ hs ha eq))).elim
      · exact supp i hs
  simpa only [Finset.sum_singleton] using e.trans h

theorem first_adjoint {A : Matrix F F K} {b : F → K}
    (ho : HasOrder 7 A b) (head : PaidHead A)
    (inj : ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j) :
    firstRow A b=firstTarget A b := by
  funext i
  apply sub_eq_zero.mp
  change firstError A b i=0
  by_cases ht : i∈tail
  · exact supported_moments_zero (n:=5) tail inj (first_head ho head)
      (by decide +kernel) (firstError_moments ho) i ht
  · exact first_head ho head i ht

omit [CharZero K] in
private theorem column_last {A : Matrix F F K} {γ : K} (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (t : F → K) : (t ᵥ* A) 8=t 8*γ := by
  change (∑ i,t i*A i 8)=_
  rw [Finset.sum_eq_single (8:F),he]
  · intro i hi hne
    have non : i.val ≠ 8 := fun h => hne (Fin.ext h)
    have iLt := i.isLt
    have i8 : i < (8 : F) := by change i.val < 8; omega
    have vz : A i 8 = 0 := ha i8
    rw [vz,mul_zero]
  · simp

theorem second_error_last {A : Matrix F F K} {b : F → K} {γ : K}
    (ho : HasOrder 7 A b) (head : PaidHead A) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hg : γ≠0) (hb : b 8≠0)
    (inj : ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j) :
    secondError A b 8≠0 := by
  have c₀ := congrFun (first_adjoint ho head inj) 8
  change (b ᵥ* A) 8=b 8*(1-x A 8) at c₀
  rw [column_last ha he] at c₀
  have c₁ := mul_left_cancel₀ hb c₀
  intro h
  change ((b*x A) ᵥ* A) 8-b 8*((1-(x A 8)^2)/2)=0 at h
  rw [column_last ha he] at h
  change b 8*x A 8*γ-b 8*((1-(x A 8)^2)/2)=0 at h
  have E : x A 8*γ=(1-(x A 8)^2)/2 := by
    apply mul_left_cancel₀ hb
    linear_combination h
  have G : γ^2=0 := by linear_combination -2*E+(γ+1+x A 8)*c₁
  exact pow_ne_zero 2 hg G

theorem second_error_every_tail {A : Matrix F F K} {b : F → K} {γ : K}
    (ho : HasOrder 7 A b) (head : PaidHead A) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hg : γ≠0) (hb : b 8≠0)
    (inj : ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j)
    (j : F) (hj : j∈tail) : secondError A b j≠0 := by
  have last := second_error_last ho head ha he hg hb inj
  intro h
  have sub : tail.erase j ⊆ tail := Finset.erase_subset _ _
  have size : (tail.erase j).card ≤ 5 := by
    rw [Finset.card_erase_of_mem hj,show tail.card=6 by decide +kernel]
  have s (i : F) (hi : i∉tail.erase j) : secondError A b i=0 := by
    by_cases it : i∈tail
    · have eq : i=j := by
        by_contra e
        exact hi (Finset.mem_erase.mpr ⟨e,it⟩)
      simpa only [eq] using h
    · exact second_head ho head i it
  have e8 : (8:F)∈tail.erase j := by
    refine Finset.mem_erase.mpr ⟨?_,by decide⟩
    intro e
    exact last (e.symm ▸ h)
  exact last (supported_moments_zero (n:=4) (tail.erase j)
    (fun i k hi hk x => inj i k (sub hi) (sub hk) x) s size (secondError_moments ho) 8 e8)

omit [CharZero K] in
private theorem defect_moment {A : Matrix F F K} {b v : F → K}
    (ho : HasOrder 7 A b) (hv : v∈zeroSpace A 3) (j : ℕ) (hj : j≤3) :
    (∑ i,b i*(x A i)^j*v i)=0 := by
  have e := LinearMap.mem_ker.mp (probe_zeroSpace ho (k:=j) (by omega) hv)
  exact e

private theorem error_reads {A : Matrix F F K} {b v : F → K}
    (ho : HasOrder 7 A b) (hv : v∈zeroSpace A 3) (j : ℕ) (hj : j≤1) :
    (∑ i,secondError A b i*(x A i)^j*v i)=0 := by
  let p : F → K := fun i => (x A i)^j*v i
  have pure : p∈zeroSpace A 4 := by
    have e : j=0 ∨ j=1 := by omega
    rcases e with rfl | rfl
    · simpa only [p,pow_zero,one_mul] using zeroSpace_mono A (by decide : 3≤4) hv
    · have eq : p=diag (x A) v := by funext i; simp only [p,pow_one,diag_apply]
      rw [eq]
      exact diag_zeroSpace A 3 hv
  have h := LinearMap.mem_ker.mp (probe_zeroSpace ho (k:=1) (by decide)
    (mat_zeroSpace_charZero A 4 pure))
  simp only [row_apply,pow_one] at h
  change ((b*x A) ⬝ᵥ (A *ᵥ p))=0 at h
  rw [Matrix.dotProduct_mulVec] at h
  have h' : (∑ i,secondRow A b i*(x A i)^j*v i)=0 := by
    simpa only [dotProduct,p,←mul_assoc] using h
  have e₀ := defect_moment ho hv j (by omega)
  have e₁ := defect_moment ho hv (j+2) (by omega)
  have e :
      (∑ i,secondError A b i*(x A i)^j*v i)=
      (∑ i,secondRow A b i*(x A i)^j*v i) -
      ((∑ i,b i*(x A i)^j*v i)-(∑ i,b i*(x A i)^(j+2)*v i))/2 := by
    rw [div_eq_mul_inv,sub_mul,Finset.sum_mul,Finset.sum_mul,←Finset.sum_sub_distrib,
      ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (secondRow A b i-b i*((1-(x A i)^2)/2))*(x A i)^j*v i=_
    rw [pow_add]
    ring
  rw [e,h',e₀,e₁,sub_self,zero_div,sub_zero]

private def cubic (a b c d y : K) : K := a+b*y+c*y^2+d*y^3

omit [CharZero K] in
private theorem interpolate4
    {x₀ x₁ x₂ x₃ v₀ v₁ v₂ v₃ : K}
    (h01 : x₀≠x₁) (h02 : x₀≠x₂) (h03 : x₀≠x₃)
    (h12 : x₁≠x₂) (h13 : x₁≠x₃) (h23 : x₂≠x₃) :
    ∃ a b c d, cubic a b c d x₀=v₀ ∧ cubic a b c d x₁=v₁ ∧
      cubic a b c d x₂=v₂ ∧ cubic a b c d x₃=v₃ := by
  let u₀ := v₀/((x₀-x₁)*(x₀-x₂)*(x₀-x₃))
  let u₁ := v₁/((x₁-x₀)*(x₁-x₂)*(x₁-x₃))
  let u₂ := v₂/((x₂-x₀)*(x₂-x₁)*(x₂-x₃))
  let u₃ := v₃/((x₃-x₀)*(x₃-x₁)*(x₃-x₂))
  have prod (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) : a*b*c≠0 :=
    mul_ne_zero (mul_ne_zero ha hb) hc
  have e₀ : u₀*((x₀-x₁)*(x₀-x₂)*(x₀-x₃))=v₀ := div_mul_cancel₀ _
    (prod _ _ _ (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02) (sub_ne_zero.mpr h03))
  have e₁ : u₁*((x₁-x₀)*(x₁-x₂)*(x₁-x₃))=v₁ := div_mul_cancel₀ _
    (prod _ _ _ (sub_ne_zero.mpr (Ne.symm h01)) (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13))
  have e₂ : u₂*((x₂-x₀)*(x₂-x₁)*(x₂-x₃))=v₂ := div_mul_cancel₀ _
    (prod _ _ _ (sub_ne_zero.mpr (Ne.symm h02)) (sub_ne_zero.mpr (Ne.symm h12)) (sub_ne_zero.mpr h23))
  have e₃ : u₃*((x₃-x₀)*(x₃-x₁)*(x₃-x₂))=v₃ := div_mul_cancel₀ _
    (prod _ _ _ (sub_ne_zero.mpr (Ne.symm h03)) (sub_ne_zero.mpr (Ne.symm h13)) (sub_ne_zero.mpr (Ne.symm h23)))
  refine ⟨-u₀*x₁*x₂*x₃-u₁*x₀*x₂*x₃-u₂*x₀*x₁*x₃-u₃*x₀*x₁*x₂,
    u₀*(x₁*x₂+x₁*x₃+x₂*x₃)+u₁*(x₀*x₂+x₀*x₃+x₂*x₃)+
      u₂*(x₀*x₁+x₀*x₃+x₁*x₃)+u₃*(x₀*x₁+x₀*x₂+x₁*x₂),
    -u₀*(x₁+x₂+x₃)-u₁*(x₀+x₂+x₃)-u₂*(x₀+x₁+x₃)-u₃*(x₀+x₁+x₂),
    u₀+u₁+u₂+u₃,?_,?_,?_,?_⟩
  · unfold cubic; linear_combination e₀
  · unfold cubic; linear_combination e₁
  · unfold cubic; linear_combination e₂
  · unfold cubic; linear_combination e₃

omit [CharZero K] in
private theorem poly_moment (w c : F → K) (a b d e : K) (j : ℕ) :
    (∑ i,w i*(c i)^j*cubic a b d e (c i))=
      a*(∑ i,w i*(c i)^j)+b*(∑ i,w i*(c i)^(j+1))+
        d*(∑ i,w i*(c i)^(j+2))+e*(∑ i,w i*(c i)^(j+3)) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [cubic,pow_add,pow_one]
  ring

omit [CharZero K] in
private theorem fin9_endpoints (w : F → K)
    (h : ∀ i, i≠7 → i≠8 → w i=0) : (∑ i,w i)=w 7+w 8 := by
  calc
    _ = ∑ i∈({7,8}:Finset F),w i := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro i _ hnot
      exact h i (fun eq => hnot (by simp [eq])) (fun eq => hnot (by simp [eq]))
    _ = _ := Finset.sum_pair (by decide : (7:F)≠8)

omit [CharZero K] in
private theorem paired_residues {a b x₇ x₈ : K} (hne : x₇≠x₈)
    (h0 : a+b=0) (h1 : x₇*a+x₈*b=0) : a=0 ∧ b=0 := by
  have e : (x₇-x₈)*a=0 := by linear_combination h1-x₈*h0
  have z : a=0 := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨z,by simpa only [z,zero_add] using h0⟩

theorem tail_cubic_pure {A : Matrix F F K} {b v : F → K} {γ : K}
    (ho : HasOrder 7 A b) (head : PaidHead A) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hg : γ≠0) (hb : b 8≠0)
    (inj : ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j)
    (hv : v∈zeroSpace A 3) : ∀ i∈tail,v i=0 := by
  let r := secondError A b
  have distinct (i j : F) (hi : i∈tail) (hj : j∈tail) (ne : i≠j) :
      x A i≠x A j := fun e => ne (inj _ _ hi hj e)
  obtain ⟨p₀,p₁,p₂,p₃,h₃,h₄,h₅,h₆⟩ :=
    interpolate4 (v₀:=v 3) (v₁:=v 4) (v₂:=v 5) (v₃:=v 6)
      (distinct 3 4 (by decide) (by decide) (by decide))
      (distinct 3 5 (by decide) (by decide) (by decide))
      (distinct 3 6 (by decide) (by decide) (by decide))
      (distinct 4 5 (by decide) (by decide) (by decide))
      (distinct 4 6 (by decide) (by decide) (by decide))
      (distinct 5 6 (by decide) (by decide) (by decide))
  let p : F → K := fun i => cubic p₀ p₁ p₂ p₃ (x A i)
  let d : F → K := fun i => r i*(v i-p i)
  have pRead (j : ℕ) (hj : j≤1) : (∑ i,r i*(x A i)^j*p i)=0 := by
    change (∑ i,r i*(x A i)^j*cubic p₀ p₁ p₂ p₃ (x A i))=0
    rw [poly_moment]
    rw [secondError_moments ho j (by omega),secondError_moments ho (j+1) (by omega),
      secondError_moments ho (j+2) (by omega),secondError_moments ho (j+3) (by omega)]
    ring
  have annihilate (j : ℕ) (hj : j≤1) : (∑ i,(x A i)^j*d i)=0 := by
    have eq : (∑ i,(x A i)^j*d i) =
      (∑ i,r i*(x A i)^j*v i) - (∑ i,r i*(x A i)^j*p i) := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [d]
      ring
    rw [eq,error_reads ho hv j hj,pRead j hj,sub_self]
  have dSupport (i : F) (h₇ : i≠7) (h₈ : i≠8) : d i=0 := by
    by_cases it : i∈tail
    · have hh := mem_tail.mp it
      have nr7 : i.val≠7 := fun e=>h₇ (Fin.ext e)
      have nr8 : i.val≠8 := fun e=>h₈ (Fin.ext e)
      have lt := i.isLt
      have cases : i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 := by omega
      rcases cases with a | a | a | a
      · have e : i=3 := Fin.ext a; simp [d,p,e,h₃]
      · have e : i=4 := Fin.ext a; simp [d,p,e,h₄]
      · have e : i=5 := Fin.ext a; simp [d,p,e,h₅]
      · have e : i=6 := Fin.ext a; simp [d,p,e,h₆]
    · change secondError A b i*(v i-p i)=0
      rw [second_head ho head i it,zero_mul]
  have sums0 := fin9_endpoints d dSupport
  have sums1 := fin9_endpoints (fun i=>x A i*d i) (by
    intro i e₀ e₁; rw [dSupport i e₀ e₁,mul_zero])
  have e₀ : d 7+d 8=0 := by
    rw [←sums0]
    simpa only [pow_zero,one_mul] using annihilate 0 (by decide)
  have e₁ : x A 7*d 7+x A 8*d 8=0 := by
    rw [←sums1]
    simpa only [pow_one] using annihilate 1 (by decide)
  obtain ⟨d₇,d₈⟩ := paired_residues (distinct 7 8 (by decide) (by decide) (by decide)) e₀ e₁
  have equal (i : F) (it : i∈tail) : v i=p i := by
    have zero : d i=0 := by
      by_cases e₇ : i=7
      · simpa only [e₇] using d₇
      by_cases e₈ : i=8
      · simpa only [e₈] using d₈
      exact dSupport i e₇ e₈
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left
      (second_error_every_tail ho head ha he hg hb inj i it))
  have q (j : ℕ) (hj : j≤3) : (∑ i,b i*(x A i)^j*p i)=0 := by
    rw [← defect_moment ho hv j hj]
    apply Finset.sum_congr rfl
    intro i _
    by_cases it : i∈tail
    · rw [equal i it]
    · rw [(head_rows ho head it).1,zero_mul,zero_mul,zero_mul]
  have Q (j : ℕ) (hj : j≤3) :
      p₀/((j:K)+1) + p₁/((j:K)+2) + p₂/((j:K)+3) + p₃/((j:K)+4)=0 := by
    have e := q j hj
    change (∑ i,b i*(x A i)^j*cubic p₀ p₁ p₂ p₃ (x A i))=0 at e
    rw [poly_moment,clock_moment ho j (by omega),clock_moment ho (j+1) (by omega),
      clock_moment ho (j+2) (by omega),clock_moment ho (j+3) (by omega)] at e
    simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at e
    rw [show (j:K)+1+1=(j:K)+2 by ring, show (j:K)+2+1=(j:K)+3 by ring,
      show (j:K)+3+1=(j:K)+4 by ring] at e
    simpa only [div_eq_mul_inv,one_mul] using e
  have Q0 := Q 0 (by decide)
  have Q1 := Q 1 (by decide)
  have Q2 := Q 2 (by decide)
  have Q3 := Q 3 (by decide)
  norm_num at Q0 Q1 Q2 Q3
  have z₀ : p₀=0 := by linear_combination 16*Q0-120*Q1+240*Q2-140*Q3
  have z₁ : p₁=0 := by linear_combination -120*Q0+1200*Q1-2700*Q2+1680*Q3
  have z₂ : p₂=0 := by linear_combination 240*Q0-2700*Q1+6480*Q2-4200*Q3
  have z₃ : p₃=0 := by linear_combination -140*Q0+1680*Q1-4200*Q2+2800*Q3
  intro i it
  rw [equal i it]
  simp [p,cubic,z₀,z₁,z₂,z₃]

/-- In the rational six-active-stage quadratic-clean seed chart, cubic
purity is forced even without an input assumption that the clocks differ. -/
theorem rational_seed_chart_cubic_pure
    {A : Matrix F F ℚ} {b v : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hg : γ≠0)
    (clean : ∀ i∈tail,monomialStageDefect A 1 i=0)
    (distinct : ∀ i j, i∉tail → j∉tail → i≠j → x A i≠x A j)
    (seed : ∀ i, i∉tail → monomialStageDefect A 1 i≠0)
    (active : ∀ i∈tail,b i≠0)
    (hv : v∈zeroSpace A 3) : ∀ i∈tail,v i=0 := by
  have head : HeadPaid A := headPaid_of_quadratic_clean_tail A clean distinct seed
  exact tail_cubic_pure ho head ha he hg (active 8 (by decide))
    (distinct_tail_of_headPaid ho ha he hg head active) hv

end
end RKResearch.Certified.SDIRKSevenTailCubicPurity
