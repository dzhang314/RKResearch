module

public import RKCert.Research.SDIRKSevenTailCollision
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.SDIRKSevenTailCollision
open RKResearch Graded
open scoped Matrix BigOperators Classical

noncomputable section

private theorem no_ordered_collision {A : Matrix F F ℚ} {b : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hg : γ≠0)
    (head : HeadPaid A) (active : ∀ i ∈ tail,b i≠0)
    {lo hi : F} (hl : lo ∈ tail) (hh : hi ∈ tail) (ht : lo<hi) (e : x A lo=x A hi) :
    False := by
  let c := x A
  let src := tail.erase hi
  let sites := src.image c
  let support := activeQuadratureSites b c
  have hc (i : F) (it : i ∈ tail) : c i ∈ sites := by
    by_cases ih : i=hi
    · have hne := ne_of_lt ht
      exact Finset.mem_image.mpr ⟨lo,Finset.mem_erase.mpr ⟨hne,hl⟩,
        e.trans (congrArg c ih).symm⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨ih,it⟩,rfl⟩
  have hSub : support ⊆ sites := by
    intro v hv
    have hn := (mem_activeQuadratureSites_iff.mp hv).2
    by_contra hy
    apply hn
    unfold quadratureSiteWeight
    apply Finset.sum_eq_zero
    intro i im
    by_cases it : i ∈ tail
    · have hclock : c i = v := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using im
      exact (hy (hclock ▸ hc i it)).elim
    · exact (head_rows ho head it).1
  have htail : tail.card=6 := by decide +kernel
  have hsrc : src.card=5 := by simp [src,Finset.card_erase_of_mem hh,htail]
  have hin : 5 ≤ support.card := by
    simpa only [show min 5 (7-5/2)=5 by decide] using
      ho.prime_floor_activeQuadratureSites_of_rat 5 (by decide) (fun v _ => ⟨v,rfl⟩)
  have hup : sites.card≤src.card := Finset.card_image_le
  have hLow : support.card≤sites.card := Finset.card_le_card hSub
  have hEq : sites.card=src.card := by omega
  have inj := Finset.injOn_of_card_image_eq hEq
  have hSupport : support=sites := Finset.eq_of_subset_of_card_le hSub (by omega)
  let twin : SingleTwin c :=
    { lo := lo
      hi := hi
      ht := hl
      lt := ht
      same := e
      only := by
        intro i j it jt ij
        by_cases ihi : i=hi
        · by_cases jhi : j=hi
          · exact Or.inl (ihi.trans jhi.symm)
          · have ex : c lo=c j := e.trans ((congrArg c ihi).symm.trans ij)
            have lj : lo=j := inj (Finset.mem_erase.mpr ⟨ne_of_lt ht,hl⟩)
              (Finset.mem_erase.mpr ⟨jhi,jt⟩) ex
            exact Or.inr (Or.inr ⟨ihi,lj.symm⟩)
        · by_cases jhi : j=hi
          · have ex : c i=c lo := ij.trans ((congrArg c jhi).trans e.symm)
            have il : i=lo := inj (Finset.mem_erase.mpr ⟨ihi,it⟩)
              (Finset.mem_erase.mpr ⟨ne_of_lt ht,hl⟩) ex
            exact Or.inr (Or.inl ⟨il,jhi⟩)
          · exact Or.inl (inj (Finset.mem_erase.mpr ⟨ihi,it⟩)
              (Finset.mem_erase.mpr ⟨jhi,jt⟩) ij) }
  have hnMass : b lo+b hi≠0 := by
    have hm : c lo ∈ support := hSupport.symm ▸ hc lo hl
    have nz := (mem_activeQuadratureSites_iff.mp hm).2
    intro bad
    apply nz
    have hsum : (∑ i ∈ tail.filter (fun i => c i=c lo),b i) =
        quadratureSiteWeight b c (c lo) := by
      unfold quadratureSiteWeight
      refine Finset.sum_subset ?_ ?_
      · intro i im
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at im ⊢
        exact im.2
      · intro i im inot
        apply (head_rows ho head ?_).1
        intro it
        apply inot
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at im ⊢
        exact ⟨it,im⟩
    rw [twin.filtered_pair,Finset.sum_pair (ne_of_lt ht)] at hsum
    exact hsum.symm.trans bad
  exact no_single_twin ho ha he hg head (active 7 (by decide)) (active 8 (by decide)) twin
    (fun e7 e8 => by change lo=7 at e7; change hi=8 at e8; simpa only [e7,e8] using hnMass)

/-- The six active tail clocks have to be distinct. The three head
coordinate columns must belong to the actual grade-four defect space;
there is no simplifying row hypothesis and no fixed diagonal. -/
theorem distinct_tail_of_headPaid {A : Matrix F F ℚ} {b : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hg : γ≠0)
    (head : HeadPaid A) (active : ∀ i ∈ tail,b i≠0) :
    ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j := by
  intro i j ih jh eq
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact no_ordered_collision ho ha he hg head active ih jh lt eq
  · exact no_ordered_collision ho ha he hg head active jh ih gt eq.symm

private theorem axis_from_seed (A : Matrix F F ℚ)
    (clean : ∀ i ∈ tail,monomialStageDefect A 1 i=0)
    {i j k : F} (hij : x A i≠x A j) (hik : x A i≠x A k)
    (ni : monomialStageDefect A 1 i≠0)
    (cover : ∀ l, l ∉ tail → l=i ∨ l=j ∨ l=k) :
    Pi.single i (1:ℚ) ∈ zeroSpace A 4 := by
  let g := monomialStageDefect A 1
  let adv (a : ℚ) (v : F → ℚ) := diag (x A) v-a • v
  have step {n : ℕ} {v : F → ℚ} (hv : v ∈ zeroSpace A n) (a : ℚ) :
      adv a v ∈ zeroSpace A (n+1) := by
    exact (zeroSpace A (n+1)).sub_mem (diag_zeroSpace A n hv)
      ((zeroSpace A (n+1)).smul_mem a (zeroSpace_mono A (by omega) hv))
  let V := adv (x A j) (adv (x A k) g)
  have vpaid : V ∈ zeroSpace A 4 := step (step (monomialStageDefect_mem A 1) _) _
  have form (l : F) : V l=(x A l-x A j)*(x A l-x A k)*g l := by
    simp only [V,adv,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply]
    ring
  have nz : V i ≠ 0 := by rw [form]; exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hij)
    (sub_ne_zero.mpr hik)) ni
  have equal : (Pi.single i (1:ℚ)) = (V i)⁻¹ • V := by
    funext l
    by_cases el : l=i
    · subst l
      simp only [Pi.single_eq_same,Pi.smul_apply,smul_eq_mul]
      exact (inv_mul_cancel₀ nz).symm
    · rw [Pi.single_eq_of_ne el]
      change 0=(V i)⁻¹*V l
      rw [form l]
      by_cases lh : l∈tail
      · have cl : g l=0 := clean l lh
        rw [cl,mul_zero,mul_zero]
      · rcases cover l lh with eq | eq | eq
        · exact (el eq).elim
        · rw [eq,sub_self,zero_mul,zero_mul,mul_zero]
        · rw [eq,sub_self,mul_zero,zero_mul,mul_zero]
  rw [equal]
  exact (zeroSpace A 4).smul_mem _ vpaid

/-- Three distinct helper clocks with nonvanishing quadratic defects
and a quadratic-clean tail necessarily expose the whole paid head. -/
theorem headPaid_of_quadratic_clean_tail (A : Matrix F F ℚ)
    (clean : ∀ i ∈ tail,monomialStageDefect A 1 i=0)
    (distinct : ∀ i j, i∉tail → j∉tail → i≠j → x A i≠x A j)
    (seed : ∀ i, i∉tail → monomialStageDefect A 1 i≠0) : HeadPaid A := by
  have head_cases (i : F) (ih : i∉tail) : i=(0:F) ∨ i=(1:F) ∨ i=(2:F) := by
    have e : i.val < 3 := Nat.lt_of_not_ge (fun h => ih (mem_tail.mpr h))
    have eq : i.val=0∨i.val=1∨i.val=2 := by omega
    rcases eq with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  intro i hi
  rcases head_cases i hi with rfl | rfl | rfl
  · exact axis_from_seed A clean (j:=1) (k:=2) (distinct 0 1 hi (by decide) (by decide))
      (distinct 0 2 hi (by decide) (by decide)) (seed 0 hi) head_cases
  · apply axis_from_seed A clean (j:=0) (k:=2) (distinct 1 0 hi (by decide) (by decide))
      (distinct 1 2 hi (by decide) (by decide)) (seed 1 hi)
    intro l lh
    rcases head_cases l lh with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · apply axis_from_seed A clean (j:=0) (k:=1) (distinct 2 0 hi (by decide) (by decide))
      (distinct 2 1 hi (by decide) (by decide)) (seed 2 hi)
    intro l lh
    rcases head_cases l lh with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- The rational collision escape is unavailable throughout this
three-helper / six-active-stage class, not just at common diagonal 1/4. -/
theorem distinct_tail_in_seed_chart {A : Matrix F F ℚ} {b : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hg : γ≠0)
    (clean : ∀ i ∈ tail,monomialStageDefect A 1 i=0)
    (distinct : ∀ i j, i∉tail → j∉tail → i≠j → x A i≠x A j)
    (seed : ∀ i, i∉tail → monomialStageDefect A 1 i≠0)
    (active : ∀ i ∈ tail,b i≠0) :
    ∀ i j, i ∈ tail → j ∈ tail → x A i=x A j → i=j :=
  distinct_tail_of_headPaid ho ha he hg (headPaid_of_quadratic_clean_tail A clean distinct seed) active

end
end RKResearch.Certified.SDIRKSevenTailCollision
