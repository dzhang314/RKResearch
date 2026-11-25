module

public import RKCert.ReviewedNative.CausalStage
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # A chronological obstruction to a one-dimensional compressed row residual

All sources are ordinary physical class coordinates. The three primitive
rows are *not* assumed to vanish or to define an RK method on those classes.
Their residuals may be arbitrary scalar multiples of the same row.
-/
namespace RKResearch.Certified.Graded.HyperplaneTerminal

open scoped Classical Matrix
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

private theorem earliest (ord : Fin s ≃ Fin s) (P : Fin s → Prop) (ex : ∃i,P i) :
    ∃i, P i ∧ ∀j, (ord j).val < (ord i).val → ¬P j := by
  classical
  let S := Finset.univ.filter P
  obtain ⟨i,hi,hl⟩ := Finset.exists_min_image S ord
    (by obtain ⟨i,hi⟩:=ex; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  intro j hj hp
  exact (not_le_of_gt (show ord j<ord i from hj))
    (hl j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩))

private theorem prefix_scale {ord : Fin s ≃ Fin s}
    {N : (Fin s → K) →ₗ[K] (Fin s → K)} (hc : Causal ord N)
    (i : Fin s) (x b : Fin s→K) (a : K)
    (eq : ∀j, (ord j).val<(ord i).val → x j=a*b j) :
    N x i=a*N b i := by
  have h := hc i (x-a • b) (fun j hj=>sub_eq_zero.mpr (eq j hj))
  simpa only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_eq_zero] using h

/-- The three unnormalized reverse primitive rows cannot share one
hyperplane functional when the output supports two clocks. The only zero
reflected-clock mask needed is visibility of its supported coordinates.
`ord` is reverse physical chronology in the compressed tableau. -/
theorem three_rows_impossible (ord : Fin s ≃ Fin s)
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (hc : Causal ord N)
    (y b l : Fin s → K) (a d e : K)
    (one : ∀i, N b i=y i*b i+a*l i)
    (two : ∀i, 2*N (fun j=>y j*b j) i=y i^2*b i+d*l i)
    (three : ∀i, 3*N (fun j=>y j^2*b j) i=y i^3*b i+e*l i)
    (mask : ∀i, b i≠0 → y i≠0 ∨ l i≠0)
    (distinct : ∃i j, b i≠0 ∧ b j≠0 ∧ y i≠y j) : False := by
  obtain ⟨u,v,bu,bv,uv⟩:=distinct
  obtain ⟨L,bL,prev⟩:=earliest ord (fun i=>b i≠0) ⟨u,bu⟩
  have bz (j : Fin s) (hj : (ord j).val<(ord L).val) : b j=0 :=
    not_not.mp (prev j hj)
  have z0 := hc L b bz
  have z1 := hc L (fun j=>y j*b j) (fun j hj=>by rw [bz j hj,mul_zero])
  have z2 := hc L (fun j=>y j^2*b j) (fun j hj=>by rw [bz j hj,mul_zero])
  have r0 := one L
  have r1 := two L
  have r2 := three L
  rw [z0] at r0
  rw [z1,mul_zero] at r1
  rw [z2,mul_zero] at r2
  have ex : ∃i, b i≠0 ∧ y i≠y L := by
    by_cases eq : y u=y L
    · exact ⟨v,bv,fun bad=>uv (eq.trans bad.symm)⟩
    · exact ⟨u,bu,eq⟩
  obtain ⟨i,hi,onlyL⟩:=earliest ord (fun i=>b i≠0 ∧ y i≠y L) ex
  have priorClocks (j : Fin s) (hj : (ord j).val<(ord i).val) :
      b j=0 ∨ y j=y L := by
    by_cases bj : b j=0
    · exact Or.inl bj
    · exact Or.inr (not_not.mp (fun bad=>onlyL j hj ⟨bj,bad⟩))
  have f1 := prefix_scale hc i (fun j=>y j*b j) b (y L)
    (by intro j hj; rcases priorClocks j hj with h|h <;> simp [h])
  have f2 := prefix_scale hc i (fun j=>y j^2*b j) b (y L^2)
    (by intro j hj; rcases priorClocks j hj with h|h <;> simp [h])
  have eq1 := two i
  have eq2 := three i
  rw [f1,one i] at eq1
  rw [f2,one i] at eq2
  by_cases Y : y L=0
  · have lL := (mask L bL).resolve_left (not_not.mpr Y)
    have dL : d*l L=0 := by simpa [Y] using r1.symm
    have dz := (mul_eq_zero.mp dL).resolve_right lL
    have quiet : y i^2*b i=0 := by simpa [Y,dz] using eq1.symm
    exact hi.2 ((eq_zero_of_pow_eq_zero ((mul_eq_zero.mp quiet).resolve_right hi.1)).trans Y.symm)
  · have lL : l L≠0 := by
      intro z
      have bad : y L*b L=0 := by simpa [z] using r0.symm
      exact (mul_ne_zero Y bL) bad
    have a0 : a≠0 := by
      intro z
      have bad : y L*b L=0 := by simpa [z] using r0.symm
      exact (mul_ne_zero Y bL) bad
    have dd : d=y L*a := by
      apply mul_right_cancel₀ lL
      linear_combination y L*r0-r1
    have ee : e=y L^2*a := by
      apply mul_right_cancel₀ lL
      linear_combination y L^2*r0-r2
    rw [dd] at eq1
    rw [ee] at eq2
    have cubic : y i*(y i-y L)^2*b i=0 := by
      linear_combination 2*y L*eq1-eq2
    have times : y i*(y i-y L)^2=0 := (mul_eq_zero.mp cubic).resolve_right hi.1
    have yi : y i=0 := (mul_eq_zero.mp times).resolve_right
      (pow_ne_zero _ (sub_ne_zero.mpr hi.2))
    have li := (mask i hi.1).resolve_left (not_not.mpr yi)
    have kill : y L*(a*l i)=0 := by
      rw [yi] at eq1
      linear_combination eq1
    exact (mul_ne_zero Y (mul_ne_zero a0 li)) kill

end RKResearch.Certified.Graded.HyperplaneTerminal
