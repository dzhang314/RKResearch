module

public import RKCert.ERKLowBase
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # The physical rank-one backward Hermite obstruction -/
namespace RKCert.Paired
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- Formal polynomial Hermite residual for an arbitrary diagonal c: no
assumption that c is the row sum of the chronological matrix. -/
noncomputable def hermiteBack (A : Fin s → Fin s → K) (c b : Vec K s) :
    Polynomial K →ₗ[K] Vec K s :=
  let E : Polynomial K →ₗ[K] Vec K s := LinearMap.pi fun i => Polynomial.leval (c i)
  (diag b).comp E + (transMat A).comp ((diag b).comp (E.comp derivative))

omit [CharZero K] in
theorem hermiteBack_apply (A : Fin s → Fin s → K) (c b : Vec K s)
    (P : Polynomial K) (i : Fin s) :
    hermiteBack A c b P i = b i * P.eval (c i) +
      transMat A (fun j => b j * P.derivative.eval (c j)) i := rfl

omit [CharZero K] in
theorem hermiteBack_at_of_no_later_derivative {A : Fin s → Fin s → K}
    (ha : StrictLower A) (c b : Vec K s) (P : Polynomial K) (i : Fin s)
    (ht : ∀ j, i < j → b j * P.derivative.eval (c j)=0) :
    hermiteBack A c b P i=b i*P.eval (c i) := by
  rw [hermiteBack_apply]
  have hz : transMat A (fun j => b j * P.derivative.eval (c j)) i=0 :=
    transMat_vanish ha i _ ht i le_rfl
  rw [hz,add_zero]

private theorem exists_last_predicate (P : Fin s → Prop) (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ j, i < j → ¬ P j := by
  classical
  let T : Finset (Fin s) := Finset.univ.filter P
  obtain ⟨i,hi⟩ := h
  have hn : T.Nonempty := ⟨i,by simp [T,hi]⟩
  let j := T.max' hn
  have hm : j∈T := T.max'_mem hn
  refine ⟨j,(by simpa [T] using hm),?_⟩
  intro k hk hP
  exact (not_le_of_gt hk) (Finset.le_max' T k (by simp [T,hP]))

/-- If the reflected weighted moments are 1/2, 1/6, 1/12, the actual
quadratic, cubic and quartic two-jet residuals at endpoint one cannot
lie in a one-dimensional space. Signed weights and repeated/exterior
nodes are allowed. This is the manuscript's rank-one backward gate. -/
theorem hermite_backward_rank_two {A : Fin s → Fin s → K}
    (ha : StrictLower A) (c b : Vec K s)
    (h0 : (∑ i, b i*(1-c i))=1/2) (h1 : (∑ i, (b i*(1-c i))*c i)=1/6)
    (h2 : (∑ i, (b i*(1-c i))*c i^2)=1/12)
    (U : Submodule K (Vec K s))
    (hB : hermiteBack A c b ((1-X)^2)∈U)
    (hBX : hermiteBack A c b ((1-X)^2*X)∈U)
    (hBXX : hermiteBack A c b ((1-X)^2*X^2)∈U) :
    2 ≤ finrank K U := by
  let e (i : Fin s) := b i*(1-c i)
  have hn : ∃ i, e i≠0 := by
    by_contra! hz
    have hz' : (∑ i, e i)=0 := Finset.sum_eq_zero fun i _ => hz i
    have he : (1:K)/2=0 := h0.symm.trans hz'
    exact (div_ne_zero one_ne_zero (by norm_num)) he
  obtain ⟨j,hj,hjlast⟩ := exists_last_predicate (fun i => e i≠0) hn
  let y := c j
  have hprev : ∃ i, e i≠0 ∧ c i≠y := by
    by_contra! hh
    have hm1 : (∑ i, e i*c i)=y*(∑ i,e i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : e i=0
      · simp [he]
      · rw [hh i he,mul_comm]
    have hm2 : (∑ i, e i*c i^2)=y*(∑ i,e i*c i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : e i=0
      · simp [he]
      · rw [hh i he]; ring
    change (∑ i,e i)=_ at h0
    change (∑ i,e i*c i)=_ at h1
    change (∑ i,e i*c i^2)=_ at h2
    rw [h1,h0] at hm1
    rw [h2,h1] at hm2
    apply (one_ne_zero : (1:K)≠0)
    linear_combination 36*hm2-12*hm1
  obtain ⟨i,⟨hi,hiy⟩,hilast⟩ := exists_last_predicate (fun k => e k≠0 ∧ c k≠y) hprev
  have hex : ∀ k, e k=0 → b k=0 ∨ c k=1 := by
    intro k hk
    rcases mul_eq_zero.mp hk with hk'|hk'
    · exact Or.inl hk'
    · exact Or.inr ((sub_eq_zero.mp hk').symm)
  let B : Polynomial K := (1-X)^2
  let F : Polynomial K := B*(X-C y)^2
  let u := hermiteBack A c b F
  let v := hermiteBack A c b B
  have hF : F = B*X^2 + (-2*y) • (B*X) + y^2 • B := by
    simp only [F,Polynomial.smul_eq_C_mul,map_mul,map_neg,map_ofNat,map_pow]
    ring
  have hu : u∈U := by
    change hermiteBack A c b F∈U
    rw [hF,map_add,map_add,map_smul,map_smul]
    exact U.add_mem (U.add_mem hBXX (U.smul_mem _ hBX)) (U.smul_mem _ hB)
  have hv : v∈U := hB
  have hdB : B.derivative.eval 1=0 := by simp [B,Polynomial.derivative_pow]
  have hdF : F.derivative.eval 1=0 := by
    simp [F,B,Polynomial.derivative_mul,Polynomial.derivative_pow,Polynomial.derivative_sub]
  have hdFy : F.derivative.eval y=0 := by
    simp [F,B,Polynomial.derivative_mul,Polynomial.derivative_pow,Polynomial.derivative_sub]
  have htF (k : Fin s) (hk : i < k) : b k * F.derivative.eval (c k)=0 := by
    by_cases he : e k=0
    · rcases hex k he with h|h
      · rw [h,zero_mul]
      · rw [h,hdF,mul_zero]
    · have h : c k=y := by by_contra hh; exact hilast k hk ⟨he,hh⟩
      rw [h,hdFy,mul_zero]
  have htFj (k : Fin s) (hk : j < k) : b k * F.derivative.eval (c k)=0 := by
    rcases hex k (not_not.mp (hjlast k hk)) with h|h
    · rw [h,zero_mul]
    · rw [h,hdF,mul_zero]
  have htBj (k : Fin s) (hk : j < k) : b k * B.derivative.eval (c k)=0 := by
    rcases hex k (not_not.mp (hjlast k hk)) with h|h
    · rw [h,zero_mul]
    · rw [h,hdB,mul_zero]
  have hvi : v j≠0 := by
    rw [show v j = b j * B.eval (c j) from hermiteBack_at_of_no_later_derivative ha c b B j htBj]
    have hj' := mul_ne_zero_iff.mp hj
    simpa [B] using mul_ne_zero hj'.1 (pow_ne_zero 2 hj'.2)
  have hui : u i≠0 := by
    rw [show u i = b i * F.eval (c i) from hermiteBack_at_of_no_later_derivative ha c b F i htF]
    have hi' := mul_ne_zero_iff.mp hi
    simpa only [F,B,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C] using
      mul_ne_zero hi'.1 (mul_ne_zero (pow_ne_zero 2 hi'.2) (pow_ne_zero 2 (sub_ne_zero.mpr hiy)))
  have huj : u j=0 := by
    rw [show u j = b j * F.eval (c j) from hermiteBack_at_of_no_later_derivative ha c b F j htFj]
    simp [F,y]
  by_contra! hr
  have hvn : v≠0 := fun hz => hvi (congrFun hz j)
  have he : Submodule.span K {v}=U := Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem ..).mpr hv) (by rw [finrank_span_singleton hvn]; omega)
  rw [← he] at hu
  obtain ⟨a,ha'⟩ := Submodule.mem_span_singleton.mp hu
  have hz := congrFun ha' j
  change a*v j=u j at hz
  rw [huj] at hz
  have ha0 := (mul_eq_zero.mp hz).resolve_right hvi
  rw [ha0,zero_smul] at ha'
  exact hui (congrFun ha'.symm i)

end RKCert.Paired
