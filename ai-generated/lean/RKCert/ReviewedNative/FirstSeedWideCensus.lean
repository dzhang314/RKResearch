module

public import RKCert.ReviewedNative.ERK17WideRank

@[expose] public section

/-! # The very-wide ordinary signed census and inactive original rows -/
namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- Ordinary unit moments through degree n detect every polynomial of
degree at most n under the paid Cauchy budget. -/
theorem paid_unit_moments_detect (ho : HasOrder p A b) {n : ℕ} {P : K[X]}
    (pay : 2*n+1≤p) (d : P.natDegree≤n)
    (tests : ∀i : Fin (n+1), (primitive (X^i.val*P)).eval 1=0) : P=0 := by
  let a : Fin (n+1)→K := fun j=>P.coeff j.val
  have moments (i : Fin (n+1)) : (∑ j : Fin (n+1), a j/((i.val+j.val+1:ℕ):K))=0 := by
    have h := probe_evalNodes ho P i.val (by have := i.isLt; omega)
    rw [tests i,evalNodes_eq_coeffEval A P d,probe_coeffEval ho (by have := i.isLt; omega)] at h
    exact h
  have z := moments_detect ho (n:=n+1) (d:=1) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a moments
  ext j
  rw [coeff_zero]
  by_cases hj : j<n+1
  · exact z ⟨j,hj⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The true unmarked signed contrast has four sites. If its nodal
polynomial had degree at most three, nine exact unit moments would
force the product with the nonzero degree-five head to vanish. -/
theorem contrast_four_sites_of_order17 (ho : HasOrder 17 A b) (Q P : K[X])
    (qn : Q≠0) (qd : Q.natDegree≤5) (pd : P.natDegree≤4) :
    4≤(weightedSites (reflectedClock A) (linearContrast A b Q P)).card := by
  let y := reflectedClock A
  let W := linearContrast A b Q P
  let T := weightedSites y W
  let N := nodalHull T
  let F := Q*N
  change 4≤T.card
  by_contra! small
  have nd : N.natDegree=T.card := natDegree_nodalHull T
  have fd : F.natDegree≤8 := by
    have h := natDegree_mul_le (p:=Q) (q:=N)
    dsimp [F]
    omega
  have tests (i : Fin 9) : (primitive (X^i.val*F)).eval 1=0 := by
    let R := X^i.val*N
    have rd : R.natDegree ≤ i.val+T.card := by
      dsimp only [R]
      exact natDegree_mul_le_of_le (natDegree_X_pow _).le nd.le
    have z : (∑ j,weightedEval y W R j)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases wj : W j=0
      · simp [wj]
      · have rt : N.eval (y j)=0 :=
          nodalHull_eval_of_mem (mem_weightedSites.mpr ⟨j,wj,rfl⟩)
        simp [R,rt]
    have ms := linear_contrast_moment ho Q P R (by have := i.isLt; omega)
      (by have := i.isLt; omega)
    rw [z,show R*Q=X^i.val*F by dsimp [R,F];ring] at ms
    exact ms.symm
  exact (mul_ne_zero qn (monic_nodalHull T).ne_zero)
    (paid_unit_moments_detect ho (by decide) fd tests)

/-- Actual coordinates where neither the first seed nor the output is
present. This excludes neither end by definition. -/
def inactiveRows (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) : Finset (Fin s) :=
  Finset.univ.filter (fun i=>firstSeed A b i=0 ∧ b i=0)

@[simp] theorem mem_inactiveRows {i : Fin s} :
    i∈inactiveRows A b ↔ firstSeed A b i=0 ∧ b i=0 := by simp [inactiveRows]

theorem not_visible_of_inactive {i : Fin s} (h : i∈inactiveRows A b) :
    ¬visible A b i := by
  obtain ⟨d,e⟩ := mem_inactiveRows.mp h
  simp [visible,d,e]

theorem visible_of_not_inactive {i : Fin s} (h : i∉inactiveRows A b) :
    visible A b i := by
  by_contra no
  have both : firstSeed A b i=0 ∧ b i=0 := by simpa only [visible,not_or,not_not] using no
  exact h (mem_inactiveRows.mpr both)

/-- The carrier's dimension is the actual number of inactive
coordinates, using restriction and zero extension on the original rows. -/
theorem carrier_rank_eq_inactive_card :
    finrank K (carrier A b)=(inactiveRows A b).card := by
  let I := inactiveRows A b
  let R : carrier A b →ₗ[K] (I→K) :=
    LinearMap.pi (fun i:I => (LinearMap.proj i.val).comp (carrier A b).subtype)
  have inj : Function.Injective R := by
    apply (injective_iff_map_eq_zero _).mpr
    intro u h
    apply Subtype.ext
    funext i
    by_cases hi : i∈I
    · exact congrFun h (⟨i,hi⟩:I)
    · exact (mem_carrier_iff.mp u.property) i (visible_of_not_inactive hi)
  have onto : Function.Surjective R := by
    intro f
    let w : Fin s→K := fun i => if hi:i∈I then f ⟨i,hi⟩ else 0
    have hw : w∈carrier A b := mem_carrier_iff.mpr (fun i hi => by
      have off : i∉I := fun h=>not_visible_of_inactive h hi
      simp [w,off])
    refine ⟨⟨w,hw⟩,?_⟩
    funext i
    change w i.val=f i
    simp only [w,i.property,dite_eq_left,Subtype.coe_eta]
  have e := (LinearEquiv.ofBijective R ⟨inj,onto⟩).finrank_eq
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using e

theorem inactive_filler (v : Fin s→K) :
    ∃ w∈carrier A b, ∀ i∈inactiveRows A b,w i=v i := by
  let w : Fin s→K := fun i=>if i∈inactiveRows A b then v i else 0
  refine ⟨w,mem_carrier_iff.mpr (fun i hi => ?_),fun i h=>by simp only [w,h,ite_true]⟩
  have off : i∉inactiveRows A b := fun h=>not_visible_of_inactive h hi
  simp only [w,off,ite_false]

end
end RKResearch.Certified.Graded.Reverse.FirstWide
