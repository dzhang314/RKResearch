module

public import RKCert.Dirk15ReadySample

@[expose] public section

/-! # Strictly ordered companion-band minors have only the diagonal term -/
namespace RKCert.Compound
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

private theorem ordered_perm_eq_one {k : ℕ} (σ : Equiv.Perm (Fin k))
    (h : StrictMono σ) : σ=1 := by
  let E := StrictMono.orderIsoOfSurjective σ h σ.surjective
  have e : E=OrderIso.refl _ := Subsingleton.elim _ _
  apply Equiv.ext
  intro a
  exact congrArg (fun f : Fin k ≃o Fin k => f a) e

theorem det_ordered_band {n k : ℕ} (r c : Fin k→Fin n)
    (hr : StrictMono r) (hc : StrictMono c) (M : Matrix (Fin k) (Fin k) R)
    (axis : ∀ i j, M i j≠0 → (c j).val≤(r i).val ∧ (r i).val≤(c j).val+1) :
    M.det=∏ i,M i i := by
  classical
  rw [Matrix.det_apply,Finset.sum_eq_single (1:Equiv.Perm (Fin k))]
  · simp
  · intro σ _ ne
    by_cases zero : ∃ j, M (σ j) j=0
    · obtain ⟨j,hj⟩ := zero
      have he : (∏ i : Fin k,M (σ i) i)=0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [he,smul_zero]
    · push Not at zero
      exfalso
      apply ne
      apply ordered_perm_eq_one
      intro i j ij
      have hx := (axis (σ i) i (zero i)).2
      have hy := (axis (σ j) j (zero j)).1
      have hxy : (c i).val<(c j).val := hc ij
      by_contra! not_lt
      have nne : σ j≠σ i := fun f => (ne_of_lt ij).symm (σ.injective f)
      have lt : σ j<σ i := lt_of_le_of_ne not_lt nne
      have rv : (r (σ j)).val<(r (σ i)).val := hr lt
      omega
  · simp

def bandTag : List (ℕ×ℕ) → Option (ℕ×ℤ)
  | [] => some (0,1)
  | (r,c)::t =>
    if r=c then (bandTag t).map (fun q=>(q.1+1,q.2))
    else if r=c+1 then (bandTag t).map (fun q=>(q.1,-q.2))
    else none

noncomputable def bandPolynomial (L : List (ℕ×ℕ)) : R[X] :=
  match bandTag L with
  | none => 0
  | some q => C (q.2:R)*X^q.1

theorem bandPolynomial_eq_prod (L : List (ℕ×ℕ)) :
    (bandPolynomial L:R[X])=
      (L.map (fun q => (if q.1=q.2 then X else 0)-(if q.1=q.2+1 then 1 else 0))).prod := by
  induction L with
  | nil => simp [bandPolynomial,bandTag]
  | cons a L ih =>
    obtain ⟨r,c⟩ := a
    simp only [List.map_cons,List.prod_cons,←ih]
    by_cases rc : r=c
    · subst r
      cases z : bandTag L <;> simp [bandPolynomial,bandTag,z,pow_succ,mul_left_comm,mul_comm]
    · by_cases rstep : r=c+1
      · subst r
        cases z : bandTag L <;> simp [bandPolynomial,bandTag,z]
      · simp [bandPolynomial,bandTag,rc,rstep]

theorem bandTag_degree (L : List (ℕ×ℕ)) {p : ℕ×ℤ} (s : bandTag L=some p) :
    p.1≤L.length := by
  induction L generalizing p with
  | nil => simp [bandTag] at s; rw [←s]; decide
  | cons a L ih =>
    obtain ⟨r,c⟩ := a
    simp only [bandTag] at s
    split_ifs at s
    all_goals cases h : bandTag L with
    | none => simp [h] at s
    | some v =>
      have dd := ih h
      simp only [h,Option.map_some,Option.some.injEq] at s
      subst p
      simp only [List.length_cons]
      omega

/-- When every selected column is nonlast, the polynomial minor is a single
signed monomial or zero. No full Laplace loops are needed. -/
theorem band_submatrix_det {n k : ℕ} (r c : Fin k→Fin n)
    (strictR : StrictMono r) (strictC : StrictMono c)
    (b : Fin (n+1)→R) (hn : ∀ i,(c i).val+1<n) :
    ((rawResolvent b).submatrix r c).det=
      bandPolynomial (List.ofFn (fun i=>((r i).val,(c i).val))) := by
  rw [det_ordered_band r c strictR strictC,bandPolynomial_eq_prod,List.map_ofFn,List.prod_ofFn]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Matrix.submatrix_apply,rawResolvent,hn,ite_true,Fin.ext_iff,Function.comp_apply]
  · intro i j z
    by_cases e : r i=c j
    · simp [e]
    · by_cases sh : (r i).val=(c j).val+1
      · omega
      · exfalso
        apply z
        simp [Matrix.submatrix_apply,rawResolvent,hn,e,sh]

end RKCert.Compound
