module

public import RKCert.ERKOrderNineGoodPrimeAssembly
public import RKCert.ERKOrderNineCompactSelector

@[expose] public section

/-! Witnessed polynomial products and mixed legacy/compact root selection. -/
namespace RKCert.CompactResidue

open Polynomial RKCert.GoodPrimeDense RKCert.Paired RKCert.FixedFactor

theorem factorization_of_product (R : List (NatSelectorDatum 1319))
    (checked : Product 1319 ([455] :: R.map factorRecipe) (h48Coeffs.map (intResidue 1319))) :
    h48.map (Int.castRingHom Fp) =
      C (455:Fp) * (R.map (fun S=>S.split.factor Fp)).prod := by
  have e := checked.correct (E:=Fp)
  rw [List.map_cons,List.prod_cons,List.map_map] at e
  have eq (S : NatSelectorDatum 1319) :
      polynomial Fp (factorRecipe S) = S.split.factor Fp := factorRecipe_poly S
  have c : polynomial Fp [455] = C (455:Fp) := by
    simp [polynomial,decode,Polynomial.ofCoeffList_cons]
  have raw : polynomial Fp (h48Coeffs.map (intResidue 1319)) =
      h48.map (Int.castRingHom Fp) := by
    simp [polynomial,decode,h48,map_ofCoeffList,List.map_map,Function.comp_def,
      intResidue_cast (R:=Fp) (p:=1319) (by decide)]
  simp only [c,Function.comp_def,eq,raw] at e
  exact e.symm

section
variable (primeRows : List (NatSelectorDatum 1319))
    (factorization_check : h48.map (Int.castRingHom Fp) =
      C (455:Fp) * (primeRows.map (fun S=>S.split.factor Fp)).prod)
    (rows_checked : ∀ {S}, S∈primeRows → S.Checked 581 ∨ TapeChecked S 581)

private theorem zero_product_choice {B E : Type*} [Field E] (C : List B) (f : B→E)
    (z : (C.map f).prod=0) : ∃ x∈C, f x=0 := by
  induction C with
  | nil => simp at z
  | cons a as ih =>
    rw [List.map_cons,List.prod_cons,mul_eq_zero] at z
    rcases z with z|z
    · exact ⟨a,List.mem_cons_self,z⟩
    · obtain ⟨b,m,zb⟩ := ih z
      exact ⟨b,List.mem_cons_of_mem _ m,zb⟩

include factorization_check rows_checked in
theorem mod1319_terminal_of_mixed_certificate {E : Type*} [Field E] [CharP E 1319] (h u v l d : E)
    (checkD : d*84=1) (checkL : (h48.map (Int.castRingHom E)).eval l=0)
    (roots : RootSystem (pencilAt l d) h u v) (diag : ∀j,zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l d≠0 := by
  let ψ := ZMod.castHom (dvd_refl 1319) E
  have ei : ψ.comp (Int.castRingHom Fp) = Int.castRingHom E := Subsingleton.elim ..
  have z : (h48.map (Int.castRingHom Fp)).eval₂ ψ l=0 := by
    rw [eval₂_eq_eval_map,map_map,ei]
    exact checkL
  rw [factorization_check,eval₂_mul,eval₂_C,eval₂_list_prod,List.map_map] at z
  have n : ψ (455:Fp)≠0 := fun e=>(by decide : (455:Fp)≠0) (ψ.injective (e.trans ψ.map_zero.symm))
  obtain ⟨S,mem,Sz⟩ := zero_product_choice primeRows _ ((mul_eq_zero.mp z).resolve_left n)
  have aD : ψ (581:Fp)*84=1 := by
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg ψ (show (581:Fp)*84=1 by decide +kernel)
  have dEq : d=ψ (581:Fp) := by
    apply mul_right_cancel₀ (show (84:E)≠0 by
      intro e
      simp [e] at checkD)
    rw [checkD,aD]
  have sr : (S.split.factor E).eval l=0 := by
    have z' : ((S.split.factor Fp).map ψ).eval l=0 := by
      rw [←eval₂_eq_eval_map]
      exact Sz
    have e : (S.split.factor Fp).map ψ = S.split.factor E := by
      simp [NatSplitDatum.factor,Polynomial.map_sub,Polynomial.map_pow,map_ofCoeffList,List.map_map,
        Function.comp_def]
    rwa [e] at z'
  have dE : d=(581:E) := by simpa only [map_ofNat] using dEq
  rw [dE] at roots ⊢
  rcases rows_checked mem with prior | compact
  · exact NatSelectorDatum.terminal_nonzero (by decide) S 581 h u v l prior sr roots diag
  · exact compact.terminal_nonzero (by decide) h u v l sr roots diag

include factorization_check rows_checked in
/-- The verified characteristic-zero transfer from the finite factor certificate. -/
theorem sixOn_atlas_impossible_of_mixed_certificate {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (hr : (lobattoPencil l).eval h=0) (ur : (lobattoPencil l).eval u=0)
    (vr : (lobattoPencil l).eval v=0) (uh : u≠h) (vh : v≠h) (vu : v≠u)
    (k : sixOnK8 h u v l=0) :
    sixOnTerminalProduct h u v l ≠ 0 := by
  have root : RootSystem (pencilAt l ((84:K)⁻¹)) h u v :=
    rootSystem_of_distinct ((pencilAt_eval _ _).trans hr) ((pencilAt_eval _ _).trans ur)
      ((pencilAt_eval _ _).trans vr) uh vh vu
  rw [←terminalAt_legacy]
  refine endpoint_good_prime 1319 h48 (by decide +kernel) ?_ diagAux
    (fun h u v l d => mod1319_terminal_of_mixed_certificate primeRows factorization_check rows_checked h u v l d) h u v l
    (h48_zero_of_k8 root k) root (normStages_vanish root k)
  rw [h48_leadingCoeff]
  decide +kernel

end

end RKCert.CompactResidue
