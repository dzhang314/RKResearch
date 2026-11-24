module

public import RKCert.ERKOrderNineGoodPrimeNatSelector
public import RKCert.ERKOrderNineH48Diagnostics

@[expose] public section

namespace RKCert.GoodPrimeDense
open Polynomial RKCert.Paired RKCert.FixedFactor

instance instPrime1319 : Fact (Nat.Prime 1319) := ⟨by decide +kernel⟩

abbrev Fp := ZMod 1319

def factorRecipe (S : NatSelectorDatum 1319) : List ℕ :=
  plus (naturalPrime 1319) (List.replicate S.split.rel.length 0 ++ [1])
    (opposite (naturalPrime 1319) S.split.rel)

def composeFactors : List (NatSelectorDatum 1319) → List ℕ
  | [] => [1]
  | S :: SS => times (naturalPrime 1319) (factorRecipe S) (composeFactors SS)

theorem factorRecipe_poly (S : NatSelectorDatum 1319) :
    decode (fun k : ℕ => (k:Fp)) (factorRecipe S) = S.split.factor Fp := by
  let s := Sound.naturalPrime (R:=Fp) (p:=1319) (by decide)
  unfold factorRecipe NatSplitDatum.factor
  have e : (naturalPrime 1319).zero = 0 := rfl
  rw [decode_plus s,decode_opposite s,←e,decode_shift s]
  simp [decode,ofCoeffList_cons,sub_eq_add_neg]

theorem composeFactors_poly (D : List (NatSelectorDatum 1319)) :
    decode (fun k : ℕ => (k:Fp)) (composeFactors D) = (D.map (fun S=>S.split.factor Fp)).prod := by
  let s := Sound.naturalPrime (R:=Fp) (p:=1319) (by decide)
  induction D with
  | nil => simp [composeFactors,decode,ofCoeffList_cons]
  | cons S D ih =>
    rw [composeFactors,decode_times s,factorRecipe_poly,ih,List.map_cons,List.prod_cons]


def FactorizationData (R : List (NatSelectorDatum 1319)) : Prop :=
  h48Coeffs.map (intResidue 1319) = timesScalar (naturalPrime 1319) 455 (composeFactors R)

section
variable (primeRows : List (NatSelectorDatum 1319)) (factorization_check : FactorizationData primeRows)
  (rows_checked : ∀ {S}, S∈primeRows → S.Checked 581)

include factorization_check in
theorem h48_prime_factorization :
    h48.map (Int.castRingHom Fp) =
      C (455:Fp) * (primeRows.map (fun S=>S.split.factor Fp)).prod := by
  have e := congrArg (decode (fun k : ℕ => (k:Fp))) (show
      h48Coeffs.map (intResidue 1319) = timesScalar (naturalPrime 1319) 455 (composeFactors primeRows)
      from factorization_check)
  rw [decode_timesScalar (Sound.naturalPrime (R:=Fp) (p:=1319) (by decide)),composeFactors_poly] at e
  simpa [decode,h48,map_ofCoeffList,List.map_map,Function.comp_def,intResidue_cast (R:=Fp) (p:=1319) (by decide)] using e

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
theorem mod1319_terminal_of_certificate {E : Type*} [Field E] [CharP E 1319] (h u v l d : E)
    (checkD : d*84=1) (checkL : (h48.map (Int.castRingHom E)).eval l=0)
    (roots : RootSystem (pencilAt l d) h u v) (diag : ∀j,zEval (diagAux j) ![l,h,u,v]=0) :
    terminalAt h u v l d≠0 := by
  let ψ := ZMod.castHom (dvd_refl 1319) E
  have ei : ψ.comp (Int.castRingHom Fp) = Int.castRingHom E := Subsingleton.elim ..
  have z : (h48.map (Int.castRingHom Fp)).eval₂ ψ l=0 := by
    rw [eval₂_eq_eval_map,map_map,ei]
    exact checkL
  rw [h48_prime_factorization primeRows factorization_check,eval₂_mul,eval₂_C,eval₂_list_prod,List.map_map] at z
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
  exact NatSelectorDatum.terminal_nonzero (by decide) S 581 h u v l (rows_checked mem) sr roots diag

include factorization_check rows_checked in
/-- The verified characteristic-zero transfer from the finite factor certificate. -/
theorem sixOn_atlas_impossible_of_certificate {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (hr : (lobattoPencil l).eval h=0) (ur : (lobattoPencil l).eval u=0)
    (vr : (lobattoPencil l).eval v=0) (uh : u≠h) (vh : v≠h) (vu : v≠u)
    (k : sixOnK8 h u v l=0) :
    sixOnTerminalProduct h u v l ≠ 0 := by
  have root : RootSystem (pencilAt l ((84:K)⁻¹)) h u v :=
    rootSystem_of_distinct ((pencilAt_eval _ _).trans hr) ((pencilAt_eval _ _).trans ur)
      ((pencilAt_eval _ _).trans vr) uh vh vu
  rw [←terminalAt_legacy]
  refine endpoint_good_prime 1319 h48 (by decide +kernel) ?_ diagAux
    (fun h u v l d => mod1319_terminal_of_certificate primeRows factorization_check rows_checked h u v l d) h u v l
    (h48_zero_of_k8 root k) root (normStages_vanish root k)
  rw [h48_leadingCoeff]
  decide +kernel

end

end RKCert.GoodPrimeDense
