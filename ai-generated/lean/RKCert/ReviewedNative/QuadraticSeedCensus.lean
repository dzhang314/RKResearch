module

public import RKCert.ReviewedNative.NativeHiddenCarrier

@[expose] public section

/-! # Paid quadratic seed fibres each occupy two actual physical rows

This field-general result is independent of the weak or strong
midpoint chart. It uses only the paid seed moments and exact
interpolation on the distinct reflected seed clocks. -/
namespace RKResearch.Certified.Graded.Reverse.Thin

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- When all site isolators fit the actual seed moment budget, every
nonzero seed clock has at least two original rows; a single nonzero
coefficient could not have zero isolated signed mass. -/
theorem quadratic_seed_double_rows (ho : HasOrder p A b)
    (pay : (weightedSites (reflectedClock A) (quadraticSeed A b)).card+2≤p) :
    2*(weightedSites (reflectedClock A) (quadraticSeed A b)).card≤
      (Hidden.activeRows (quadraticSeed A b)).card := by
  classical
  let y := reflectedClock A
  let d := quadraticSeed A b
  let S := weightedSites y d
  let T := Hidden.activeRows d
  have image : T.image y=S := rfl
  have two (a : K) (ha : a∈S) : 2≤(T.filter fun i=>y i=a).card := by
    obtain ⟨i,di,eq⟩ := mem_weightedSites.mp ha
    let B := T.filter fun j=>y j=a
    have ih : i∈B := Finset.mem_filter.mpr ⟨(Hidden.mem_activeRows i).mpr di,eq⟩
    by_contra! small
    change B.card<2 at small
    have one : B.card=1 := by have := Finset.card_pos.mpr ⟨i,ih⟩;omega
    let R := Lagrange.nodal (S.erase a) id
    have deg : R.natDegree+3≤p := by
      rw [show R.natDegree=(S.erase a).card from Lagrange.natDegree_nodal,Finset.card_erase_of_mem ha]
      have pos := Finset.card_pos.mpr ⟨a,ha⟩
      change S.card+2≤p at pay
      omega
    have ri : R.eval (y i)≠0 := by
      rw [eq]
      exact Lagrange.eval_nodal_not_at_node fun z hz ez => (Finset.mem_erase.mp hz).1 ez.symm
    have only (j : Fin s) (ne : j≠i) : weightedEval y d R j=0 := by
      by_cases z : d j=0
      · simp [z]
      have diff : y j≠a := by
        intro e
        exact ne (Finset.card_le_one.mp one.le j
          (Finset.mem_filter.mpr ⟨(Hidden.mem_activeRows j).mpr z,e⟩) i ih)
      have hy : y j∈S.erase a := Finset.mem_erase.mpr ⟨diff,mem_weightedSites.mpr ⟨j,z,rfl⟩⟩
      rw [weightedEval_apply,show R.eval (y j)=0 from Lagrange.eval_nodal_at_node (v:=id) hy,zero_mul]
    have sum := seed_eval_mass ho R deg
    change (∑ j,weightedEval y d R j)=0 at sum
    rw [Finset.sum_eq_single i (fun j _ h=>only j h) (fun e=>(e (Finset.mem_univ _)).elim),
      weightedEval_apply] at sum
    exact (mul_ne_zero ri di) sum
  calc
    2*S.card = ∑ _∈S, (2:ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ a∈S,(T.filter fun i=>y i=a).card := Finset.sum_le_sum two
    _ = T.card := image ▸ (Finset.card_eq_sum_card_image y T).symm

end
end RKResearch.Certified.Graded.Reverse.Thin
