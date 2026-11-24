module

public import RKCert.TreeMoments
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Finite Cauchy matrices without a characteristic restriction

Eliminate the first column and first row. The remaining system is another
Cauchy system, after nonzero row and column rescaling. This algebraic proof
does not use a real ordering, positivity, or square-root operations.
-/
namespace RKCert.Paired

variable {K : Type*} [Field K]

/-- Mixed Cauchy moments detect every coefficient over a field. Only the stated
node differences and pole distances need be nonzero. -/
theorem cauchy_kernel {n : ℕ} (x y a : Fin n → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0)
    (he : ∀ i, (∑ j : Fin n, a j / (x i + y j)) = 0) : ∀ j, a j = 0 := by
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
    let xs : Fin n → K := fun i => x i.succ
    let ys : Fin n → K := fun j => y j.succ
    let as' : Fin n → K := fun j => a j.succ * (y j.succ-y 0) / (x 0+y j.succ)
    have hx' : Function.Injective xs := fun _ _ h => Fin.succ_injective _ (hx h)
    have hy' : Function.Injective ys := fun _ _ h => Fin.succ_injective _ (hy h)
    have hxy' (i j : Fin n) : xs i + ys j ≠ 0 := hxy _ _
    have rem (i : Fin n) : (∑ j : Fin n, as' j / (xs i+ys j))=0 := by
      let d := x i.succ - x 0
      have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => Fin.succ_ne_zero i (hx h))
      have eql (j : Fin n) :
          d * (as' j / (xs i+ys j)) =
          (x i.succ+y 0) * (a j.succ / (x i.succ+y j.succ)) -
            (x 0+y 0) * (a j.succ / (x 0+y j.succ)) := by
        dsimp [d,as',xs,ys]
        field_simp [hxy]
        ring
      have hdprod : d * (∑ j : Fin n, as' j / (xs i+ys j)) = 0 := by
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => eql j), Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        have htail (l : Fin (n+1)) : (∑ j : Fin n, a j.succ / (x l+y j.succ)) =
            -(a 0 / (x l+y 0)) := by
          have hh := he l
          rw [Fin.sum_univ_succ] at hh
          exact eq_neg_of_add_eq_zero_right hh
        rw [htail, htail]
        field_simp [hxy]
        ring
      exact (mul_eq_zero.mp hdprod).resolve_left hd
    have hs := ih xs ys as' hx' hy' hxy' rem
    have htail (j : Fin n) : a j.succ=0 := by
      have h := hs j
      change a j.succ * (y j.succ - y 0) / (x 0+y j.succ) = 0 at h
      have hu := (div_eq_zero_iff.mp h).resolve_right (hxy _ _)
      exact (mul_eq_zero.mp hu).resolve_right (sub_ne_zero.mpr (fun hh => Fin.succ_ne_zero j (hy hh)))
    refine Fin.cases ?_ htail
    have h := he 0
    rw [Fin.sum_univ_succ] at h
    simp only [htail, zero_div, Finset.sum_const_zero, add_zero] at h
    exact (div_eq_zero_iff.mp h).resolve_right (hxy _ _)

end RKCert.Paired
