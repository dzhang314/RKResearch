module

public import RKCert.GradeSeparation
public import RKCert.BackwardMoments

@[expose] public section

/-! # Endpoint moment separation without positivity

If a polynomial with vanishing constant term has moments equal to a fixed
point mass at 1 through degree q, subtract the zeroth moment from each of
the q others. The resulting q-by-q system is an ordinary shifted Cauchy
matrix after dividing each column by its nonzero pole distance. This
proves the endpoint obstruction in every attained characteristic.
-/
namespace RKCert.Paired

variable {K : Type*} [Field K] {s : ℕ} {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}

private theorem frac_diff (x y z : K) (hy : y≠0) (hs : x+y≠0) :
    -x*(z/y/(x+y)) = z/(x+y) - z/y := by
  field_simp
  ring

/-- A constant sequence of q+1 mixed moments of the q positive monomials
must be zero. No fixed determinant or enumeration of the order is used. -/
theorem constant_mixed_moments {q : ℕ} (ho : HasTreeOrderAtLeast A b p) (hq : 2*q+1≤p)
    (a : Fin q → K) (m : K)
    (he : ∀ k : Fin (q+1), (∑ j : Fin q, a j / ((k.val+j.val+2 : ℕ):K))=m) :
    (∀ j, a j = 0) ∧ m=0 := by
  let a' : Fin q → K := fun j => a j / ((j.val+2:ℕ):K)
  have hbase := he 0
  simp only [Fin.val_zero, zero_add] at hbase
  have hd (j : Fin q) : ((j.val+2 : ℕ):K) ≠ 0 :=
    cast_ne_zero_of_budget ho (by omega) (by omega)
  have hs (i : Fin q) : (∑ j : Fin q, a' j / ((i.val+j.val+3 : ℕ):K))=0 := by
    have hi := he i.succ
    have e (j : Fin q) : i.succ.val+j.val+2=i.val+j.val+3 := by simp only [Fin.val_succ]; omega
    simp_rw [e] at hi
    have hx : ((i.val+1:ℕ):K) ≠ 0 := cast_ne_zero_of_budget ho (by omega) (by omega)
    have eqn (j : Fin q) :
        -((i.val+1:ℕ):K) * (a' j / ((i.val+j.val+3:ℕ):K)) =
          a j / ((i.val+j.val+3:ℕ):K) - a j / ((j.val+2:ℕ):K) := by
      have hn : ((i.val+j.val+3:ℕ):K) ≠ 0 := cast_ne_zero_of_budget ho (by omega) (by omega)
      have hsum : ((i.val+j.val+3:ℕ):K) = ((i.val+1:ℕ):K) + ((j.val+2:ℕ):K) := by
        rw [← Nat.cast_add]
        congr 1; omega
      dsimp only [a']
      rw [hsum] at hn ⊢
      exact frac_diff _ _ _ (hd j) hn
    have hh : -((i.val+1:ℕ):K) * (∑ j : Fin q, a' j / ((i.val+j.val+3:ℕ):K))=0 := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => eqn j),
        Finset.sum_sub_distrib,hi,hbase,sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hx)
  have ha' := moments_detect ho (d:=3) (by decide) (by omega) (fun i j => by omega) a' hs
  have ha (j : Fin q) : a j=0 := (div_eq_zero_iff.mp (ha' j)).resolve_right (hd j)
  exact ⟨ha, by simpa [ha] using hbase.symm⟩

end RKCert.Paired
