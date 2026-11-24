module

public import RKCert.ReviewedNative.GradedSeparation
public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Tactic.LinearCombination

public section

/-! # Clock coefficients anchored at two physical endpoints

An exact zero at the origin and at a physical node one permits one fewer
ordinary moment. Eliminate the last coefficient using the node-one value;
the remaining paid test is precisely a shifted native Cauchy system.
There is no degree-specific rational matrix or arithmetic replay.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch

variable {K : Type*} [Field K]

/-- A paid Hilbert kernel with one extra equation supplied by the sum of
the actual coefficients instead of another moment. -/
theorem paid_sum_cauchy {ι : Type*} [Fintype ι] {A : Matrix ι ι K} {b : ι → K} {p n : ℕ}
    (ho : HasOrder p A b) (pay : 2*n+1≤p) (a : Fin (n+1) → K)
    (sum : (∑ j, a j)=0)
    (test : ∀ i : Fin n, (∑ j : Fin (n+1), a j / ((i.val+j.val+2:ℕ):K))=0) :
    a=0 := by
  let w : Fin n → K := fun j => ((n:K)-(j.val:K))*a j.castSucc
  have nz (k : ℕ) (kpos : 0<k) (paid : k≤p) : (k:K)≠0 :=
    (ho.natCast_isUnit kpos paid).ne_zero
  have ker (i : Fin n) :
      (∑ j : Fin n, w j / ((i.val+j.val+2:ℕ):K))=0 := by
    let D : K := ((i.val+n+2:ℕ):K)
    have d : D≠0 := nz _ (by omega) (by have := i.isLt; omega)
    have t := test i
    rw [Fin.sum_univ_castSucc] at t
    change (∑ j : Fin n, a j.castSucc / ((i.val+j.val+2:ℕ):K)) +
      a (Fin.last n) / D=0 at t
    have u := congrArg (fun x : K => D*x) t
    have last : D*(a (Fin.last n)/D)=a (Fin.last n) := by field_simp
    rw [mul_zero,mul_add,Finset.mul_sum,last] at u
    have s := sum
    rw [Fin.sum_univ_castSucc] at s
    have term (j : Fin n) :
        w j / ((i.val+j.val+2:ℕ):K) =
          D*(a j.castSucc / ((i.val+j.val+2:ℕ):K))-a j.castSucc := by
      have dn : ((i.val+j.val+2:ℕ):K)≠0 :=
        nz _ (by omega) (by have := i.isLt; have := j.isLt; omega)
      have diff : (n:K)-(j.val:K) = D-((i.val+j.val+2:ℕ):K) := by
        dsimp only [D]
        push_cast
        ring
      dsimp only [w]
      rw [diff]
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => term j),Finset.sum_sub_distrib]
    linear_combination u-s
  have z := moments_detect ho (n:=n) (d:=2) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) w ker
  have rest (j : Fin n) : a j.castSucc=0 := by
    have diff : (n:K)-(j.val:K)≠0 := by
      rw [←Nat.cast_sub (le_of_lt j.isLt)]
      exact nz _ (by have := j.isLt; omega) (by omega)
    exact (mul_eq_zero.mp (z j)).resolve_left diff
  have last : a (Fin.last n)=0 := by
    rw [Fin.sum_univ_castSucc] at sum
    simpa only [rest,Finset.sum_const_zero,zero_add] using sum
  ext j
  exact Fin.lastCases last rest j

/-- The zero first row and the nodal coordinate t at one separate
degree-(n+1) clocks from the genuine grade-j defects vanishing at t. -/
theorem coeff_separated_two_endpoints {s p n j : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i k, i ≤ k → A i k=0) (ho : HasOrder p A b)
    (mom : 2*n+1≤p) (pay : n+j≤p) {t : Fin (s+1)} (one : nodes A t=1)
    (a : Fin (n+2) → K) (inF : coeffEval A (n+1) a∈zeroAt (zeroSpace A j) t) : a=0 := by
  obtain ⟨f,endZero⟩ := mem_zeroAt.mp inF
  have z0 := origin_zeroSpace ha j f
  change coeffEval A (n+1) a 0=0 at z0
  have a0 : a 0=0 := by rwa [coeffEval_origin ha] at z0
  have endpoint : (∑ i : Fin (n+2), a i)=0 := by
    rw [coeffEval_apply] at endZero
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,normTree_clockTree,Pi.pow_apply,
      one,one_pow,mul_one] using endZero
  have sumTail : (∑ i : Fin (n+1), a i.succ)=0 := by
    rwa [Fin.sum_univ_succ,a0,zero_add] at endpoint
  have tests (i : Fin n) :
      (∑ k : Fin (n+1), a k.succ / ((i.val+k.val+2:ℕ):K))=0 := by
    have e := probe_zeroSpace (k:=i.val) ho (by have := i.isLt; omega) f
    change probe A b i.val (coeffEval A (n+1) a)=0 at e
    rw [probe_coeffEval ho (by have := i.isLt; omega),Fin.sum_univ_succ,a0,zero_div,zero_add] at e
    simpa only [Fin.val_succ,Nat.add_assoc] using e
  have tail := paid_sum_cauchy ho mom (fun i : Fin (n+1) => a i.succ) sumTail tests
  ext i
  exact Fin.cases a0 (fun k => congrFun tail k) i

end RKResearch.Certified.Graded.Reverse
