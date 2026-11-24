module

public import RKCert.NodalHermiteRank
public import RKCert.ReviewedNative.PolynomialStageSeparation
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! A clock-invariant part of the genuine defect flag cannot hide many
clock blocks. Use only a single paid probe on the invariant space. Clock
multiples of a common polynomial lift give the entire shifted Cauchy
test at no further cost in the defect grade. No sign, distinct-clock or
individual nonzero-weight premise is used. -/
namespace RKResearch.Certified.Graded

open Polynomial RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s j p : ℕ}

/-- On a finite set of stage clocks, closure under the clock gives closure
under every scalar function of it, via polynomial interpolation. -/
theorem clock_function_mem {c : Fin s → K} {U : Submodule K (Fin s → K)}
    (inv : ∀ v∈U, diag c v∈U) (f : K → K) {v} (hv : v∈U) :
    (fun i => f (c i) * v i)∈U := by
  classical
  have times (k : ℕ) : (fun i => c i ^ k * v i) ∈ U := by
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      convert inv _ ih using 1
      ext i
      simp [pow_succ',mul_assoc]
  have pol (P : K[X]) : (fun i => P.eval (c i)*v i)∈U := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => convert U.add_mem hP hQ using 1; ext; simp [add_mul]
    | monomial k a => convert U.smul_mem a (times k) using 1; ext; simp [mul_assoc]
  let S := Finset.univ.image c
  let P := Lagrange.interpolate S id f
  have e (i : Fin s) : P.eval (c i) = f (c i) :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (Finset.mem_image_of_mem c (Finset.mem_univ i))
  simpa only [e] using pol P

/-- Reuse the tree-independent prefix-matching definition, with the literal
stage clock and actual invariant submodule. -/
theorem clock_mask_invariant {c : Fin s → K} {U : Submodule K (Fin s → K)}
    (inv : ∀ v∈U, diag c v ∈ U) : MaskInvariant c U := by
  intro a v hv
  have h := clock_function_mem inv (fun z => if z = a then 1 else 0) hv
  convert h using 1
  ext i
  by_cases hci : c i = a <;> simp [blockMask,hci]

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Nonzero clock blocks at which the constant column cannot be matched.
At least r such blocks are forced whenever order 2r pays the shifted
Cauchy tests. The argument also works in every admissible positive
characteristic; the paid-unit theorem separates denominators. -/
theorem paid_failed_clock_blocks (ho : HasOrder p A b) (pay : j+1≤p)
    {U : Submodule K (Fin s → K)} (hUF : U≤zeroSpace A j)
    (hmask : MaskInvariant (nodes A) U) {r : ℕ} (paid : 2*r≤p) :
    r≤(failedNodes (nodes A) 1 U s).card := by
  classical
  by_contra hs
  let S := insert 0 (failedNodes (nodes A) 1 U s)
  let H : K[X] := nodalHull S
  have hS : S.card ≤ r := by
    have h := Finset.card_insert_le 0 (failedNodes (nodes A) 1 U s)
    dsimp [S]
    omega
  have dH : H.natDegree ≤ r := (natDegree_nodalHull S).le.trans hS
  have H0 : H.eval 0 = 0 := nodalHull_eval_of_mem (Finset.mem_insert_self 0 _)
  obtain ⟨w,hwU,hw⟩ := exists_masked_prefix_lift (nodes A) 1 hmask s H H0
    (fun a ha => nodalHull_eval_of_mem (Finset.mem_insert_of_mem ha))
  have ew : evalNodes A H = w := by
    ext i
    simpa using (hw i i.isLt).symm
  let a : Fin (r+1) → K := fun i => H.coeff i.val
  have eh : coeffEval A r a = evalNodes A H := (evalNodes_eq_coeffEval A H dH).symm
  have a0 : a 0 = 0 := by simpa [a,coeff_zero_eq_eval_zero] using H0
  have test (i : Fin r) : probe A b i.val (coeffEval A r a) = 0 := by
    rw [eh, ew]
    have hg := mulByBlock_mem (nodes A) hmask (fun x => x ^ i.val) hwU
    have hp0 : probe A b 0 (fun l => (nodes A l)^i.val*w l)=0 :=
      probe_zeroSpace ho (by omega) (hUF hg)
    simpa only [probe,row_apply,dotProduct,pow_zero,mul_one,mul_assoc] using hp0
  have ker (i : Fin r) :
      (∑ k : Fin r, a k.succ / ((i.val+k.val+2:ℕ):K))=0 := by
    have e := test i
    rw [probe_coeffEval ho (by have := i.isLt; omega),Fin.sum_univ_succ,a0,zero_div,zero_add] at e
    simpa only [Fin.val_succ,Nat.add_assoc] using e
  have vanish := moments_detect ho (d:=2) (by decide) (by omega)
    (fun (i k : Fin r) => by have := i.isLt; have := k.isLt; omega) (fun k => a k.succ) ker
  have az (i : Fin (r+1)) : a i = 0 := Fin.cases a0 vanish i
  apply (monic_nodalHull S).ne_zero
  ext k
  rw [coeff_zero]
  by_cases hk : k ≤ r
  · exact az ⟨k,Nat.lt_succ_of_le hk⟩
  · exact coeff_eq_zero_of_natDegree_lt (dH.trans_lt (Nat.lt_of_not_ge hk))

end RKResearch.Certified.Graded
