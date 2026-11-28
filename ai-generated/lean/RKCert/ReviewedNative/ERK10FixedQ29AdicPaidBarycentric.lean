module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

@[expose] public section

/-! Paid barycentric interpolation works over a ring, with no field or
domain hypothesis. Pairwise unit differences replace equality of roots. -/
namespace RKResearch.Certified.PaidBarycentric

open Polynomial
open scoped Ring BigOperators

noncomputable section
set_option maxHeartbeats 0

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

def rootPoly (s : Finset ι) (x : ι → R) : Polynomial R :=
  ∏ i ∈ s, (X-C (x i))

def Den (s : Finset ι) (x : ι → R) (i : ι) : R :=
  ∏ j ∈ s.erase i, (x i-x j)

def Paid (s : Finset ι) (x : ι → R) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (x i-x j)

def basis (s : Finset ι) (x : ι → R) (i : ι) : Polynomial R :=
  C ((Den s x i)⁻¹ʳ)*rootPoly (s.erase i) x

theorem den_unit {s : Finset ι} {x : ι → R} (h : Paid s x) {i : ι} (hi : i∈s) :
    IsUnit (Den s x i) := by
  apply IsUnit.prod_iff.mpr
  intro j hj
  obtain ⟨hne,hjs⟩ := Finset.mem_erase.mp hj
  exact h i hi j hjs hne.symm

theorem rootPoly_insert (s : Finset ι) (x : ι → R) {i : ι} (hi : i∉s) :
    rootPoly (insert i s) x = (X-C (x i))*rootPoly s x := by
  simp [rootPoly,Finset.prod_insert hi]

theorem rootPoly_erase {s : Finset ι} (x : ι → R) {i : ι} (hi : i∈s) :
    rootPoly s x = (X-C (x i))*rootPoly (s.erase i) x := by
  nth_rw 1 [←Finset.insert_erase hi]
  exact rootPoly_insert _ x (Finset.notMem_erase _ _)

theorem rootPoly_monic (s : Finset ι) (x : ι → R) : (rootPoly s x).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (x i))

theorem rootPoly_natDegree [Nontrivial R] (s : Finset ι) (x : ι → R) :
    (rootPoly s x).natDegree = s.card := by
  induction s using Finset.induction_on with
  | empty => simp [rootPoly]
  | @insert i s hi ih =>
    rw [rootPoly_insert _ _ hi,(monic_X_sub_C _).natDegree_mul (rootPoly_monic _ _),
      natDegree_X_sub_C,ih,Finset.card_insert_of_notMem hi,Nat.add_comm]

theorem eval_rootPoly (s : Finset ι) (x : ι → R) (y : R) :
    (rootPoly s x).eval y = ∏ i ∈ s, (y-x i) := by
  change (evalRingHom y) _ = _
  simp [rootPoly,map_prod]

theorem rootPoly_eval_zero {s : Finset ι} (x : ι → R) {i : ι} (hi : i∈s) :
    (rootPoly s x).eval (x i) = 0 := by
  rw [rootPoly_erase x hi,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul]

theorem eval_basis {s : Finset ι} {x : ι → R} (h : Paid s x)
    {i j : ι} (hi : i∈s) (hj : j∈s) :
    (basis s x i).eval (x j) = if i=j then 1 else 0 := by
  by_cases e : i=j
  · subst j
    rw [ite_eq_left rfl,basis,eval_mul,eval_C,eval_rootPoly]
    exact Ring.inverse_mul_cancel _ (den_unit h hi)
  · have hmem : j∈s.erase i := Finset.mem_erase.mpr ⟨fun h => e h.symm,hj⟩
    rw [ite_eq_right e,basis,eval_mul,rootPoly_eval_zero _ hmem,mul_zero]

theorem rootPoly_dvd {s : Finset ι} {x : ι → R} (pay : Paid s x) {p : Polynomial R}
    (hzero : ∀ i∈s, p.eval (x i)=0) : rootPoly s x ∣ p := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp [rootPoly]
  | @insert i s hi ih =>
    have hir := hzero i (Finset.mem_insert_self _ _)
    obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr (show IsRoot p (x i) from hir)
    have pay' : Paid s x := by
      intro a ha b hb hn
      exact pay a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hn
    have hqzero : ∀ j ∈ s, q.eval (x j)=0 := by
      intro j hj
      have hj' := hzero j (Finset.mem_insert_of_mem hj)
      rw [hq,eval_mul,eval_sub,eval_X,eval_C] at hj'
      have hji : j≠i := fun he => hi (he ▸ hj)
      exact (pay j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _) hji).mul_left_cancel
        (by simpa only [mul_zero] using hj')
    obtain ⟨w,hw⟩ := ih pay' hqzero
    exact ⟨w,by rw [rootPoly_insert _ _ hi,hq,hw,mul_assoc]⟩

theorem interp [Nontrivial R] {s : Finset ι} {x : ι → R} (pay : Paid s x)
    (p : Polynomial R) (hp : p.natDegree<s.card) :
    (∑ i∈s, C (p.eval (x i))*basis s x i) = p := by
  let r : Polynomial R := ∑ i∈s, C (p.eval (x i))*basis s x i
  have hdeg : r.natDegree≤s.card-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_C_mul_le ..).trans ((natDegree_C_mul_le ..).trans ?_)
    rw [rootPoly_natDegree,Finset.card_erase_of_mem hi]
  have hzeros : ∀ j∈s, (r-p).eval (x j)=0 := by
    intro j hj
    rw [eval_sub,sub_eq_zero]
    change (evalRingHom (x j)) (∑ i∈s,C (p.eval (x i))*basis s x i) = _
    rw [map_sum,Finset.sum_eq_single j]
    · change (C (p.eval (x j))*basis s x j).eval (x j) = _
      rw [eval_mul,eval_C,eval_basis pay hj hj,ite_eq_left rfl,mul_one]
    · intro i hi hij
      change (C (p.eval (x i))*basis s x i).eval (x j) = _
      rw [eval_mul,eval_basis pay hi hj,ite_eq_right hij,mul_zero]
    · exact fun hn => (hn hj).elim
  have hdvd := rootPoly_dvd pay hzeros
  apply sub_eq_zero.mp (show r-p = 0 from ?_)
  by_contra hn
  have hh := (rootPoly_monic s x).natDegree_le_of_dvd hn hdvd
  rw [rootPoly_natDegree] at hh
  have hsub := (natDegree_sub_le r p).trans (max_le hdeg (by omega))
  omega

theorem coeff_basis_top [Nontrivial R] {s : Finset ι} (x : ι→R) {i : ι} (hi : i∈s) :
    (basis s x i).coeff (s.card-1) = (Den s x i)⁻¹ʳ := by
  have hroot := rootPoly_natDegree (s.erase i) x
  rw [Finset.card_erase_of_mem hi] at hroot
  rw [basis,coeff_C_mul,←hroot,coeff_natDegree,(rootPoly_monic _ _).leadingCoeff,mul_one]

/-- The exact cofactor sum of a lower-degree polynomial vanishes. -/
theorem low_sum [Nontrivial R] {s : Finset ι} {x : ι→R} (pay : Paid s x)
    (p : Polynomial R) (hp : p.natDegree < s.card-1) :
    ∑ i∈s, p.eval (x i)*(Den s x i)⁻¹ʳ = 0 := by
  have hh := congrArg (fun q : Polynomial R => q.coeff (s.card-1))
    (interp pay p (by omega))
  rw [coeff_eq_zero_of_natDegree_lt hp,finsetSum_coeff] at hh
  rw [←hh]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_C_mul,coeff_basis_top x hi]

end
end RKResearch.Certified.PaidBarycentric

#print axioms RKResearch.Certified.PaidBarycentric.interp
#print axioms RKResearch.Certified.PaidBarycentric.low_sum
