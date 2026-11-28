module

public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring

@[expose] public section

/-! Interpolation quadrature with two paid hull moments. This generic
bridge is independent of the selected order-twelve tableau. -/
namespace RKResearch.Certified.PaidNodalQuadrature

open Polynomial
open scoped Polynomial BigOperators

variable {K ι : Type*} [Field K] [DecidableEq ι]

noncomputable def quadr (s : Finset ι) (v : ι → K) (I : K[X] →ₗ[K] K) : K[X] →ₗ[K] K :=
  ∑ i ∈ s, (I (Lagrange.basis s v i)) • Polynomial.leval (v i)

theorem quadr_apply (s : Finset ι) (v : ι → K) (I : K[X] →ₗ[K] K) (q : K[X]) :
    quadr s v I q = ∑ i ∈ s, I (Lagrange.basis s v i)*q.eval (v i) := by
  simp only [quadr, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Polynomial.leval_apply]

theorem exact_below (s : Finset ι) (v : ι → K) (I : K[X] →ₗ[K] K)
    (distinct : Set.InjOn v s) (q : K[X]) (hq : q.natDegree < s.card) :
    quadr s v I q = I q := by
  by_cases z : q=0
  · simp [z]
  have deg := (natDegree_lt_iff_degree_lt z).mp hq
  have h := Lagrange.eq_interpolate distinct deg
  have e := congrArg I h
  rw [Lagrange.interpolate_apply, map_sum] at e
  rw [quadr_apply, e]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]

theorem multiple_zero (s : Finset ι) (v : ι → K) (I : K[X] →ₗ[K] K) (q : K[X]) :
    quadr s v I (Lagrange.nodal s v*q) = 0 := by
  rw [quadr_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, mul_zero]

/-- Interpolation weights for n distinct nodes are exact through n+1,
provided the two integral hull moments of grades zero and one vanish. -/
theorem exact_two_more (s : Finset ι) (v : ι → K) (I : K[X] →ₗ[K] K)
    (hs : s.Nonempty) (distinct : Set.InjOn v s)
    (h0 : I (Lagrange.nodal s v) = 0) (h1 : I (X*Lagrange.nodal s v)=0)
    (q : K[X]) (hq : q.natDegree < s.card+2) :
    quadr s v I q = I q := by
  let H := Lagrange.nodal s v
  let r := q %ₘ H
  let u := q /ₘ H
  have monic : H.Monic := Lagrange.nodal_monic
  have deg : H.natDegree = s.card := Lagrange.natDegree_nodal
  have Hne : H ≠ 1 := by
    intro e
    rw [e,natDegree_one] at deg
    exact hs.card_pos.ne' deg.symm
  have rdeg : r.natDegree < s.card := by
    rw [← deg]
    exact natDegree_modByMonic_lt _ monic Hne
  have udeg : u.natDegree ≤ 1 := by
    change (q /ₘ H).natDegree ≤ 1
    rw [natDegree_divByMonic q monic,deg]
    omega
  have uform : ∃ a b : K, u = C a*X+C b :=
    exists_eq_X_add_C_of_natDegree_le_one udeg
  obtain ⟨a,b,eu⟩ := uform
  have hu : I (H*u)=0 := by
    rw [eu]
    have e : H*(C a*X+C b)=a • (X*H)+b • H := by
      simp only [Polynomial.smul_eq_C_mul]
      ring
    rw [e,map_add,map_smul,map_smul]
    change a • I (X*Lagrange.nodal s v)+b • I (Lagrange.nodal s v)=0
    simp only [h0,h1,smul_zero,add_zero]
  have hq0 : q = r+H*u := (Polynomial.modByMonic_add_div q H).symm
  rw [hq0,map_add,map_add,exact_below s v I distinct r rdeg,
    multiple_zero s v I u,hu]

end RKResearch.Certified.PaidNodalQuadrature

#print axioms RKResearch.Certified.PaidNodalQuadrature.exact_two_more
