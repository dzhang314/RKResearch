module

public import RKCert.ReviewedNative.JacobiMomentPorts

@[expose] public section

/-! # Tableau-free scalar obligations for the order-seventeen explicit barrier

Geometry may supply a normalized free pencil, or stop earlier at the global
moment equations for a polynomial and its small cofactor. Neither interface
contains a tableau, an order predicate, an ordered field, or replay data. -/
namespace RKCert.ReviewedNative.ERK17.Scalar
open Polynomial RKCert.Endpoint RKCert.ReviewedNative.JacobiMoments

variable {K : Type*} [Field K]
noncomputable section

/-- No origin factor or monic normalization; the parameter is unconstrained. -/
def pencil (a : K) : K[X] := signedSlope K 9 + C a * signedSlope K 8

/-- The local scalar information measured at the first nonzero active clock. -/
structure LocalPaid (P : K[X]) (u : K) : Prop where
  clock_ne : u ≠ 0
  omits : P.eval u ≠ 0
  first : (formalPrimitive (X*P)).eval u = 0
  second : (formalPrimitive (X^2*P)).eval u = 0

/-- Direct input to the degree-210 norm pair. Divisibility is polynomial
divisibility, not a collection of tests on distinct roots. -/
structure PencilPorts (P : K[X]) (a u : K) : Prop extends LocalPaid P u where
  degree : P.natDegree = 5
  root : (pencil a).eval u = 0
  divides : P ∣ pencil a

/-- Earlier input: seven moment differences at one for M = X P N. A genuine
nodal cubic is sufficient for N; any nonzero cofactor of degree at most three
works. No fixed/free pencil diagnosis is required on the geometry side. -/
structure MeshPorts (P N : K[X]) (u : K) : Prop extends LocalPaid P u where
  degree : P.natDegree ≤ 5
  cofactor_ne : N ≠ 0
  cofactor_degree : N.natDegree ≤ 3
  cofactor_root : N.eval u = 0
  mesh : MomentDifferences (P*N) 6

/-- A signed quadrature rule on the actual clocks gives the seven mesh
equations automatically. Only the nonzero clocks of nonzero-weight rows
need to lie in S. Neither positive weights nor distinct physical rows
are assumed. The formal moments in LocalPaid are at the one omitted clock. -/
theorem MeshPorts.of_quadrature [CharZero K] {ι : Type*} [Fintype ι]
    {P : K[X]} {u : K} (B : LocalPaid P u) (pd : P.natDegree ≤ 5)
    (c w : ι → K) (S : Finset K) (small : S.card ≤ 3) (member : u ∈ S)
    (cover : ∀ i, w i ≠ 0 → c i = 0 ∨ c i ∈ S)
    (rule : ∀ R : K[X], R.natDegree ≤ 10 →
      (formalPrimitive (R*((1-X)*P))).eval 1 = ∑ i, R.eval (c i)*w i) :
    MeshPorts P (nodalHull S) u := by
  classical
  let N := nodalHull S
  have nd : N.natDegree ≤ 3 := (natDegree_nodalHull S).le.trans small
  refine ⟨B,pd,(monic_nodalHull S).ne_zero,nd,nodalHull_eval_of_mem member,?_⟩
  intro k
  let R : K[X] := X^k.val*(X*N)
  have dR : R.natDegree ≤ 10 := by
    have h := natDegree_mul_le (p:=X^k.val) (q:=X*N)
    have j := natDegree_mul_le (p:=(X:K[X])) (q:=N)
    rw [natDegree_X_pow] at h
    rw [natDegree_X] at j
    have hk := k.isLt
    calc
      R.natDegree ≤ k.val + (X*N).natDegree := h
      _ ≤ 10 := by omega
  have h := rule R dR
  have zero : (∑ i, R.eval (c i)*w i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases wi : w i = 0
    · rw [wi,mul_zero]
    · rcases cover i wi with ci | ci
      · simp [R,ci]
      · simp [R,N,nodalHull_eval_of_mem ci]
  rw [zero] at h
  let M := X*(P*N)
  have res : R*((1-X)*P) = X^k.val*M - X^(k.val+1)*M := by
    dsimp [R,M]
    rw [pow_succ]
    ring
  change ((formalPrimitiveLinear (R*((1-X)*P)))).eval 1 = 0 at h
  rw [res,map_sub,eval_sub] at h
  exact sub_eq_zero.mp h

end
end RKCert.ReviewedNative.ERK17.Scalar
