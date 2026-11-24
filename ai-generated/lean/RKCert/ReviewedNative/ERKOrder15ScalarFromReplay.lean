module

public import RKCert.ReviewedNative.JacobiEndpointMass
import all RKCert.ReviewedNative.ERKOrder15MassRigidity
import RKCert.LobattoFactors
import RKCert.TableauHermiteGain
import RKCert.Dirk15ArithmeticSpecialize
import RKCert.Dirk15Replay.PairF6K4E0

@[expose] public section

/-! # Final polynomial-only adapters to the two frozen gates

Both scalar exclusions are imported as checked declarations. The old
private imports contain geometry, but no matrix, tree, or order data is
converted here. The input is the actual paid signed-Jacobi moment band;
no old mesh coefficient table or modular replay is used. -/
namespace RKCert.ReviewedNative.JacobiMoments

open Polynomial RKCert.Endpoint RKCert.Paired RKCert.FixedPolynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {a : ℕ}
variable {G P : K[X]} {u : K}

omit [CharZero K] in
private theorem remove_origin_factor {D : K[X]} (p0 : P.eval 0≠0) (h : P∣X*D) : P∣D := by
  obtain ⟨Q,eq⟩ := h
  have z := congrArg (Polynomial.eval (0:K)) eq
  simp only [eval_mul,eval_X,zero_mul] at z
  have q0 : Q.eval 0=0 := (mul_eq_zero.mp z.symm).resolve_left p0
  have qX : (X:K[X])∣Q := Polynomial.X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
  obtain ⟨R,e⟩ := qX
  refine ⟨R,mul_left_cancel₀ X_ne_zero ?_⟩
  calc
    X*D = P*Q := eq
    _ = X*(P*R) := by rw [e]; ring

private theorem alias_scalar_contradiction
    (gd : G.natDegree=7) (g0 : G.coeff 0=0)
    (mom : ∀ k≤5,(formalPrimitive (X^k*G)).eval 1=(formalPrimitive (X^(k+1)*G)).eval 1)
    (pd : P.natDegree≤4) (pf : P∣G) (un : u≠0) (gu : G.eval u=0)
    (first : (formalPrimitive (X*P)).eval u=0) : False := by
  obtain ⟨d,e⟩ := adjacent_one_mesh (m:=7) (by decide) G gd.le g0 mom
  have dn : d≠0 := fun z=>by rw [e,z,map_zero,zero_mul,natDegree_zero] at gd;omega
  have eqL : Terminal.lobatto (K:=K) 7=X*signedSlope K 7 := by
    unfold Terminal.lobatto signedSlope
    ring
  rw [←eqL] at e
  have dv : P∣Terminal.lobatto (K:=K) 7 :=
    ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr dn)).dvd_mul_left).mp (e ▸ pf)
  rw [e,eval_mul,eval_C] at gu
  apply RKCert.FixedFactor.lobatto7_first_moment dv pd un ((mul_eq_zero.mp gu).resolve_left dn)
  simpa only [formalPrimitive_eq_treePrimitive] using first

private theorem variable_scalar_contradiction
    (gd : G.natDegree=8) (g0 : G.coeff 0=0)
    (mom : ∀ k≤5,(formalPrimitive (X^k*G)).eval 1=(formalPrimitive (X^(k+1)*G)).eval 1)
    (pd : P.natDegree=4) (pf : P∣G) (p0 : P.eval 0≠0) (un : u≠0) (pu : P.eval u≠0)
    (gu : G.eval u=0) (first : (formalPrimitive (X*P)).eval u=0)
    (second : (formalPrimitive (X*(X*P))).eval u=0) : False := by
  obtain ⟨c,d,e⟩ := adjacent_two_meshes (m:=7) (by decide) G gd.le g0 mom
  have cn : c≠0 := by
    intro z
    rw [e,z,map_zero,zero_mul,zero_add] at gd
    have h := (natDegree_C_mul_le d (X*signedSlope K 7)).trans
      (x_signedSlope_degree 7 (K:=K) (by decide)).le
    omega
  let H := fieldPencil K 6 (d/c)
  have signed (n : ℕ) : signedSlope K (n+1)=fieldJacobi K n := by
    simp [signedSlope,fieldJacobi,integerJacobi]
  have q1 := signed 7
  have q2 := signed 6
  have scale : C c*C (d/c)=C d := by
    rw [←map_mul,mul_comm,div_mul_cancel₀ _ cn]
  have shape : G=C c*(X*H) := by
    rw [e,q1,q2]
    change C c*(X*fieldJacobi K 7)+C d*(X*fieldJacobi K 6)=
      C c*(X*(fieldJacobi K 7+C (d/c)*fieldJacobi K 6))
    rw [←scale]
    ring
  have rt : H.eval u=0 := by
    rw [shape,eval_mul,eval_C,eval_mul,eval_X] at gu
    exact (mul_eq_zero.mp ((mul_eq_zero.mp gu).resolve_left cn)).resolve_left un
  have dv : P∣H := remove_origin_factor p0
    (((isUnit_C.mpr (isUnit_iff_ne_zero.mpr cn)).dvd_mul_left).mp (shape ▸ pf))
  have p1 : Signature.paidMoment ((1-X)^0*P) u 1=0 := by
    simpa only [Signature.paidMoment,pow_zero,pow_one,one_mul] using first
  have p2 : Signature.paidMoment ((1-X)^0*P) u 2=0 := by
    simpa only [Signature.paidMoment,pow_zero,one_mul,pow_two,mul_assoc] using second
  have m1 := nodeMomentNorm_zero (n:=6) (k:=4) (j:=1) (w:=0) (by decide) (by decide)
    un pd rt dv pu p1
  have m2 := nodeMomentNorm_zero (n:=6) (k:=4) (j:=2) (w:=0) (by decide) (by decide)
    un pd rt dv pu p2
  have cap (j : ℕ) : (nodeMomentNorm 6 4 j 0).natDegree≤120 := by
    rw [←show momentCap 6 4 0=120 by decide]
    exact nodeMomentNorm_degree (n:=6) (k:=4) (by decide) (by decide) j 0
  exact FixedReplay.F6K4E0.no_common (cap 1) (cap 2) u m1 m2

/-- The actual marked Jacobi mesh cannot supply the degree-three or
degree-four divisor with its displayed omitted clock and paid tests. -/
theorem order15_marked_omission_impossible (alo : 6≤a) (ahi : a≤7)
    (gd : G.natDegree=a+1) (g0 : G.coeff 0=0)
    (mom : ∀ k≤5,(formalPrimitive (X^k*G)).eval 1=(formalPrimitive (X^(k+1)*G)).eval 1)
    (pd : P.natDegree+3=a) (pf : P∣G) (p0 : P.eval 0≠0)
    (un : u≠0) (pu : P.eval u≠0) (gu : G.eval u=0)
    (first : (formalPrimitive (X*P)).eval u=0)
    (second : (formalPrimitive (X*(X*P))).eval u=0) : False := by
  by_cases a6 : a=6
  · exact alias_scalar_contradiction (by omega) g0 mom (by omega) pf un gu first
  · exact variable_scalar_contradiction (by omega) g0 mom (by omega) pf p0 un pu gu first second

end
end RKCert.ReviewedNative.JacobiMoments
