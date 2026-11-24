module

public import RKCert.CompanionFactorLine
public import RKCert.Dirk15SignatureAlgebra
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! # Actual factor moment operators on a common exterior line

The operator is specified by polynomial interpolation of the exterior
companion at fixed distinct auxiliary sites. An actual monic factor
supplies its factor evaluation, hence each integrated moment, as
eigenvalues on the same line even at repeated roots. Nothing here asserts
the nonzero resultant of a specified free Jacobi pencil.
-/
namespace RKCert.Compound
open Polynomial exteriorPower RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def paidMomentLinear (u : K) (j : ℕ) : K[X] →ₗ[K] K :=
  ((leval u).comp formalPrimitiveLinear).comp (LinearMap.mulLeft K (X^j))

@[simp] theorem paidMomentLinear_apply (u : K) (j : ℕ) (P : K[X]) :
    paidMomentLinear u j P=paidMoment P u j := rfl

def factorSites (K : Type*) [Field K] (k : ℕ) : Fin (k+1) → K := fun i => i.val

theorem factorSites_injective (k : ℕ) : Function.Injective (factorSites K k) := by
  intro i j e
  exact Fin.ext (Nat.cast_injective (R:=K) e)

def factorMomentOperator (D : K[X]) (k : ℕ) (u : K) (j : ℕ) :
    (⋀[K]^k (AdjoinRoot D)) →ₗ[K] (⋀[K]^k (AdjoinRoot D)) :=
  ∑ i : Fin (k+1),
    (paidMomentLinear u j (Lagrange.basis Finset.univ (factorSites K k) i)) •
      exteriorPower.map k (shiftedRootOperator D (factorSites K k i))

theorem paidMoment_interpolation (G : K[X]) (u : K) (j : ℕ) :
    (∑ i : Fin (G.natDegree+1),
      paidMomentLinear u j (Lagrange.basis Finset.univ (factorSites K G.natDegree) i) *
        G.eval (factorSites K G.natDegree i))=paidMoment G u j := by
  let k := G.natDegree
  let f := factorSites K k
  have R : G=Lagrange.interpolate Finset.univ f (fun i => G.eval (f i)) :=
    Lagrange.eq_interpolate (factorSites_injective k).injOn (by
      apply G.degree_le_natDegree.trans_lt
      simp only [Finset.card_univ,Fintype.card_fin]
      exact_mod_cast (Nat.lt_succ_self k))
  have e := congrArg (paidMomentLinear u j) R
  rw [Lagrange.interpolate_apply,map_sum] at e
  simp_rw [←smul_eq_C_mul,map_smul,smul_eq_mul,mul_comm (G.eval _)] at e
  exact e.symm

theorem factor_paid_moment_eigenline (F G : K[X]) (hF : F≠0) (hG : G.Monic) :
    ∃ z : ⋀[K]^G.natDegree (AdjoinRoot (F*G)),z≠0 ∧
      ∀ u : K,∀ j : ℕ,
        factorMomentOperator (F*G) G.natDegree u j z=(paidMoment G u j) • z := by
  obtain ⟨z,nz,eigen⟩ := polynomial_factor_exterior_line F G hF hG
  refine ⟨z,nz,fun u j => ?_⟩
  simp only [factorMomentOperator,LinearMap.sum_apply,LinearMap.smul_apply,eigen,smul_smul]
  rw [←Finset.sum_smul,paidMoment_interpolation]

theorem factor_paid_moment_det_zero (F G : K[X]) (hF : F≠0) (hG : G.Monic)
    (u : K) (j : ℕ) (zero : paidMoment G u j=0) :
    LinearMap.det (factorMomentOperator (F*G) G.natDegree u j)=0 := by
  let : Module.Finite K (AdjoinRoot (F*G)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (mul_ne_zero hF hG.ne_zero)).basis
  obtain ⟨z,nz,eigen⟩ := factor_paid_moment_eigenline F G hF hG
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro e
  apply nz
  have zker : z∈LinearMap.ker (factorMomentOperator (F*G) G.natDegree u j) := by
    rw [LinearMap.mem_ker,eigen,zero,zero_smul]
  rwa [e,Submodule.mem_bot] at zker

theorem factor_paid_gram_det_zero (F G : K[X]) (hF : F≠0) (hG : G.Monic)
    (u : K) (j : ℕ)
    (zero : paidMoment G u j *paidMoment G u (j+2) -(paidMoment G u (j+1))^2=0) :
    LinearMap.det (gramBlock (factorMomentOperator (F*G) G.natDegree u j)
      (factorMomentOperator (F*G) G.natDegree u (j+1))
      (factorMomentOperator (F*G) G.natDegree u (j+2)))=0 := by
  let : Module.Finite K (AdjoinRoot (F*G)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (mul_ne_zero hF hG.ne_zero)).basis
  obtain ⟨z,nz,eigen⟩ := factor_paid_moment_eigenline F G hF hG
  exact gramBlock_det_zero_of_line _ _ _ nz (eigen u j) (eigen u (j+1)) (eigen u (j+2)) zero

end
end RKCert.Compound
