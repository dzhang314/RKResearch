module

public import RKCert.CompoundEigenline
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

/-! # An actual repeated-factor line in the companion quotient
Embedding is multiplication by the complementary factor on the
polynomial quotient. No ordering or distinctness of roots is needed. -/
namespace RKCert.Compound
open Polynomial Module

noncomputable section

variable {K : Type*} [Field K]
variable (F G : K[X])

def factorEmbedding : AdjoinRoot G →ₗ[K] AdjoinRoot (F*G) :=
  ((Ideal.span ({G}:Set K[X])).restrictScalars K).liftQ
    ((AdjoinRoot.mkₐ (F*G)).toLinearMap.comp (LinearMap.mulLeft K F))
    (by
      intro Q hQ
      apply LinearMap.mem_ker.mpr
      change AdjoinRoot.mk (F*G) (F*Q)=0
      rw [AdjoinRoot.mk_eq_zero]
      obtain ⟨X,hX⟩ := Ideal.mem_span_singleton.mp hQ
      exact ⟨X,by rw [hX,mul_assoc]⟩)

theorem factorEmbedding_mk (P : K[X]) :
    factorEmbedding F G (AdjoinRoot.mk G P)=AdjoinRoot.mk (F*G) (F*P) :=
  rfl

theorem factorEmbedding_inj (hF : F≠0) : Function.Injective (factorEmbedding F G) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  induction w using AdjoinRoot.induction_on with
  | ih Q =>
    rw [factorEmbedding_mk,AdjoinRoot.mk_eq_zero] at hw
    rw [AdjoinRoot.mk_eq_zero]
    obtain ⟨T,e⟩ := hw
    exact ⟨T,mul_left_cancel₀ hF (by simpa only [mul_assoc] using e)⟩

def shiftedRootOperator (F : K[X]) (u : K) : AdjoinRoot F →ₗ[K] AdjoinRoot F :=
  LinearMap.mulLeft K (algebraMap K (AdjoinRoot F) u-AdjoinRoot.root F)

theorem factorEmbedding_intertwines (u : K) :
    (shiftedRootOperator (F*G) u).comp (factorEmbedding F G) =
      (factorEmbedding F G).comp (shiftedRootOperator G u) := by
  ext w
  induction w using AdjoinRoot.induction_on with
  | ih Q =>
    rw [LinearMap.comp_apply,LinearMap.comp_apply,factorEmbedding_mk]
    change (algebraMap K (AdjoinRoot (F*G)) u-AdjoinRoot.root (F*G)) *
      AdjoinRoot.mk (F*G) (F*Q) =
        factorEmbedding F G ((algebraMap K (AdjoinRoot G) u-AdjoinRoot.root G) * AdjoinRoot.mk G Q)
    have e (P : K[X]) :
        (algebraMap K (AdjoinRoot P) u-AdjoinRoot.root P)=AdjoinRoot.mk P (C u-X) := by
      rw [map_sub,AdjoinRoot.mk_X,AdjoinRoot.mk_C]
      rfl
    rw [e (F*G),e G,←map_mul,←map_mul,factorEmbedding_mk]
    congr 1
    ac_rfl

theorem minpoly_root_of_monic (hG : G.Monic) : minpoly K (AdjoinRoot.root G)=G := by
  symm
  apply minpoly.unique' K (AdjoinRoot.root G) hG (by rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self])
  intro Q hQ
  by_cases e : Q=0
  · exact Or.inl e
  right
  intro h
  rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_eq_zero] at h
  exact not_le_of_gt hQ (degree_le_of_dvd h e)

theorem shiftedRootOperator_det (hG : G.Monic) (u : K) :
    LinearMap.det (shiftedRootOperator G u)=G.eval u := by
  let B := AdjoinRoot.powerBasis' hG
  have eM : (Algebra.leftMulMatrix B.basis (AdjoinRoot.root G)).charpoly=G := by
    have e := charpoly_leftMulMatrix B
    change (Algebra.leftMulMatrix B.basis (AdjoinRoot.root G)).charpoly=
      minpoly K (AdjoinRoot.root G) at e
    exact e.trans (minpoly_root_of_monic G hG)
  calc
    LinearMap.det (shiftedRootOperator G u) =
        (Algebra.leftMulMatrix B.basis (AdjoinRoot.root G)).charpoly.eval u := by
      rw [Matrix.eval_charpoly,←LinearMap.det_toMatrix B.basis (shiftedRootOperator G u)]
      change (LinearMap.toMatrix B.basis B.basis (LinearMap.mulLeft K
        (algebraMap K (AdjoinRoot G) u-AdjoinRoot.root G))).det=_
      rw [Algebra.toMatrix_lmul_eq,map_sub,AlgHom.commutes]
      rfl
    _ = _ := congrArg (Polynomial.eval u) eM

/-- Every actual monic factor supplies a line on which each exterior
shifted companion acts by that factor's evaluation, even if the factors
have repeated roots or neither polynomial splits. -/
theorem polynomial_factor_exterior_line (hF : F≠0) (hG : G.Monic) :
    ∃ z : ⋀[K]^G.natDegree (AdjoinRoot (F*G)), z≠0 ∧
      ∀ u : K, exteriorPower.map G.natDegree (shiftedRootOperator (F*G) u) z =
        (G.eval u) • z := by
  obtain ⟨z,hz,h⟩ := invariant_exterior_line (AdjoinRoot.powerBasis' hG).basis
    (factorEmbedding F G) (factorEmbedding_inj F G hF)
  refine ⟨z,hz,fun u => ?_⟩
  exact (h _ _ (factorEmbedding_intertwines F G u)).trans (by
    rw [shiftedRootOperator_det G hG]; rfl)

end
end RKCert.Compound
