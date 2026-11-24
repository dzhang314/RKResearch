module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Compound-line witnesses for monic factor Gram norms
An actual invariant subspace gives one nonzero top exterior direction.
The Gram block is singular on that direction without any simplicity,
simultaneous diagonalization, or even splitting hypothesis. -/
namespace RKCert.Compound
open Module exteriorPower

noncomputable section
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {k : ℕ}

def topVector (v : Basis (Fin k) K V) : ⋀[K]^k V := ιMulti K k v

theorem topVector_ne_zero (v : Basis (Fin k) K V) : topVector v≠0 := by
  intro h
  have he := congrArg (alternatingMapLinearEquiv v.det) h
  exact one_ne_zero (by simpa only [topVector,alternatingMapLinearEquiv_apply_ιMulti,Basis.det_self,map_zero] using he)

/-- The top exterior action on an actual k-dimensional invariant space
is its determinant. The proof invokes alternating basis extensionality. -/
theorem topVector_map (v : Basis (Fin k) K V) (T : V →ₗ[K] V) :
    map k T (topVector v)=(LinearMap.det T) • topVector v := by
  let L : K →ₗ[K] (⋀[K]^k V) := (LinearMap.id : K→ₗ[K]K).smulRight (topVector v)
  have hL (a : K) : L a=a • topVector v := rfl
  have he : ιMulti K k = L.compAlternatingMap v.det := by
    classical
    refine Basis.ext_alternating v (fun i hi => ?_)
    let σ : Equiv.Perm (Fin k) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ιMulti K k (v ∘ σ)=L (v.det (v ∘ σ))
    rw [AlternatingMap.map_perm,AlternatingMap.map_perm,Basis.det_self,hL]
    simp only [Units.smul_def,←Int.cast_smul_eq_zsmul K,smul_eq_mul,mul_one,topVector]
  calc
    map k T (topVector v)=L (v.det (T ∘ v)) := by
      change map k T (ιMulti K k v)=_
      rw [map_apply_ιMulti,he,LinearMap.compAlternatingMap_apply]
    _ = _ := by rw [Basis.det_comp,Basis.det_self,mul_one,hL]

/-- An injected invariant k-space supplies a common exterior eigenline.
The same line works for any number of ambient/restricted operators. -/
theorem invariant_exterior_line (v : Basis (Fin k) K V) (I : V→ₗ[K]W)
    (hI : Function.Injective I) :
    ∃ z : ⋀[K]^k W, z≠0 ∧
      ∀ (T : W→ₗ[K]W) (t : V→ₗ[K]V), T.comp I=I.comp t →
        map k T z=(LinearMap.det t) • z := by
  let z := map k I (topVector v)
  have inj : Function.Injective (map k I) := map_injective_field hI
  have zne : z≠0 := fun hz => topVector_ne_zero v (inj (by simpa only [map_zero] using hz))
  refine ⟨z,zne,fun T t ht => ?_⟩
  change map k T (map k I (topVector v))=_
  rw [←LinearMap.comp_apply,←map_comp,ht,map_comp,LinearMap.comp_apply,topVector_map,map_smul]

def gramBlock (A B C : V→ₗ[K]V) : (V×V)→ₗ[K](V×V) :=
  (A.coprod B).prod (B.coprod C)

theorem gramBlock_apply (A B C : V→ₗ[K]V) (x y : V) :
    gramBlock A B C (x,y)=(A x+B y,B x+C y) := rfl

/-- A vanishing scalar Gram determinant on a common eigenline forces the
actual block operator determinant to vanish. -/
theorem gramBlock_det_zero_of_line [FiniteDimensional K V]
    (A B C : V→ₗ[K]V) {z : V} (hz : z≠0) {a b c : K}
    (ha : A z=a • z) (hb : B z=b • z) (hc : C z=c • z)
    (he : a*c-b^2=0) : LinearMap.det (gramBlock A B C)=0 := by
  have witness (x y : K) (hxy : x≠0 ∨ y≠0)
      (h₁ : x*a+y*b=0) (h₂ : x*b+y*c=0) :
      LinearMap.det (gramBlock A B C)=0 := by
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hbot
    have hw : (x • z,y • z)∈LinearMap.ker (gramBlock A B C) := by
      rw [LinearMap.mem_ker,gramBlock_apply,map_smul,map_smul,map_smul,map_smul,ha,hb,hc,
        smul_smul,smul_smul,smul_smul,smul_smul,←add_smul,←add_smul,h₁,h₂,zero_smul]
      rfl
    rw [hbot] at hw
    have heq : (x • z,y • z)=0 := by simpa using hw
    rcases hxy with h|h
    · exact hz ((smul_eq_zero.mp (congrArg Prod.fst heq)).resolve_left h)
    · exact hz ((smul_eq_zero.mp (congrArg Prod.snd heq)).resolve_left h)
  by_cases h0 : b=0
  · rw [h0,zero_pow (by decide : (2:ℕ)≠0),sub_zero] at he
    rcases mul_eq_zero.mp he with hac|hcc
    · exact witness 1 0 (Or.inl one_ne_zero) (by simp [hac]) (by simp [h0])
    · exact witness 0 1 (Or.inr one_ne_zero) (by simp [h0]) (by simp [hcc])
  · apply witness b (-a) (Or.inl h0)
    · ring
    · linear_combination -he

end
end RKCert.Compound
