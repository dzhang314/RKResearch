module
public import RKCert.StagePrimitives
public import RKCert.CoreSupport
public import Mathlib.RingTheory.Polynomial.Basic
public import RKCert.CauchyKnots

@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired RKCert.Paired.Clock Module Polynomial
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}

/-- Physically permissible head multipliers on the full chronological prefix,
including all equal-clock collisions, nonzero-headed zero clocks, and masked
classes with different head values. This is one *fixed* linear subspace;
increasing the scalar degree by one cannot add more than one dimension. -/
def compatible (c w : Vec K s) (U : Submodule K (Vec K s)) (i : Fin s) : Submodule K (Polynomial K) where
  carrier := {Q | ∃ F : K→K, F 0=0 ∧ ∃ u∈U, ∀ l < i, w l * Q.eval (c l)=u l+F (c l)}
  zero_mem' := ⟨0,rfl,0,U.zero_mem,by simp⟩
  add_mem' := by
    rintro P Q ⟨F,hF,u,hu,hp⟩ ⟨G,hG,v,hv,hq⟩
    refine ⟨F+G,by simp [hF,hG],u+v,U.add_mem hu hv,?_⟩
    intro l hl; simp only [eval_add,mul_add,hp l hl,hq l hl,Pi.add_apply]; ring
  smul_mem' := by
    rintro a P ⟨F,hF,u,hu,hp⟩
    refine ⟨a • F,by simp [hF],a • u,U.smul_mem a hu,?_⟩
    intro l hl
    simp only [Polynomial.eval_smul,Pi.smul_apply,smul_eq_mul]
    rw [←mul_assoc,mul_comm (w l) a,mul_assoc,hp l hl,mul_add]

/-- The one-step dimension charge needed for the simultaneous input and
primitive-output cuts; valid for arbitrary linear compatibility constraints. -/
theorem degree_charge (H : Submodule K (Polynomial K)) (r : ℕ) :
    finrank K (H ⊓ degreeLT K (r+1) : Submodule K (Polynomial K))
      ≤ finrank K (H ⊓ degreeLT K r : Submodule K (Polynomial K))+1 := by
  let W := H ⊓ degreeLT K (r+1)
  let D := degreeLT K r
  let D' := degreeLT K (r+1)
  have dim (n : ℕ) : finrank K (degreeLT K n)=n := by
    rw [(degreeLTEquiv K n).finrank_eq,Module.finrank_fin_fun]
  have hWW : W≤D' := inf_le_right
  let : FiniteDimensional K D := Module.Finite.equiv (degreeLTEquiv K r).symm
  let : FiniteDimensional K D' := Module.Finite.equiv (degreeLTEquiv K (r+1)).symm
  let : FiniteDimensional K W := Module.Finite.of_injective (Submodule.inclusion hWW)
    (Submodule.inclusion_injective hWW)
  have le : W ⊔ D ≤ D' := sup_le hWW (degreeLT_mono (by omega : r≤r+1))
  have gr := W.finrank_sup_add_finrank_inf_eq D
  have eqn : W ⊓ D = H ⊓ D := by
    dsimp [W,D]
    rw [inf_assoc,inf_eq_right.mpr (degreeLT_mono (by omega : r≤r+1))]
  rw [eqn] at gr
  have rank := Submodule.finrank_mono le
  change finrank K W≤finrank K (H⊓D : Submodule K (Polynomial K))+1
  have dr : finrank K D=r := dim r
  have dr' : finrank K D'=r+1 := dim (r+1)
  omega

/-- A true paired chronological kernel from a one-dimensional compatibility
charge. It proves simultaneous nonzero input and zero primitive observations
even if no fixed list of collision sites was ever computed. -/
theorem paired_kernel {V W X Z : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z] {m : ℕ}
    (L : (V×W)→ₗ[K](Fin m→K)) (G : V→ₗ[K]Z) (D : X→ₗ[K]Z)
    (big : m+2≤finrank K V) (step : finrank K X≤finrank K W+1)
    (map : ∀ v w, L (v,w)=0 → G v∈LinearMap.range D)
    (inj : ∀ w, L (0,w)=0 → w=0) :
    ∃ v w, v≠0 ∧ L (v,w)=0 ∧ G v=0 := by
  let B := (G.comp (LinearMap.fst K V W)).domRestrict (LinearMap.ker L)
  have ra : LinearMap.range B ≤ LinearMap.range D := by
    rintro _ ⟨vw,rfl⟩
    exact map _ _ vw.property
  have h0 := L.finrank_range_add_finrank_ker
  rw [Module.finrank_prod] at h0
  have h1 := B.finrank_range_add_finrank_ker
  have h2 := D.finrank_range_le
  have h3 := Submodule.finrank_mono ra
  have h4 := (LinearMap.range L).finrank_le
  rw [Module.finrank_fin_fun] at h4
  have hpos : 0<finrank K (LinearMap.ker B) := by omega
  obtain ⟨vw,hvw,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.mp hpos)
  refine ⟨vw.val.1,vw.val.2,?_,vw.property,hvw⟩
  intro h
  have hz : vw.val.2=0 := inj _ (by rw [←h]; exact vw.property)
  exact hn (Subtype.ext (Prod.ext h hz))

end RKCert.FourDebut
