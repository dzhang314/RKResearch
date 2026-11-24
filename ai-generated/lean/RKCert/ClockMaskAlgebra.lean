module

public import RKCert.DiagonalHead

@[expose] public section

/-! # Physical classes of a nonunital coordinatewise algebra

Construct a true indicator without finding a generic vector or ordering
the coefficient field. It is enough to separate the fixed active stage
from one other class at a time, multiply the factors, and keep one 
nonzero vector of the algebra as the initial factor. -/
namespace RKCert.Paired.ClockClass

variable {K : Type*} [Field K] {s : ℕ}
variable {U : Submodule K (Vec K s)}

def SameClass (U : Submodule K (Vec K s)) (i j : Fin s) : Prop :=
  ∀ v ∈ U, v i=v j

def Active (U : Submodule K (Vec K s)) (i : Fin s) : Prop :=
  ∃ v ∈ U, v i≠0

noncomputable def classIndicator (U : Submodule K (Vec K s)) (i : Fin s) : Vec K s :=
  by classical exact fun j => if SameClass U i j then 1 else 0

theorem classIndicator_at (U : Submodule K (Vec K s)) (i j : Fin s) :
    classIndicator U i j = (by classical exact if SameClass U i j then 1 else 0) := rfl

theorem SameClass.refl (U : Submodule K (Vec K s)) (i : Fin s) : SameClass U i i :=
  fun _ _ => rfl

theorem SameClass.symm {i j : Fin s} (h : SameClass U i j) : SameClass U j i :=
  fun v hv => (h v hv).symm

theorem SameClass.trans {i j k : Fin s} (h₁ : SameClass U i j) (h₂ : SameClass U j k) :
    SameClass U i k := fun v hv => (h₁ v hv).trans (h₂ v hv)

theorem sameClass_active {i j : Fin s} (h : SameClass U i j) :
    Active U i ↔ Active U j :=
  ⟨fun ⟨v,hv,hn⟩ => ⟨v,hv,by rwa [←h v hv]⟩,
    fun ⟨v,hv,hn⟩ => ⟨v,hv,by rwa [h v hv]⟩⟩

theorem sameClass_clock {c : Vec K s} {i j : Fin s} (hC : U.map (diag c)≤U)
    (h : SameClass U i j) (hi : Active U i) : c i=c j := by
  obtain ⟨v,hv,hn⟩ := hi
  have hcv := h (diag c v) (hC (Submodule.mem_map_of_mem hv))
  simp only [diag_apply,←h v hv] at hcv
  exact mul_right_cancel₀ hn hcv

/-- Each single active joint-value class already has an indicator in the
original algebra. In particular it need not be adjoined or paid for again. -/
theorem classIndicator_mem (hmul : ∀ u∈U, ∀ v∈U, u*v∈U)
    (i : Fin s) (hi : Active U i) : classIndicator U i∈U := by
  classical
  obtain ⟨u,hu,hui⟩ := hi
  let T : Finset (Fin s) := Finset.univ.filter (fun j => ¬SameClass U i j)
  have separate (j : Fin s) : ∃ v∈U, j∈T → v i≠v j := by
    by_cases hj : j∈T
    · have hn := (Finset.mem_filter.mp hj).2
      unfold SameClass at hn
      push Not at hn
      obtain ⟨v,hv,hij⟩ := hn
      exact ⟨v,hv,fun _ => hij⟩
    · exact ⟨0,U.zero_mem,fun h => (hj h).elim⟩
  choose v hv hSep using separate
  let factor (j : Fin s) : Vec K s := fun k => (v j k-v j j)/(v j i-v j j)
  have factor_mul_mem (j : Fin s) {x : Vec K s} (hx : x∈U) : x*factor j∈U := by
    have he : x*factor j = (v j i-v j j)⁻¹ • (x*v j - v j j • x) := by
      ext k
      simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,factor,div_eq_mul_inv]
      ring
    rw [he]
    exact U.smul_mem _ (U.sub_mem (hmul _ hx _ (hv j)) (U.smul_mem _ hx))
  let u₀ : Vec K s := (u i)⁻¹ • u
  have prod_mem (S : Finset (Fin s)) : u₀ * (∏ j ∈ S, factor j)∈U := by
    induction S using Finset.induction_on with
    | empty => simpa [u₀] using U.smul_mem (u i)⁻¹ hu
    | @insert j S hj ih =>
      rw [Finset.prod_insert hj]
      simpa only [mul_left_comm, mul_assoc, mul_comm] using factor_mul_mem j ih
  convert prod_mem T using 1
  ext k
  rw [classIndicator_at,Pi.mul_apply,Finset.prod_apply]
  by_cases hk : SameClass U i k
  · have hprod : ∏ j ∈ T, factor j k = 1 :=
      Finset.prod_eq_one (fun j hj => by
        simp only [factor,←hk _ (hv j)]
        exact div_self (sub_ne_zero.mpr (hSep j hj)))
    simp [hk,hprod,u₀,←hk u hu,hui]
  · have hkT : k∈T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
    have hzero : ∏ j ∈ T, factor j k = 0 :=
      Finset.prod_eq_zero hkT (by simp [factor])
    simp [hk,hzero]

theorem class_is_disjoint_of_not_same {i j : Fin s} (h : ¬SameClass U i j) :
    classIndicator U i * classIndicator U j = 0 := by
  classical
  ext k
  by_cases a : SameClass U i k
  · have b : ¬SameClass U j k := fun b => h (a.trans b.symm)
    simp [classIndicator_at,a,b]
  · simp [classIndicator_at,a]

end RKCert.Paired.ClockClass
