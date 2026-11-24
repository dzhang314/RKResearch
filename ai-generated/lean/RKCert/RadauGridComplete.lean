module

public import RKCert.RadauGridLift
public import RKCert.DirkResultantTransfer
public import RKCert.RadauMissingRoot
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! # All eight true Radau grid ports in a splitting field
The good prime is used solely to prove separability of a fixed integer
polynomial. This gives genuine characteristic-zero cardinality of the grid. -/
namespace RKCert.FixedPolynomial.Radau77569
open Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

theorem normalized_degree : gridNormalized.natDegree=8 := by
  rw [gridNormalized,natDegree_integralNormalization,grid_degree]

theorem normalized_monic : gridNormalized.Monic :=
  monic_integralNormalization grid_ne

theorem normalized_degree_mod : (gridNormalized.map (Int.castRingHom F)).natDegree=8 := by
  rw [normalized_monic.natDegree_map,normalized_degree]

theorem normalized_derivative_degree_mod :
    (gridNormalized.derivative.map (Int.castRingHom F)).natDegree=7 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_map_le.trans ((natDegree_derivative_le _).trans_eq (by rw [normalized_degree]))
  · rw [coeff_map,coeff_derivative]
    have hc : gridNormalized.coeff (7+1)=1 := by
      change gridNormalized.coeff 8=1
      rw [←normalized_degree,coeff_natDegree,normalized_monic.leadingCoeff]
    rw [hc]
    decide

theorem normalized_no_common_root (u : K) :
    (gridNormalized.map (Int.castRingHom K)).eval u≠0 ∨
      (gridNormalized.derivative.map (Int.castRingHom K)).eval u≠0 := by
  apply no_common_eval_of_good_prime gridNormalized gridNormalized.derivative 8 7
    normalized_degree.le (by simpa only [normalized_degree] using natDegree_derivative_le gridNormalized)
    normalized_degree_mod normalized_derivative_degree_mod (Or.inl (by decide)) scaled_grid_good

theorem normalized_separable [IsAlgClosed K] :
    (gridNormalized.map (Int.castRingHom K)).Separable := by
  rw [Separable,derivative_map]
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr
  intro a
  simpa only [coe_aeval_eq_eval] using normalized_no_common_root a

/-- Every root of the normalized integral grid corresponds to a genuine
unscaled Radau port. -/
theorem port_of_normalized_root {a : K}
    (ha : (gridNormalized.map (Int.castRingHom K)).eval a=0) :
    RKCert.Paired.IsLeftRadauPort (a/((-51480:ℤ):K)) := by
  let l : K := ((-51480:ℤ):K)
  have ln : l≠0 := by norm_num [l]
  have e := integralNormalization_eval₂_leadingCoeff_mul
    (p:=gridInt) (by rw [grid_degree]; decide) (Int.castRingHom K) (a/l)
  change (_ : K)=_ at e
  rw [grid_leading,grid_degree] at e
  change gridNormalized.eval₂ (Int.castRingHom K) (l*(a/l))=
    l^(8-1)*gridInt.eval₂ (Int.castRingHom K) (a/l) at e
  rw [←Polynomial.eval_map,show l*(a/l)=a by field_simp,ha] at e
  have root : gridInt.eval₂ (Int.castRingHom K) (a/l)=0 :=
    (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ ln)
  rw [gridInt,eval₂_mul,eval₂_X,←Polynomial.eval_map,map_reproducer] at root
  exact mul_eq_zero.mp root

theorem exists_eight_ports [IsAlgClosed K] :
    ∃ S : Finset K, S.card=8 ∧ ∀ a∈S,RKCert.Paired.IsLeftRadauPort a := by
  classical
  let P := gridNormalized.map (Int.castRingHom K)
  let l : K := ((-51480:ℤ):K)
  have ln : l≠0 := by norm_num [l]
  have idiv : Function.Injective (fun x : K => x/l) := fun x y e => by
    have h := congrArg (fun z : K => z*l) e
    change (x/l)*l=(y/l)*l at h
    simpa only [div_mul_cancel₀ _ ln] using h
  have d : P.natDegree=8 := by
    change (gridNormalized.map _).natDegree=8
    rw [normalized_monic.natDegree_map,normalized_degree]
  have pm : P.Monic := normalized_monic.map _
  have ps : P.Separable := normalized_separable
  have split : P.Splits := IsAlgClosed.splits P
  refine ⟨P.roots.toFinset.image (fun x => x/l),?_,?_⟩
  · rw [Finset.card_image_of_injective _ idiv,Multiset.toFinset_card_of_nodup (nodup_roots ps),
      ←split.natDegree_eq_card_roots,d]
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact port_of_normalized_root
      ((mem_roots pm.ne_zero).mp (Multiset.mem_toFinset.mp ha))

end
end RKCert.FixedPolynomial.Radau77569
