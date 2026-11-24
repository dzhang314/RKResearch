module

public import RKCert.NodalPrimitive
public import RKCert.EndpointPhysical

@[expose] public section

/-! # Genuine formal primitives at the two physical endpoints

Only a polynomial-to-coefficient normalization is performed here.
The scalar elimination is the reviewed two-endpoint identity, not
a repeated arithmetic certificate or a tree-order conversion. -/
namespace RKCert.EndpointPhysical
open Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

private theorem formalPrimitiveLinear_monomial (j : ℕ) (a : K) :
    formalPrimitiveLinear (monomial j a)=monomial (j+1) (a/((j+1:ℕ):K)) := by
  classical
  by_cases h : a=0
  · simp [h]
  · change formalPrimitive (monomial j a)=_
    simp [formalPrimitive,support_monomial j h]

theorem formalPrimitive_moment [DecidableEq K] (e : Fin n→K) (x : K) (k : ℕ) :
    (formalPrimitive (X^k*ofFn n e)).eval x=moment e x k := by
  classical
  change (formalPrimitiveLinear (X^k*ofFn n e)).eval x=_
  rw [ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum,moment]
  apply Finset.sum_congr rfl
  intro t _
  rw [X_pow_mul_monomial,formalPrimitiveLinear_monomial,eval_monomial]
  ring

/-- These are the exact three-plus-two primitive windows. The first
filter X excludes the origin; the second filter X(X-u) also excludes
the previous physical endpoint. -/
def primitiveTests (P : K[X]) (u v : K) : Prop :=
  (∀ R : K[X], R.natDegree≤2 → (formalPrimitive (R*(X*P))).eval u=0) ∧
  (∀ R : K[X], R.natDegree≤1 → (formalPrimitive (R*(X*(X-C u)*P))).eval v=0)

theorem tests_of_primitives [DecidableEq K] {P : K[X]} {u v : K} (h : primitiveTests P u v)
    (e : Fin n→K) (eq : ofFn n e=P) : tests e u v 3 := by
  have fm (x : K) (k : ℕ) := formalPrimitive_moment e x k
  simp only [eq] at fm
  have first (k : Fin 3) : moment e u (k.val+1)=0 := by
    have z := h.1 (X^k.val) (by rw [natDegree_X_pow]; omega)
    rw [←mul_assoc,←pow_succ,fm] at z
    exact z
  have second (k : ℕ) (hk : k≤1) : moment e v (k+2)-u*moment e v (k+1)=0 := by
    have z := h.2 (X^k) (by rwa [natDegree_X_pow])
    have p : X^k*(X*(X-C u)*P)=X^(k+2)*P-u • (X^(k+1)*P) := by
      rw [←C_mul',pow_succ X (k+1),pow_succ X k]
      ring
    change (formalPrimitiveLinear (X^k*(X*(X-C u)*P))).eval v=0 at z
    rw [p,map_sub,map_smul,eval_sub,eval_smul] at z
    exact (fm v (k+2)).symm ▸ (fm v (k+1)).symm ▸ z
  exact ⟨first,second 0 (by decide),second 1 (by decide)⟩

/-- The same physical cubic gate over any characteristic-zero field. -/
theorem cubic_eq_zero_of_primitives {P : K[X]} {u v : K} (degree : P.natDegree≤3)
    (hu : u≠0) (hv : v≠0) (hne : v≠u) (h : primitiveTests P u v) : P=0 := by
  classical
  let e : Fin 4 → K := fun i => P.coeff i.val
  have eq : ofFn 4 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have z := (rescale_eq_zero_iff e hu).mp (match3 _ _ (div_ne_zero hv hu)
    (fun h => hne ((div_eq_one_iff_eq hu).mp h)) (normalize hu (tests_of_primitives h e eq)))
  rw [←eq,z,map_zero]

/-- The identical cutoff also serves a quartic when an ordered field and
the extra grade of physical payment are available. -/
theorem ordered_quartic_eq_zero_of_primitives {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {P : F[X]} {u v : F} (degree : P.natDegree≤4)
    (hu : u≠0) (hv : v≠0) (hne : v≠u) (h : primitiveTests P u v) : P=0 := by
  classical
  let e : Fin 5 → F := fun i => P.coeff i.val
  have eq : ofFn 5 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have z := (rescale_eq_zero_iff e hu).mp (ordered_quartic_three_two _ _ (div_ne_zero hv hu)
    (fun h => hne ((div_eq_one_iff_eq hu).mp h)) (normalize hu (tests_of_primitives h e eq)))
  rw [←eq,z,map_zero]

end RKCert.EndpointPhysical
