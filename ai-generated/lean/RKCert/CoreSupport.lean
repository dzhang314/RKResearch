module
public import RKCert.HeadChart

@[expose] public section
namespace RKCert.Paired.Clock
open RKCert.Paired RKCert.OneEscape Module
variable {K : Type*} [Field K] {s : ℕ} {c w : Vec K s} {U : Submodule K (Vec K s)}

/-- Nonunital coordinatewise subalgebra, recorded without new operations. -/
def MulClosed (U : Submodule K (Vec K s)) : Prop := ∀ u∈U, ∀ v∈U, u*v∈U
/-- Visible at a physical row; this is not merely nonzero output mass. -/
def Live (U : Submodule K (Vec K s)) (i : Fin s) : Prop := ∃ v∈U, v i≠0

/-- Each single column's physical support indicator belongs to the actual
multiplicatively closed submodule. Uses interpolation of 1/x at existing
nonzero values, never requiring the unit of the full product algebra. -/
theorem vector_indicator (hU : MulClosed U) {v : Vec K s} (hv : v∈U) :
    ∃ e∈U, ∀ i, e i=(by classical exact if v i=0 then 0 else 1) := by
  classical
  let P := Lagrange.interpolate (sites v) id (fun z:K => z⁻¹)
  have co : U.map (diag v) ≤ U := by
    rintro _ ⟨u,hu,rfl⟩
    exact hU v hv u hu
  refine ⟨_,poly_preserves co P v hv,?_⟩
  intro i
  have eh : P.eval (v i)=(v i)⁻¹ :=
    Lagrange.eval_interpolate_at_node (fun z:K => z⁻¹) (Set.injOn_id _) (site_mem v i)
  rw [eh]
  by_cases h : v i=0 <;> simp [h]

/-- The union of all active physical coordinates of U has its indicator in U.
This works over every field, finite or infinite, and does not choose a
supposedly generic linear combination or require 1 ∈ U. -/
theorem core_indicator (hU : MulClosed U) :
    ∃ e∈U, ∀ i, e i=(by classical exact if Live U i then 1 else 0) := by
  classical
  have step (S : Finset (Fin s)) :
      ∃ e∈U, ∀ i∈S, Live U i → e i=1 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0,U.zero_mem,by simp⟩
    | @insert i S _ ih =>
      obtain ⟨e,he,ok⟩ := ih
      by_cases hi : Live U i
      · obtain ⟨v,hv,vi⟩ := hi
        obtain ⟨d,hd,dd⟩ := vector_indicator hU hv
        refine ⟨e+d-e*d,U.sub_mem (U.add_mem he hd) (hU e he d hd),?_⟩
        intro t ht hl
        rcases Finset.mem_insert.mp ht with rfl | ht
        · simp [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,dd,vi]
        · simp [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,ok _ ht hl]
      · refine ⟨e,he,?_⟩
        intro t ht hl
        rcases Finset.mem_insert.mp ht with rfl|ht
        · contradiction
        · exact ok _ ht hl
  obtain ⟨e,he,ok⟩ := step Finset.univ
  refine ⟨e,he,fun i => ?_⟩
  by_cases h : Live U i
  · simp [h,ok _ (Finset.mem_univ _) h]
  · have z : e i=0 := by
      by_contra hn
      exact h ⟨e,he,hn⟩
    simp [h,z]

/-- A representative may be chosen zero at *every physical row* supporting
the invariant algebra, without removing any row from the tableau. -/
theorem disjoint_head (hT : U.map (diag c)≤U) (hU : MulClosed U)
    (hkeep : ∀ u∈U, u*w∈U) :
    ∃ v : Vec K s, w-v∈U ∧ (∀ i, Live U i → v i=0) ∧
      ∀ n, chain (diag c) U v n=chain (diag c) U w n := by
  classical
  obtain ⟨e,he,ee⟩ := core_indicator hU
  have h := hkeep e he
  refine ⟨w-e*w,?_,?_,fun n=>chain_sub_head hT h n⟩
  · simpa only [sub_sub_cancel] using h
  · intro i hi
    simp [Pi.sub_apply,Pi.mul_apply,ee,hi]


/-- A multiplier that acts on a length-d complete band has polynomial values
on the physical head of degree below n-d. This is a generic projection lemma:
the multiplier need not be a head, a pure, or a scalar clock. -/
theorem multiplier_degree {a : Vec K s} {n d : ℕ}
    (disjoint : ∀ i, Live U i → w i=0) (count : n<(headSites c w).card)
    (band : ∀ k≤d,(diag c^k) (a*w) ∈ chain (diag c) U w n) :
    ∃ P : Polynomial K, (P=0 ∨ P.natDegree+d<n) ∧
      (∀ i, w i≠0 → a i=P.eval (c i)) := by
  classical
  have get (k : ℕ) (hk : k≤d) : ∃ Q : Polynomial K, Q.degree<(n:WithBot ℕ) ∧
      ∀ i, w i≠0 → Q.eval (c i)=(c i)^k * a i := by
    obtain ⟨u,hu,Q,deg,eqn⟩ := exists_head_poly (band k hk)
    refine ⟨Q,deg,fun i hi => ?_⟩
    have zu : u i=0 := by
      by_contra h
      exact hi (disjoint i ⟨u,hu,h⟩)
    have eq := eqn i
    rw [pow_diag_apply,Pi.mul_apply,zu,zero_add,←mul_assoc] at eq
    exact mul_right_cancel₀ hi eq.symm
  obtain ⟨P,hd,values⟩ := get 0 (by omega)
  have hp (i : Fin s) (hi : w i≠0) : P.eval (c i)=a i := by
    simpa only [pow_zero,one_mul] using values i hi
  have high (Q : Polynomial K) (hq : Q.degree<(n:WithBot ℕ)) :
      (Polynomial.X*Q).degree < ((headSites c w).card:WithBot ℕ) := by
    by_cases e : Q=0
    · simp [e]
    · have h := (Polynomial.natDegree_lt_iff_degree_lt e).mpr hq
      apply (Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero Polynomial.X_ne_zero e)).mp
      rw [Polynomial.natDegree_X_mul e]
      omega
  have powers (k : ℕ) (hk : k≤d) : (Polynomial.X^k*P).degree < (n:WithBot ℕ) := by
    induction k with
    | zero => simpa only [pow_zero,one_mul] using hd
    | succ k ih =>
      obtain ⟨Q,hq,he⟩ := get (k+1) hk
      have e : Q=Polynomial.X*(Polynomial.X^k*P) := by
        apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (headSites c w)
          (hq.trans (by exact_mod_cast count)) (high _ (ih (by omega)))
        intro z hz
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
        have hi' : w i≠0 := (Finset.mem_filter.mp hi).2
        rw [he i hi',Polynomial.eval_mul,Polynomial.eval_mul,
          Polynomial.eval_pow,Polynomial.eval_X,hp i hi',pow_succ']
        ring
      rw [pow_succ',mul_assoc,←e]
      exact hq
  refine ⟨P,?_,fun i hi => (hp i hi).symm⟩
  by_cases e : P=0
  · exact Or.inl e
  · right
    have z := (Polynomial.natDegree_lt_iff_degree_lt
      (mul_ne_zero (pow_ne_zero d Polynomial.X_ne_zero) e)).mpr (powers d le_rfl)
    simpa only [Polynomial.natDegree_X_pow_mul d e] using z

end RKCert.Paired.Clock
