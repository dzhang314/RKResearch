module

public import RKCert.ReviewedNative.ClockHeadFibers

@[expose] public section

/-! # A physical head away from the live coordinates of its core -/
namespace RKResearch.Certified.Graded.HeadFiber

open RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical Matrix
variable {K : Type*} [Field K] {s n d : ℕ} {c w x a : Fin s → K}
variable {U : Submodule K (Fin s → K)}

noncomputable def physicalSites (c w : Fin s → K) : Finset K := by
  classical exact (Finset.univ.filter (fun i => w i ≠ 0)).image c

theorem escape_le_physical : escapeSites c w U ⊆ physicalSites c w := by
  classical
  intro z hz
  by_contra no
  apply (Finset.mem_filter.mp hz).2
  have empty : blockMask c z w = 0 := by
    ext i
    by_cases h : c i = z
    · have zero : w i=0 := by
        by_contra nz
        exact no (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nz⟩,h⟩)
      simp [blockMask,h,zero]
    · simp [blockMask,h]
  exact empty ▸ U.zero_mem

private theorem shift (stable : U.map (diag c)≤U) {u : Fin s → K} (hu : u∈U) :
    ∀ n, chain (diag c) U (w-u) n = chain (diag c) U w n := by
  intro n
  have h₁ := (clock_chain_le_iff (T:=diag c) (U:=U) (w:=w) n).mp le_rfl
  have h₂ := (clock_chain_le_iff (T:=diag c) (U:=U) (w:=w-u) n).mp le_rfl
  have pu (k : ℕ) : (diag c^k) u ∈ U := by
    have mem := clock_function_mem (fun v (hv : v∈U) => stable (Submodule.mem_map_of_mem hv))
      (fun z => z^k) hu
    exact (show (fun i => c i^k*u i)=(diag c^k) u by ext i; simp) ▸ mem
  apply le_antisymm
  · apply (clock_chain_le_iff _).mpr
    exact ⟨h₁.1,fun k hk => by rw [map_sub]; exact (chain _ _ _ n).sub_mem (h₁.2 k hk) (h₁.1 (pu k))⟩
  · apply (clock_chain_le_iff _).mpr
    refine ⟨h₂.1,?_⟩
    intro k hk
    have added := (chain (diag c) U (w-u) n).add_mem (h₂.2 k hk) (h₂.1 (pu k))
    simpa only [map_sub,sub_add_cancel] using added

/-- In a nonunital coordinate algebra, a finite union of live physical
coordinates has a representative equal to one there.  For one new row,
scale any nonzero coordinate to one; e+d-ed keeps every previously
matched row equal to one. No division by an unknown entry is performed. -/
private theorem cover (closed : ∀ u∈U, ∀ v∈U, u*v∈U) :
    ∃ e∈U, ∀ i, (∃ u∈U, u i≠0) → e i=1 := by
  classical
  have step (S : Finset (Fin s)) : ∃ e∈U, ∀ i∈S, (∃ u∈U,u i≠0) → e i=1 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0,U.zero_mem,by simp⟩
    | @insert i S ni ih =>
      obtain ⟨e,he,ok⟩ := ih
      by_cases live : ∃ u∈U, u i≠0
      · obtain ⟨u,hu,nz⟩ := live
        let v := (u i)⁻¹ • u
        have hv : v∈U := U.smul_mem _ hu
        have one : v i=1 := inv_mul_cancel₀ nz
        refine ⟨e+v-e*v,U.sub_mem (U.add_mem he hv) (closed _ he _ hv),?_⟩
        intro t ht hl
        rcases Finset.mem_insert.mp ht with rfl|hx
        · simp [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,one]
        · simp [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,ok t hx hl]
      · exact ⟨e,he,fun t ht hl =>
          (Finset.mem_insert.mp ht).elim (fun eq => False.elim (live (eq ▸ hl))) (fun hs => ok t hs hl)⟩
  obtain ⟨e,he,h⟩ := step Finset.univ
  exact ⟨e,he,fun i => h i (Finset.mem_univ i)⟩

/-- Select one representative of the same head simultaneously in every
grade, now zero at every physical coordinate supporting the core. -/
theorem disjoint_rep (stable : U.map (diag c)≤U)
    (closed : ∀ u∈U, ∀ v∈U, u*v∈U) (keep : ∀ u∈U, u*w∈U) :
    ∃ v : Fin s → K, (∀ i, (∃ u∈U, u i≠0) → v i=0) ∧
      ∀ n, chain (diag c) U v n=chain (diag c) U w n := by
  obtain ⟨e,he,one⟩ := cover closed
  refine ⟨w-e*w,fun i hi => ?_,shift stable (keep e he)⟩
  simp [Pi.sub_apply,Pi.mul_apply,one i hi]

/-- An observed multiplier on a complete band must be a low-degree
polynomial on *all physical head rows*, including duplicate clocks. -/
theorem multiplier_polynomial (off : ∀ i, (∃ u∈U, u i≠0) → w i=0)
    (many : n < (physicalSites c w).card)
    (band : ∀ k≤d, (diag c^k) (a*w) ∈ chain (diag c) U w n) :
    ∃ P : K[X], (P=0 ∨ P.natDegree+d<n) ∧ (∀ i, w i≠0 → a i=P.eval (c i)) := by
  classical
  have get (k : ℕ) (hk : k≤d) : ∃ Q : K[X], Q.degree<(n:WithBot ℕ) ∧
      ∀ i, w i≠0 → Q.eval (c i)=c i^k*a i := by
    obtain ⟨u,hu,Q,hd,expr⟩ := exists_poly (band k hk)
    refine ⟨Q,hd,fun i hi => ?_⟩
    have zu : u i=0 := by
      by_contra nz
      exact hi (off i ⟨u,hu,nz⟩)
    have eq := congrFun expr i
    rw [clock_power_value,Pi.mul_apply,Pi.add_apply,weightedEval_apply,zu,zero_add,←mul_assoc] at eq
    exact mul_right_cancel₀ hi eq.symm
  obtain ⟨P,hd,val⟩ := get 0 (by omega)
  have hp (i : Fin s) (hi : w i≠0) : P.eval (c i)=a i := by simpa using val i hi
  have high (Q : K[X]) (hq : Q.degree < (n:WithBot ℕ)) :
      (X*Q).degree < ((physicalSites c w).card:WithBot ℕ) := by
    by_cases z : Q=0
    · simp [z]
    · apply (natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero z)).mp
      have h := (natDegree_lt_iff_degree_lt z).mpr hq
      rw [natDegree_X_mul z]
      omega
  have all (k : ℕ) (hk : k≤d) : (X^k*P).degree < (n:WithBot ℕ) := by
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      obtain ⟨Q,hq,ev⟩ := get (k+1) hk
      have eq : Q=X*(X^k*P) := by
        apply eq_of_degrees_lt_of_eval_finset_eq (physicalSites c w)
          (hq.trans (by exact_mod_cast many)) (high _ (ih (by omega)))
        intro z hz
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
        have nz := (Finset.mem_filter.mp hi).2
        rw [ev i nz,eval_mul,eval_mul,eval_pow,eval_X,hp i nz,pow_succ']
        ring
      rw [pow_succ',mul_assoc,←eq]
      exact hq
  refine ⟨P,?_,fun i hi => (hp i hi).symm⟩
  by_cases z : P=0
  · exact Or.inl z
  · right
    have bd := (natDegree_lt_iff_degree_lt (mul_ne_zero (pow_ne_zero d X_ne_zero) z)).mpr (all d le_rfl)
    simpa only [natDegree_X_pow_mul d z] using bd

end RKResearch.Certified.Graded.HeadFiber
