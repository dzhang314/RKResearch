module

public import RKCert.ReviewedNative.SDIRKSixFlags
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! # Six-row adjoint census for a nonsingular order-six/six-stage tableau

Write Bₖ for the row `b C^k`. The six canonical functionals
`B₀, B₁, B₀R, B₁R, B₂R, B₀R²` span the full stage dual. This uses the
actual cost-two commutator R, not a dimension count for unrelated row words.
No common-diagonal, positivity, or characteristic-zero assumption is imposed.
-/
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)}

/-- A linear combination of the first n raw moment rows. -/
noncomputable def probePacket (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (n : ℕ) :
    (Fin n → K) →ₗ[K] Module.Dual K ((Fin s → K)) :=
  Fintype.linearCombination K (fun j : Fin n => probe A b j.val)

theorem probePacket_apply (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (n : ℕ)
    (a : Fin n → K) (v : (Fin s → K)) :
    probePacket A b n a v = ∑ j : Fin n, a j * probe A b j.val v := by
  simp [probePacket, Fintype.linearCombination_apply, LinearMap.sum_apply]

/-- If its tests against the first n bushes vanish, the scalar packet is zero.
The exact paid budget is `2n−1 ≤ p` for nonempty packets. -/
theorem probePacket_detect {p n : ℕ} (ho : HasOrder p A b) (hn : 2*n≤p+1)
    (a : Fin n → K) (hz : ∀ i : Fin n, probePacket A b n a (normTree A (clockTree i.val))=0) :
    a=0 := by
  ext j
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) a _ j
  intro i
  rw [← hz i, probePacket_apply]
  apply Finset.sum_congr rfl
  intro k _
  have h := probe_normTree ho (clockTree i.val) k.val (by rw [order_clockTree]; omega)
  rw [order_clockTree] at h
  have hi : k.val+(i.val+1) = i.val+k.val+1 := by omega
  rw [hi] at h
  have hn' := (IsUnit.of_mul_eq_one _ h).ne_zero
  symm
  apply (eq_div_iff hn').mpr
  calc
    _ = a k * (((i.val+k.val+1 : ℕ):K) * probe A b k.val (normTree A (clockTree i.val))) := by ac_rfl
    _ = _ := by rw [h, mul_one]

/-- The four intermediate rows B₀, B₁, B₂, B₀ R. -/
noncomputable def fourRows (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) :
    ((Fin 3 → K) × K) →ₗ[K] Module.Dual K ((Fin s → K)) :=
  (probePacket A b 3).coprod
    ((LinearMap.id : K →ₗ[K] K).smulRight ((probe A b 0).comp (volterra A)))

theorem fourRows_apply (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (z : (Fin 3→K) × K)
    (v : (Fin s → K)) : fourRows A b z v = probePacket A b 3 z.1 v + z.2 * probe A b 0 (volterra A v) := rfl

private theorem bush_mem (A : Matrix (Fin s) (Fin s) K) (j : ℕ) :
    normTree A (clockTree j) ∈ treeSpace A j :=
  (treeSpace A j).smul_mem _ (Φ_mem_treeSpace _ _ (by rw [order_clockTree]))

theorem fourRows_injective (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hn : ∀i,A i i≠0) :
    Function.Injective (fourRows A b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hz' (v : (Fin s → K)) := LinearMap.congr_fun hz v
  have h1 : z.1=0 := by
    apply probePacket_detect ho (by decide)
    intro i
    have h := hz' (normTree A (clockTree i.val))
    rw [fourRows_apply, probe_commutator ho (by omega) (bush_mem A i.val), mul_zero, add_zero] at h
    exact h
  obtain ⟨v,hv⟩ := (LinearMap.surjective_of_injective (volterra_injective ha hn)) 1
  have h := hz' v
  have hunit : probe A b 0 1=1 := by
    simpa only [normTree_leaf,order,PNat.one_coe,Nat.zero_add,Nat.cast_one,one_mul] using
      probe_normTree ho .leaf 0 (by decide)
  rw [fourRows_apply, h1, map_zero, LinearMap.zero_apply, zero_add,hv,hunit,mul_one] at h
  exact Prod.ext h1 h

/-- Canonical six-row map; the second block is pullback by the *actual* R. -/
noncomputable def sixRows (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) :
    ((Fin 2 → K) × ((Fin 3 → K) × K)) →ₗ[K] Module.Dual K ((Fin s → K)) :=
  (probePacket A b 2).coprod ((volterra A).dualMap.comp (fourRows A b))

theorem sixRows_apply (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) (z : (Fin 2→K)×((Fin 3→K)×K))
    (v : (Fin s → K)) : sixRows A b z v = probePacket A b 2 z.1 v + fourRows A b z.2 (volterra A v) := rfl

theorem sixRows_injective (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hn : ∀i,A i i≠0) :
    Function.Injective (sixRows A b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have h1 : z.1=0 := by
    apply probePacket_detect ho (by decide)
    intro i
    let v := normTree A (clockTree i.val)
    have hv : v ∈ treeSpace A i.val := bush_mem _ _
    have h := LinearMap.congr_fun hz v
    have hz' (k : Fin 3) : probe A b k.val (volterra A v) = 0 :=
      probe_commutator ho (by omega) hv
    have hz'' : probe A b 0 (volterra A (volterra A v))=0 :=
      probe_commutator ho (by omega) (zeroSpace_le_treeSpace _ _ (volterra_treeSpace ho _ (by omega) hv))
    rw [sixRows_apply, fourRows_apply, hz'', mul_zero, add_zero, probePacket_apply A b 3] at h
    simpa only [hz', mul_zero, Finset.sum_const_zero, add_zero, LinearMap.zero_apply] using h
  have h2 : z.2=0 := by
    apply fourRows_injective ho ha hn
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (LinearMap.surjective_of_injective (volterra_injective ha hn)) w
    have h := LinearMap.congr_fun hz v
    rw [sixRows_apply,h1,map_zero,LinearMap.zero_apply,zero_add] at h
    simpa using h
  exact Prod.ext h1 h2

/-- Exactly six stages plus achieved order six make these six canonical
rows a basis of the entire dual, with no cancellation of individual weights. -/
theorem sixRows_surjective {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hn : ∀i,A i i≠0) :
    Function.Surjective (sixRows A b) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank _).mp (sixRows_injective ho ha hn)
  simp [Subspace.dual_finrank_eq]

/-- Direct, coordinate-free use of the census: every linear functional is
one of the displayed combinations with six scalar coefficients. -/
theorem canonical_rows_span {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hn : ∀i,A i i≠0)
    (φ : Module.Dual K ((Fin 6 → K))) :
    ∃ (a : Fin 2 → K) (c : Fin 3 → K) (d : K), ∀ v : (Fin 6 → K),
      φ v = (∑ j : Fin 2, a j * probe A b j.val v) +
        (∑ j : Fin 3, c j * probe A b j.val (volterra A v)) + d * probe A b 0 (volterra A (volterra A v)) := by
  obtain ⟨⟨a,c,d⟩,rfl⟩ := sixRows_surjective ho ha hn φ
  refine ⟨a,c,d,fun v => ?_⟩
  rw [sixRows_apply, fourRows_apply, probePacket_apply, probePacket_apply]
  simp only [add_assoc]

end RKResearch.Certified.Graded.SDIRKSix
