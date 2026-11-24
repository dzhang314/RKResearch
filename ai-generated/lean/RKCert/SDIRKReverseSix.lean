module

public import RKCert.GradeSeparation
public import RKCert.SDIRKCommutator

@[expose] public section

/-! # Six-row adjoint census for a nonsingular order-six/six-stage tableau

Write Bₖ for the row `b C^k`. The six canonical functionals
`B₀, B₁, B₀R, B₁R, B₂R, B₀R²` span the full stage dual. This uses the
actual cost-two commutator R, not a dimension count for unrelated row words.
No common-diagonal, positivity, or characteristic-zero assumption is imposed.
-/
namespace RKCert.Paired.SDIRK
open RKCert.Paired

variable {K : Type*} [Field K] {s : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- A linear combination of the first n raw moment rows. -/
noncomputable def probePacket (A : Fin s → Fin s → K) (b : Vec K s) (n : ℕ) :
    (Fin n → K) →ₗ[K] Module.Dual K (Vec K s) :=
  Fintype.linearCombination K (fun j : Fin n => probe A b j.val)

theorem probePacket_apply (A : Fin s → Fin s → K) (b : Vec K s) (n : ℕ)
    (a : Fin n → K) (v : Vec K s) :
    probePacket A b n a v = ∑ j : Fin n, a j * probe A b j.val v := by
  simp [probePacket, Fintype.linearCombination_apply, LinearMap.sum_apply]

/-- If its tests against the first n bushes vanish, the scalar packet is zero.
The exact paid budget is `2n−1 ≤ p` for nonempty packets. -/
theorem probePacket_detect {p n : ℕ} (ho : HasTreeOrderAtLeast A b p) (hn : 2*n≤p+1)
    (a : Fin n → K) (hz : ∀ i : Fin n, probePacket A b n a (normTree A (Tree.bush i.val))=0) :
    a=0 := by
  ext j
  apply moments_detect ho (d:=1) (by decide) (by omega) (fun i l => by omega) a _ j
  intro i
  rw [← hz i, probePacket_apply]
  apply Finset.sum_congr rfl
  intro k _
  have h := probe_normTree ho (Tree.bush i.val) k.val (by rw [Tree.order_bush]; omega)
  rw [Tree.order_bush] at h
  have hi : k.val+(i.val+1) = i.val+k.val+1 := by omega
  rw [hi] at h
  have hn' := (IsUnit.of_mul_eq_one _ h).ne_zero
  symm
  apply (eq_div_iff hn').mpr
  calc
    _ = a k * (((i.val+k.val+1 : ℕ):K) * probe A b k.val (normTree A (Tree.bush i.val))) := by ac_rfl
    _ = _ := by rw [h, mul_one]

/-- The four intermediate rows B₀, B₁, B₂, B₀ R. -/
noncomputable def fourRows (A : Fin s → Fin s → K) (b : Vec K s) :
    ((Fin 3 → K) × K) →ₗ[K] Module.Dual K (Vec K s) :=
  (probePacket A b 3).coprod
    ((LinearMap.id : K →ₗ[K] K).smulRight ((probe A b 0).comp (R A)))

theorem fourRows_apply (A : Fin s → Fin s → K) (b : Vec K s) (z : (Fin 3→K) × K)
    (v : Vec K s) : fourRows A b z v = probePacket A b 3 z.1 v + z.2 * probe A b 0 (R A v) := rfl

private theorem bush_mem (A : Fin s → Fin s → K) (j : ℕ) :
    normTree A (Tree.bush j) ∈ treeSpace A j :=
  (treeSpace A j).smul_mem _ (stageWeight_mem_space _ _ (by rw [Tree.order_bush]))

theorem fourRows_injective (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hn : ∀i,A i i≠0) :
    Function.Injective (fourRows A b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hz' (v : Vec K s) := LinearMap.congr_fun hz v
  have h1 : z.1=0 := by
    apply probePacket_detect ho (by decide)
    intro i
    have h := hz' (normTree A (Tree.bush i.val))
    rw [fourRows_apply, probe_commutator ho (by omega) (bush_mem A i.val), mul_zero, add_zero] at h
    exact h
  obtain ⟨v,hv⟩ := (LinearMap.surjective_of_injective (commutator_injective ha hn)) 1
  have h := hz' v
  have hunit : probe A b 0 1=1 := by
    simpa only [normTree_leaf,Tree.order,Nat.zero_add,Nat.cast_one,one_mul] using
      probe_normTree ho .leaf 0 (by decide)
  rw [fourRows_apply, h1, map_zero, LinearMap.zero_apply, zero_add,hv,hunit,mul_one] at h
  exact Prod.ext h1 h

/-- Canonical six-row map; the second block is pullback by the *actual* R. -/
noncomputable def sixRows (A : Fin s → Fin s → K) (b : Vec K s) :
    ((Fin 2 → K) × ((Fin 3 → K) × K)) →ₗ[K] Module.Dual K (Vec K s) :=
  (probePacket A b 2).coprod ((R A).dualMap.comp (fourRows A b))

theorem sixRows_apply (A : Fin s → Fin s → K) (b : Vec K s) (z : (Fin 2→K)×((Fin 3→K)×K))
    (v : Vec K s) : sixRows A b z v = probePacket A b 2 z.1 v + fourRows A b z.2 (R A v) := rfl

theorem sixRows_injective (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hn : ∀i,A i i≠0) :
    Function.Injective (sixRows A b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have h1 : z.1=0 := by
    apply probePacket_detect ho (by decide)
    intro i
    let v := normTree A (Tree.bush i.val)
    have hv : v ∈ treeSpace A i.val := bush_mem _ _
    have h := LinearMap.congr_fun hz v
    have hz' (k : Fin 3) : probe A b k.val (R A v) = 0 :=
      probe_commutator ho (by omega) hv
    have hz'' : probe A b 0 (R A (R A v))=0 :=
      probe_commutator ho (by omega) (commutator_mem hv)
    rw [sixRows_apply, fourRows_apply, hz'', mul_zero, add_zero, probePacket_apply A b 3] at h
    simpa only [hz', mul_zero, Finset.sum_const_zero, add_zero, LinearMap.zero_apply] using h
  have h2 : z.2=0 := by
    apply fourRows_injective ho ha hn
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (LinearMap.surjective_of_injective (commutator_injective ha hn)) w
    have h := LinearMap.congr_fun hz v
    rw [sixRows_apply,h1,map_zero,LinearMap.zero_apply,zero_add] at h
    simpa using h
  exact Prod.ext h1 h2

/-- Exactly six stages plus achieved order six make these six canonical
rows a basis of the entire dual, with no cancellation of individual weights. -/
theorem sixRows_surjective {A : Fin 6 → Fin 6 → K} {b : Vec K 6}
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hn : ∀i,A i i≠0) :
    Function.Surjective (sixRows A b) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank _).mp (sixRows_injective ho ha hn)
  simp [Vec,Subspace.dual_finrank_eq]

/-- Direct, coordinate-free use of the census: every linear functional is
one of the displayed combinations with six scalar coefficients. -/
theorem canonical_rows_span {A : Fin 6 → Fin 6 → K} {b : Vec K 6}
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hn : ∀i,A i i≠0)
    (φ : Module.Dual K (Vec K 6)) :
    ∃ (a : Fin 2 → K) (c : Fin 3 → K) (d : K), ∀ v : Vec K 6,
      φ v = (∑ j : Fin 2, a j * probe A b j.val v) +
        (∑ j : Fin 3, c j * probe A b j.val (R A v)) + d * probe A b 0 (R A (R A v)) := by
  obtain ⟨⟨a,c,d⟩,rfl⟩ := sixRows_surjective ho ha hn φ
  refine ⟨a,c,d,fun v => ?_⟩
  rw [sixRows_apply, fourRows_apply, probePacket_apply, probePacket_apply]
  simp only [add_assoc]

end RKCert.Paired.SDIRK
