module

public import RKCert.ReviewedNative.DefectPrefix

@[expose] public section

/-! # Actual low-grade subspaces for the order-seven/eight certificates -/
namespace RKResearch.Certified.Graded.LowDefects

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The genuine quadratic primitive defect. -/
abbrev seed (B : Matrix ι ι R) : ι → R := monomialStageDefect B 1

abbrev seedSpace (B : Matrix ι ι R) : Submodule R (ι → R) :=
  Submodule.span R ({seed B} : Set (ι → R))

/-- A candidate cubic space can be any certified cover. In particular
one can use all four generators, or a smaller paid rank chart. -/
structure CubicCover (B : Matrix ι ι R) (U : Submodule R (ι → R)) : Prop where
  seed_mem : seed B ∈ U
  clock_seed : diag (nodes B) (seed B) ∈ U
  advance_seed : mat B (seed B) ∈ U
  primitive : monomialStageDefect B 2 ∈ U

def generatedCubic (B : Matrix ι ι R) : Submodule R (ι → R) :=
  Submodule.span R
    ({seed B, diag (nodes B) (seed B), mat B (seed B), monomialStageDefect B 2} :
      Set (ι → R))

theorem generated_cubic_cover (B : Matrix ι ι R) : CubicCover B (generatedCubic B) := by
  constructor <;> apply Submodule.subset_span <;> simp [generatedCubic]

theorem span_pair_le_iff {v w : ι → R} {U : Submodule R (ι → R)} :
    Submodule.span R ({v, w} : Set (ι → R)) ≤ U ↔ v ∈ U ∧ w ∈ U := by
  constructor
  · intro h
    exact ⟨h (Submodule.subset_span (by simp)), h (Submodule.subset_span (by simp))⟩
  · rintro ⟨hv, hw⟩
    apply Submodule.span_le.mpr
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hv
    · exact hw

/-- G₄ adjoins the two operator images, the quadratic product, and e₄. -/
def quartic (B : Matrix ι ι R) (U : Submodule R (ι → R)) : Submodule R (ι → R) :=
  U ⊔ (U.map (diag (nodes B)) ⊔ (U.map (mat B) ⊔
    Submodule.span R ({seed B * seed B, monomialStageDefect B 3} : Set (ι → R))))

/-- G₅ adjoins the two operator images, the seed-times-cubic products,
and e₅. The construction does not involve the weights or any chosen scale. -/
def quintic (B : Matrix ι ι R) (U : Submodule R (ι → R)) : Submodule R (ι → R) :=
  let V := quartic B U
  V ⊔ (V.map (diag (nodes B)) ⊔
    (V.map (mat B) ⊔ (U.map (diag (seed B)) ⊔
      Submodule.span R ({monomialStageDefect B 4} : Set (ι → R)))))

/-- A quartic test packet is exactly four submodule/generator tests. -/
theorem quartic_le_iff (B : Matrix ι ι R) (U W : Submodule R (ι → R)) :
    quartic B U ≤ W ↔
      U ≤ W ∧ U ≤ W.comap (diag (nodes B)) ∧ U ≤ W.comap (mat B) ∧
      seed B * seed B ∈ W ∧ monomialStageDefect B 3 ∈ W := by
  simp only [quartic, sup_le_iff, Submodule.map_le_iff_le_comap, span_pair_le_iff]

/-- The exact five-column-family expansion of a quintic submodule test. -/
theorem quintic_le_iff (B : Matrix ι ι R) (U W : Submodule R (ι → R)) :
    quintic B U ≤ W ↔
      quartic B U ≤ W ∧ quartic B U ≤ W.comap (diag (nodes B)) ∧
      quartic B U ≤ W.comap (mat B) ∧ U ≤ W.comap (diag (seed B)) ∧
      monomialStageDefect B 4 ∈ W := by
  simp only [quintic, sup_le_iff, Submodule.map_le_iff_le_comap,
    Submodule.span_singleton_le_iff_mem]

variable {B : Matrix ι ι R} {U : Submodule R (ι → R)}

theorem quartic_clock : U ≤ (quartic B U).comap (diag (nodes B)) :=
  ((quartic_le_iff B U _).mp le_rfl).2.1

theorem quartic_advance : U ≤ (quartic B U).comap (mat B) :=
  ((quartic_le_iff B U _).mp le_rfl).2.2.1

theorem quartic_square : seed B * seed B ∈ quartic B U :=
  ((quartic_le_iff B U _).mp le_rfl).2.2.2.1

theorem quartic_primitive : monomialStageDefect B 3 ∈ quartic B U :=
  ((quartic_le_iff B U _).mp le_rfl).2.2.2.2

theorem quintic_clock : quartic B U ≤ (quintic B U).comap (diag (nodes B)) :=
  ((quintic_le_iff B U _).mp le_rfl).2.1

theorem quintic_advance : quartic B U ≤ (quintic B U).comap (mat B) :=
  ((quintic_le_iff B U _).mp le_rfl).2.2.1

theorem quintic_primitive : monomialStageDefect B 4 ∈ quintic B U :=
  ((quintic_le_iff B U _).mp le_rfl).2.2.2.2

theorem quintic_seed_product : ProductsIn (seedSpace B) U (quintic B U) :=
  ProductsIn.singleton_left _ (((quintic_le_iff B U _).mp le_rfl).2.2.2.1)

def prefixBase (B : Matrix ι ι R) : DefectPrefix B 2 where
  space := fun _ => ⊥
  zero := rfl
  one := rfl
  clock := fun _ _ => bot_le
  advance := fun _ _ => bot_le
  primitive := by
    intro j hj
    have hj' : j = 0 := by omega
    subst j
    simpa only [monomialStageDefect_at_zero] using
      (⊥ : Submodule R (ι → R)).zero_mem
  product := by
    intro j k hj v w hv hw
    have hz : v = 0 := (Submodule.mem_bot R).mp hv
    simpa only [hz, zero_mul] using (⊥ : Submodule R (ι → R)).zero_mem

def prefixSeed (B : Matrix ι ι R) : DefectPrefix B 3 :=
  (prefixBase B).append (by decide) (seedSpace B) bot_le bot_le
    (Submodule.mem_span_singleton_self _) (by intro j k hj hk hsum; omega)

def prefixCubic (h : CubicCover B U) : DefectPrefix B 4 :=
  (prefixSeed B).append (by decide) U
    ((Submodule.span_singleton_le_iff_mem _ _).mpr h.clock_seed)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr h.advance_seed)
    h.primitive (by intro j k hj hk hsum; omega)

/-- Prefix through degree four: 0,0,span(s),U,G₄. -/
def prefixQuartic (h : CubicCover B U) : DefectPrefix B 5 :=
  (prefixCubic h).append (by decide) (quartic B U)
    quartic_clock quartic_advance quartic_primitive (by
      intro j k hj hk hsum
      have hj' : j = 2 := by omega
      have hk' : k = 2 := by omega
      subst j
      subst k
      exact ProductsIn.singleton_pair quartic_square)

/-- Prefix through degree five: G₅ is the only additional space. -/
def prefixQuintic (h : CubicCover B U) : DefectPrefix B 6 :=
  (prefixQuartic h).append (by decide) (quintic B U)
    (quintic_clock (B := B) (U := U)) (quintic_advance (B := B) (U := U)) (quintic_primitive (B := B) (U := U)) (by
      intro j k hj hk hsum
      have e : (j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2) := by omega
      rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact quintic_seed_product (B := B) (U := U)
      · exact (quintic_seed_product (B := B) (U := U)).swap)

end RKResearch.Certified.Graded.LowDefects
