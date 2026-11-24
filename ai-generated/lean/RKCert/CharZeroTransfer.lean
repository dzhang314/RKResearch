module

public import RKCert.PrimeTransfer

@[expose] public section

/-! # Characteristic-zero field images of rings

Even a characteristic-zero ring need not have a characteristic-zero maximal
residue field. Instead choose a prime disjoint from all positive integer
scalars (and, if required, all powers of a designated common diagonal), then
take the fraction field. The marker criterion is exact, including for rings
with nilpotents and additive torsion.
-/
namespace RKCert
universe u
variable {R : Type u} [CommRing R] {s p : ℕ} {Q : Prop}

private def markedNaturals (d : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, 0<n ∧ x=(n:R)*d^k}
  one_mem' := ⟨1,0,by decide,by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n,k,hn,rfl⟩ ⟨m,l,hm,rfl⟩
    refine ⟨n*m,k+l,Nat.mul_pos hn hm,?_⟩
    rw [Nat.cast_mul,pow_add]; ac_rfl

/-- Retain a common diagonal and characteristic zero in the *same* field.
The assumption is automatic for a unit marker in a characteristic-zero ring. -/
theorem specialize_charZero_marker {d : R}
    (hd : ∀ n k : ℕ, 0<n → (n:R)*d^k ≠ 0)
    (action : ∀ (K : Type u) [Field K] [CharZero K] (f : R →+* K), f d ≠ 0 → Q) : Q := by
  classical
  let M := markedNaturals d
  have dis : Disjoint ((⊥ : Ideal R) : Set R) (M : Set R) := Set.disjoint_left.mpr (by
    rintro x hx ⟨n,k,hn,rfl⟩
    exact hd n k hn ((Submodule.mem_bot R).mp hx))
  obtain ⟨I,hI,_,hdis⟩ := (⊥:Ideal R).exists_le_prime_disjoint M dis
  let := hI
  let K := FractionRing (R ⧸ I)
  let f : R →+* K := (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)
  have keeps (x : R) (hx : x ∈ M) : f x ≠ 0 := by
    intro h
    apply Set.disjoint_left.mp hdis _ hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ I) K
    simpa [f] using h
  let : CharZero K := charZero_of_inj_zero (by
    intro n hn
    by_contra h
    have hz := keeps (n:R) ⟨n,0,Nat.pos_of_ne_zero h,by simp⟩
    exact hz ((map_natCast f n).trans hn))
  exact action K f (keeps d ⟨1,1,by decide,by simp⟩)

/-- Exactly which markers disappear in *every characteristic-zero* field
image. Compare with plain nilpotence when fields of all characteristics are
allowed. Positive integer torsion times a power of the marker is the precise
additional obstruction. -/
theorem all_charZero_field_images_zero_iff (d : R) :
    (∀ (K : Type u) [Field K] [CharZero K] (f : R →+* K), f d=0) ↔
      ∃ n k : ℕ, 0<n ∧ (n:R)*d^k=0 := by
  constructor
  · intro h
    by_contra hh
    push Not at hh
    exact specialize_charZero_marker hh (fun K _ _ f hf => hf (h K f))
  · rintro ⟨n,k,hn,h⟩ K _ _ f
    have hh := congrArg f h
    simp only [map_mul,map_natCast,map_pow,map_zero] at hh
    by_contra he
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero k he)) hh

/-- Every characteristic-zero commutative ring has a unital homomorphism
to some characteristic-zero field (not necessarily a maximal residue field). -/
theorem specialize_charZero [CharZero R]
    (action : ∀ (K : Type u) [Field K] [CharZero K] (_f : R →+* K), Q) : Q :=
  specialize_charZero_marker (d:=(1:R)) (fun n _ hn => by simp [Nat.ne_of_gt hn])
    (fun K _ _ f _ => action K f)

theorem explicit_of_charZero_fields [CharZero R]
    (hfield : ∀ (K : Type u) [Field K] [CharZero K] (A : Fin s → Fin s → K) (b : Fin s → K),
      StrictLower A → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b p) : Q :=
  specialize_charZero (R:=R) (fun K _ _ f => hfield K _ _ (ha.map f) (ho.map f))

theorem lowerTriangular_of_charZero_fields [CharZero R]
    (hfield : ∀ (K : Type u) [Field K] [CharZero K] (A : Fin s → Fin s → K) (b : Fin s → K),
      (∀ i j, i.val < j.val → A i j=0) → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} (ha : ∀ i j, i.val < j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) : Q :=
  specialize_charZero (R:=R) (fun K _ _ f => hfield K _ _ (lowerTriangular_map ha f) (ho.map f))

/-- Strict SDIRK char-zero field results transfer with a unit shared diagonal,
or more generally with the exact torsion/power avoidance condition. -/
theorem markedCommonDiagonal_of_charZero_fields
    (hfield : ∀ (K : Type u) [Field K] [CharZero K] (A : Fin s → Fin s → K) (b : Fin s → K) (d:K),
      (∀ i j, i.val < j.val → A i j=0) → (∀i,A i i=d) → d≠0 → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} {d : R} (ha : ∀ i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=d) (hd : ∀ n k : ℕ, 0<n → (n:R)*d^k≠0)
    (ho : HasTreeOrderAtLeast A b p) : Q :=
  specialize_charZero_marker hd (fun K _ _ f hf =>
    hfield K _ _ (f d) (lowerTriangular_map ha f) (fun i => congrArg f (he i)) hf (ho.map f))

theorem unitCommonDiagonal_of_charZero_fields [CharZero R]
    (hfield : ∀ (K : Type u) [Field K] [CharZero K] (A : Fin s → Fin s → K) (b : Fin s → K) (d:K),
      (∀ i j, i.val < j.val → A i j=0) → (∀i,A i i=d) → d≠0 → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} {d : R} (ha : ∀ i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=d) (hd : IsUnit d) (ho : HasTreeOrderAtLeast A b p) : Q := by
  apply markedCommonDiagonal_of_charZero_fields hfield ha he _ ho
  intro n k hn hz
  have hh : (n:R)*d^k=0*d^k := by simpa using hz
  exact (Nat.cast_ne_zero.mpr hn.ne') ((hd.pow k).mul_right_cancel hh)

end RKCert
