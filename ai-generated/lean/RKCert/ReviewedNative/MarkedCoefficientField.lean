module
public import RKCert.ReviewedNative.CoefficientField

@[expose] public section

/-! # Preserve a designated coefficient in a characteristic-zero field image

The ordinary characteristic-zero specialization need not preserve a
nonunit. Enlarge the avoided multiplicative set by all powers of the marker.
This is a coefficient-ring lemma; it requires no Runge–Kutta definitions. -/
namespace RKCert.ReviewedNative
universe u
variable {R : Type u} [CommRing R] {Q : Prop}

private def markedNaturals (d : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, 0<n ∧ x=(n:R)*d^k}
  one_mem' := ⟨1,0,by decide,by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n,k,hn,rfl⟩ ⟨m,l,hm,rfl⟩
    refine ⟨n*m,k+l,Nat.mul_pos hn hm,?_⟩
    rw [Nat.cast_mul,pow_add]; ac_rfl

/-- Retain a common diagonal and characteristic zero in the *same* field.
The assumption is automatic for a unit marker in a characteristic-zero ring. -/
theorem with_marked_charZero_field {d : R}
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
    exact with_marked_charZero_field hh (fun K _ _ f hf => hf (h K f))
  · rintro ⟨n,k,hn,h⟩ K _ _ f
    have hh := congrArg f h
    simp only [map_mul,map_natCast,map_pow,map_zero] at hh
    by_contra he
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero k he)) hh

end RKCert.ReviewedNative
