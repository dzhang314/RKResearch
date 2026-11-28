import RKCert.ReviewedNative.ERK10MirrorPortfolio
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKResearch.Certified

variable {R : Type*} [CommRing R] [Ring.KrullDimLE 0 R]

private def nilAnnihilator (a : R) : Ideal R where
  carrier := {x | IsNilpotent (x*a)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change IsNilpotent (x*a) at hx
    change IsNilpotent (y*a) at hy
    change IsNilpotent ((x+y)*a)
    rw [add_mul]
    exact Commute.isNilpotent_add (Commute.all _ _) hx hy
  smul_mem' := by
    intro c x hx
    change IsNilpotent (x*a) at hx
    change IsNilpotent ((c*x)*a)
    rw [mul_assoc]
    exact Commute.isNilpotent_mul_left (Commute.all _ _) hx

private lemma separates (a : R) (p : Ideal R) [p.IsPrime] (ha : a ∈ p) :
    ∃ s ∉ p, s ∈ nilAnnihilator a := by
  let S := Localization.AtPrime p
  have hmin : p ∈ minimalPrimes R := Ideal.mem_minimalPrimes_of_krullDimLE_zero p
  let : Ring.KrullDimLE 0 S := Ring.KrullDimLE.of_isLocalization p hmin S
  have hmem : algebraMap R S a ∈ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨n,hn⟩ := Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hmem
  have hzero : algebraMap R S (a^n) = 0 := by simpa only [map_pow] using hn
  obtain ⟨s,hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S (a^n)).mp hzero
  refine ⟨s, s.property, ?_⟩
  change IsNilpotent ((s:R)*a)
  refine ⟨n+1, ?_⟩
  rw [mul_pow]
  have hz : a^n * (s:R) = 0 := by simpa [mul_comm] using hs
  calc
    (s:R)^(n+1) * a^(n+1) = ((s:R)^n * a) * (a^n * (s:R)) := by
      rw [pow_succ (s:R),pow_succ a]
      ring
    _ = 0 := by rw [hz,mul_zero]

omit [Ring.KrullDimLE 0 R] in
private lemma nil_mem (p : Ideal R) [p.IsPrime] {x : R} (hx : IsNilpotent x) :
    x ∈ p := by
  exact nilpotent_iff_mem_prime.mp hx p inferInstance

theorem exists_unit_add_idempotent_dim_zero (a : R) :
    ∃ (u : Rˣ) (e : R), e*e=e ∧ a=(u:R)+e := by
  let J := nilAnnihilator a
  have htop : Ideal.span {a} ⊔ J = ⊤ := by
    by_contra h
    obtain ⟨p,hm,hp⟩ := Ideal.exists_le_maximal _ h
    let : p.IsMaximal := hm
    have ha : a ∈ p := hp (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
    obtain ⟨s,hs,hJ⟩ := separates a p ha
    exact hs (hp (Ideal.mem_sup_right hJ))
  have hone : (1:R) ∈ Ideal.span {a} ⊔ J := by simp [htop]
  obtain ⟨b,c,hc,hbc⟩ := Ideal.mem_span_singleton_sup.mp hone
  let z := b*a
  have hz : z+c=1 := hbc
  have hnil : IsNilpotent (c*a) := hc
  have hz' : IsNilpotent (z*z-z) := by
    have h : z*z-z = (-b)*(c*a) := by
      have h' : z*z-z = -z*c := by linear_combination z * hz
      rw [h']
      dsimp [z]
      ring
    rw [h]
    exact Commute.isNilpotent_mul_left (Commute.all _ _) hnil
  let f := Ideal.Quotient.mk (nilradical R)
  have hf : ∀ x ∈ RingHom.ker f, IsNilpotent x := by
    intro x hx
    exact mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hid : IsIdempotentElem (f z) := by
    have h : f (z*z-z) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (mem_nilradical.mpr hz')
    rw [map_sub,map_mul,sub_eq_zero] at h
    exact h
  obtain ⟨v,hv,hfv⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hf (f z)
    ⟨z,rfl⟩ hid
  have hdiff : IsNilpotent (z-v) := hf _ (by
    change f (z-v) = 0
    rw [map_sub,hfv,sub_self])
  let e := 1-v
  have he : e*e=e := by
    change (1-v)*(1-v)=1-v
    linear_combination hv.eq
  have hu : IsUnit (a-e) := by
    by_contra hn
    obtain ⟨p,hm,hp⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hn)
    let : p.IsMaximal := hm
    have hau : a-e ∈ p := hp (Ideal.mem_span_singleton_self _)
    have hd : z-v ∈ p := nil_mem p hdiff
    apply Ideal.one_notMem p
    by_cases ha : a ∈ p
    · have hzp : z ∈ p := p.mul_mem_left b ha
      have hvp : v ∈ p := by simpa using p.sub_mem hzp hd
      have hep : e ∈ p := by simpa using p.sub_mem ha hau
      simpa [e] using p.add_mem hep hvp
    · have hcp : c ∈ p := ((Ideal.IsPrime.mem_or_mem inferInstance (nil_mem p hnil))).resolve_right ha
      have hep : e ∈ p := by
        have h : e = c+(z-v) := by dsimp [e]; linear_combination -hz
        rw [h]
        exact p.add_mem hcp hd
      exact False.elim (ha (by simpa using p.add_mem hau hep))
  refine ⟨hu.unit,e,he,?_⟩
  rw [IsUnit.unit_spec]
  ring

/-- The 16-stage exact order-ten portfolio glues over every nonzero
commutative ring of Krull dimension zero with 10! invertible. -/
theorem ERK10MirrorPortfolio.dimension_zero_exact [Nontrivial R]
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) : ExactExplicitPortfolio.Exact 16 10 R :=
  ERK10MirrorPortfolio.clean_ring_exact R exists_unit_add_idempotent_dim_zero hf

/-- A nonzero algebra with a paid zero-dimensional coefficient ring
inherits the exact tableau, including its unit eleventh-order witness. -/
theorem ERK10MirrorPortfolio.dimension_zero_coefficients_exact {S : Type*}
    [CommRing S] [Nontrivial S] (hf : IsUnit ((Nat.factorial 10 : Nat) : R))
    (f : R →+* S) : ExactExplicitPortfolio.Exact 16 10 S :=
  ERK10MirrorPortfolio.clean_coefficients_exact exists_unit_add_idempotent_dim_zero hf f

#print axioms exists_unit_add_idempotent_dim_zero
#print axioms ERK10MirrorPortfolio.dimension_zero_exact
#print axioms ERK10MirrorPortfolio.dimension_zero_coefficients_exact
end RKResearch.Certified
