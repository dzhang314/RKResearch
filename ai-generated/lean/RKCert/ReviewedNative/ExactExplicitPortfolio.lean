module

public import RKResearch.ERK
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

/-! Exact order, unlike mere order-at-least, needs injection at the
last cast from the finite residue ring. This is generic in the
tableau width, the requested order and the chart denominators. -/
namespace RKResearch.Certified.ExactExplicitPortfolio
open FiniteRootedTree
open scoped Matrix

def Exact (s p : ℕ) (R : Type*) [CommRing R] : Prop :=
  ∃ A : Matrix (Fin s) (Fin s) R, ∃ b : Fin s → R,
    ERK A ∧ HasOrder p A b ∧ ¬ HasOrder (p+1) A b

variable {R S : Type*} [CommRing R] [CommRing S] {s p : Nat}

private theorem of_map_order {q : Nat} {A : Matrix (Fin s) (Fin s) R}
    {b : Fin s → R} (f : R →+* S) (hf : Function.Injective f)
    (h : HasOrder q (A.map f) (f ∘ b)) : HasOrder q A b := by
  intro t ht
  apply hf
  rw [map_mul, map_natCast, RingHom.map_dotProduct, map_Φ, map_one]
  exact h t ht

/-- An injective scalar extension preserves not just the first p
conditions, but also failure of the next order. -/
theorem Exact.map (h : Exact s p R) (f : R →+* S)
    (hf : Function.Injective f) : Exact s p S := by
  obtain ⟨A,b,ha,ho,hn⟩ := h
  refine ⟨A.map f, f ∘ b, ?_, ho.map f, fun h' => hn (of_map_order f hf h')⟩
  intro i j hij
  change f (A i j) = 0
  rw [ha hij, map_zero]

private theorem fst_hom (z : R × S) : z.1 = (RingHom.fst R S) z := rfl
private theorem snd_hom (z : R × S) : z.2 = (RingHom.snd R S) z := rfl

theorem Exact.prod (h : Exact s p R) (k : Exact s p S) : Exact s p (R × S) := by
  obtain ⟨A,b,ha,hA,hAn⟩ := h
  obtain ⟨B,c,hb,hB,_⟩ := k
  let T : Matrix (Fin s) (Fin s) (R × S) := Matrix.of fun i j => (A i j, B i j)
  let w : Fin s → R × S := fun i => (b i, c i)
  refine ⟨T,w,?_ ,?_ ,?_⟩
  · intro i j hij
    exact Prod.ext (ha hij) (hb hij)
  · intro t ht
    apply Prod.ext
    · rw [fst_hom, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hA t ht
    · rw [snd_hom, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hB t ht
  · intro e
    apply hAn
    exact e.map (RingHom.fst R S)

/-- A prime-power source can be glued without any uniform choice of
its tableaux or witnesses. Each factor retains the same stage slots. -/
theorem zmod_exact_of_prime_powers (P : Nat)
    (base : ∀ q k : Nat, q.Prime → 0 < k → P.Coprime (q^k) →
      Exact s p (ZMod (q^k))) :
    ∀ n : Nat, 1 < n → P.Coprime n → Exact s p (ZMod n) := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n => 1 < n → P.Coprime n → Exact s p (ZMod n)) ?_ ?_ ?_ ?_
  · intro q k hq hk _ hc
    exact base q k hq hk hc
  · omega
  · omega
  · intro a b ha hb hab Ha Hb h hc
    by_cases ha' : 1<a
    · by_cases hb' : 1<b
      · have Pa := Ha ha' (hc.coprime_dvd_right (show a ∣ a*b from ⟨b,rfl⟩))
        have Pb := Hb hb' (hc.coprime_dvd_right (show b ∣ a*b from ⟨a,Nat.mul_comm a b⟩))
        exact (Pa.prod Pb).map (ZMod.chineseRemainder hab).symm.toRingHom
          (ZMod.chineseRemainder hab).symm.injective
      · have hb1 : b=1 := by omega
        subst b
        rw [mul_one]; exact Ha ha' (by simpa only [mul_one] using hc)
    · have ha1 : a=1 := by omega
      subst a
      rw [one_mul]; exact Hb (by simpa only [one_mul] using h)
        (by simpa only [one_mul] using hc)

theorem zmod_exact_cast {n : Nat} [CharP R n] (h : Exact s p (ZMod n)) :
    Exact s p R := h.map (ZMod.castHom (dvd_refl n) R) (ZMod.castHom_injective R)

/-- A literal Bézout certificate selects one unit denominator in a local
ring. It does not require Hensel lifting or a positive characteristic. -/
theorem select_unit_denominator [IsLocalRing R] (terms : List (Int × Nat))
    {g : Nat}
    (h : (terms.map (fun t => t.1 * (t.2 : Int))).sum = (g : Int))
    (hu : IsUnit (g : R)) :
    ∃ z : Int × Nat, z ∈ terms ∧ IsUnit (z.2 : R) := by
  have map_sum (L : List (Int × Nat)) :
      ((L.map (fun t => t.1 * (t.2 : Int))).sum : R) =
        (L.map (fun t => (t.1 : R) * (t.2 : R))).sum := by
    induction L with
    | nil => simp
    | cons a ts ih => simp [ih]
  have hc : IsUnit ((terms.map (fun t => (t.1 : R) * (t.2 : R))).sum) := by
    rw [←map_sum, h, Int.cast_natCast]
    exact hu
  clear h hu map_sum
  induction terms with
  | nil => simp at hc
  | cons a ts ih =>
    simp only [List.map_cons, List.sum_cons] at hc
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc with hd | hts
    · exact ⟨a, List.mem_cons_self, ((Commute.all _ _).isUnit_mul_iff.mp hd).2⟩
    · obtain ⟨t, ht, hu⟩ := ih hts
      exact ⟨t, List.mem_cons_of_mem _ ht, hu⟩

/-- Soundly select from a list of exact tableau charts over a local ring. -/
theorem local_exact_of_denominators [IsLocalRing R] (terms : List (Int × Nat))
    {g : Nat}
    (h : (terms.map (fun t => t.1 * (t.2 : Int))).sum = (g : Int))
    (hu : IsUnit (g : R))
    (charts : ∀ z ∈ terms, IsUnit (z.2 : R) → Exact s p R) : Exact s p R := by
  obtain ⟨z, hz, hunit⟩ := select_unit_denominator terms h hu
  exact charts z hz hunit

/-- A verified local-ring existence theorem already suffices for every
finite characteristic coprime to the integer inverted by that theorem.
The target need not itself be local. -/
theorem positive_characteristic_of_local (P n : Nat) [CharP R n]
    (hn : 1 < n) (hc : P.Coprime n)
    (localWitness : ∀ (T : Type) [CommRing T] [IsLocalRing T],
      IsUnit (P : T) → Exact s p T) : Exact s p R := by
  apply zmod_exact_cast
  apply zmod_exact_of_prime_powers P _ n hn hc
  intro q k hq hk hcop
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact localWitness _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop)

private theorem coprime_of_isUnit {a n : Nat} [CharP R n] (hn : 0 < n)
    (hu : IsUnit (a : R)) : a.Coprime n := by
  let g := Nat.gcd a n
  have hg : IsUnit (g : R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.gcd_dvd_left a n)) hu
  obtain ⟨t,hn'⟩ := Nat.gcd_dvd_right a n
  change n = g*t at hn'
  have ht₀ : 0 < t := by
    by_contra! hh
    have ht : t = 0 := by omega
    simp [ht] at hn'
    omega
  have hr : (g : R)*(t : R)=0 := by
    rw [←Nat.cast_mul,←hn']
    exact (CharP.cast_eq_zero_iff R n n).mpr dvd_rfl
  have ht := (CharP.cast_eq_zero_iff R n t).mp (hg.mul_right_eq_zero.mp hr)
  have hle := Nat.le_of_dvd ht₀ ht
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hn
  change g=1
  by_contra! hn
  have hlt : 1*t < g*t := Nat.mul_lt_mul_of_pos_right (by omega) ht₀
  rw [one_mul,←hn'] at hlt
  omega

/-- If the local theorem assumes that one integer is a unit, the
same assumption suffices over every nonzero finite characteristic. -/
theorem positive_characteristic_of_local_unit [Nontrivial R] (P n : Nat)
    [CharP R n] (hn : 0 < n) (hu : IsUnit (P : R))
    (localWitness : ∀ (T : Type) [CommRing T] [IsLocalRing T],
      IsUnit (P : T) → Exact s p T) : Exact s p R := by
  have h1 : n ≠ 1 := by
    intro eq
    have h := (CharP.cast_eq_zero_iff R n n).mpr dvd_rfl
    rw [eq, Nat.cast_one] at h
    exact one_ne_zero h
  exact positive_characteristic_of_local P n (by omega)
    (coprime_of_isUnit hn hu) localWitness

end RKResearch.Certified.ExactExplicitPortfolio
#print axioms RKResearch.Certified.ExactExplicitPortfolio.select_unit_denominator
#print axioms RKResearch.Certified.ExactExplicitPortfolio.positive_characteristic_of_local
#print axioms RKResearch.Certified.ExactExplicitPortfolio.zmod_exact_cast
#print axioms RKResearch.Certified.ExactExplicitPortfolio.zmod_exact_of_prime_powers

#print axioms RKResearch.Certified.ExactExplicitPortfolio.positive_characteristic_of_local_unit
#print axioms RKResearch.Certified.ExactExplicitPortfolio.local_exact_of_denominators
