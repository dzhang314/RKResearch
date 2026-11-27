module

public import RKCert.ReviewedNative.ERK8RationalEleven
public import RKCert.ReviewedNative.ERK8LocalPortfolio1
public import RKCert.ReviewedNative.ERK8LocalPortfolio2
public import RKCert.ReviewedNative.ERKUniform
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

/-! # Eleven-stage order eight over local rings and in positive characteristic

The explicit charts have a factorial-smooth denominator gcd. Selecting a
unit denominator uses locality; the characteristic-n theorem instead glues
over prime-power factors by the Chinese remainder theorem. These theorems
do not assert one chart over the generic factorial localization. -/

namespace RKResearch.Certified.ERK8LocalPortfolio

open FiniteRootedTree
open scoped Matrix

abbrev D₀ : Int := ERK8RationalEleven.D
abbrev D₁ : Nat := ERK8LocalPortfolio1.D
abbrev D₂ : Nat := ERK8LocalPortfolio2.D

def e₀ : Int := 28555822304347883951322747095317877461064755181802741912892378986364365683576620356639512629841474004760019680175279338712498123134890234881265582659359629500575305455194722013435980804072553074581446465951343267359062538114719430971278297675852974219040965711800226217980224894032014743430768208294665573927163081711511788478364356994975827559002964911931353003654177527465238854080169976801328351088519493921145574544555889665697685412756516927338380557996207864653183109457674865589690504719702398210170655306107650722300511568499032899188572259436507049662002686563247219763455035442714658027930383136127774211334536346685617473035214090714601484916978098540158226747324791682829867087023511216240721595955896130310849814014720248342020092818605713714182251337797181972560522067271218491145997694147459644008589885156893585099108890638519939023333035911435946492849937613596998252863955788966841236993217728944506676067122931651278504333379006493107837975534465557065925971983138801757191111908281355710653106233961451336734681329257425531875387584165585574879566861006555026443010570642226891739134902814552523898387508659279462073815483956145848121408017549094201370034920339834243475113035552260384698827143476735949576672782488059961746020599779377196244913383060432258921552892
def e₁ : Int := -216063284722078318814622260070048979073176865131570200583234574467038567258150060156110220588953661079280812666582291309624389468095785282774073201102806154103837480390923630653438867808534458101371764192669803761297053138502131149596376951125999336233426165882533403751596275451430307228441
def e₂ : Int := -595386567146034213008893

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem denominator_bezout :
    e₀ * D₀ + (e₁ * (D₁ : Int) + e₂ * (D₂ : Int)) = 6970199040 := by decide +kernel

def Paid (R : Type*) [CommRing R] : Prop :=
  ∃ A : Matrix (Fin 11) (Fin 11) R, ∃ b : Fin 11 → R, ERK A ∧ HasOrder 8 A b

def Exact (R : Type*) [CommRing R] : Prop :=
  ∃ A : Matrix (Fin 11) (Fin 11) R, ∃ b : Fin 11 → R,
    ERK A ∧ HasOrder 8 A b ∧ ¬ HasOrder 9 A b

variable {R S : Type*} [CommRing R] [CommRing S]

theorem Paid.exact [Nontrivial R] (h : Paid R) : Exact R := by
  obtain ⟨A,b,ha,ho⟩ := h
  refine ⟨A,b,ha,ho,?_⟩
  intro hn
  have e := hn.erk_uniform_stages (fun i j hij => ha hij)
  norm_num at e

theorem Paid.map (h : Paid R) (f : R →+* S) : Paid S := by
  obtain ⟨A,b,ha,ho⟩ := h
  refine ⟨A.map f, f ∘ b, ?_, ho.map f⟩
  intro i j hij
  change f (A i j) = 0
  rw [ha hij, map_zero]

private theorem fst_hom (z : R × S) : z.1 = (RingHom.fst R S) z := rfl
private theorem snd_hom (z : R × S) : z.2 = (RingHom.snd R S) z := rfl

theorem Paid.prod (h : Paid R) (k : Paid S) : Paid (R × S) := by
  obtain ⟨A,b,ha,hA⟩ := h
  obtain ⟨B,c,hb,hB⟩ := k
  let T : Matrix (Fin 11) (Fin 11) (R × S) := Matrix.of fun i j => (A i j, B i j)
  let w : Fin 11 → R × S := fun i => (b i, c i)
  refine ⟨T, w, ?_, ?_⟩
  · intro i j hij
    exact Prod.ext (ha hij) (hb hij)
  · intro t ht
    apply Prod.ext
    · rw [fst_hom, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hA t ht
    · rw [snd_hom, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hB t ht

private theorem select_denom [IsLocalRing R] (h : IsUnit (Nat.factorial 8 : R)) :
    IsUnit (D₀ : R) ∨ IsUnit (D₁ : R) ∨ IsUnit (D₂ : R) := by
  have hdiv : 6970199040 ∣ (Nat.factorial 8)^5 := by decide
  have hunit : IsUnit (6970199040 : R) := by
    have hp : IsUnit (((Nat.factorial 8)^5 : Nat) : R) := by
      simpa only [Nat.cast_pow] using h.pow 5
    simpa only [Nat.cast_ofNat] using isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := R) hdiv) hp
  have e := congrArg (fun z : Int => (z : R)) denominator_bezout
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at e
  rw [←e] at hunit
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with h₀ | h₁₂
  · exact Or.inl ((Commute.all _ _).isUnit_mul_iff.mp h₀).2
  · rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h₁₂ with h₁ | h₂
    · exact Or.inr (Or.inl ((Commute.all _ _).isUnit_mul_iff.mp h₁).2)
    · exact Or.inr (Or.inr ((Commute.all _ _).isUnit_mul_iff.mp h₂).2)

private theorem base_paid (h : IsUnit (D₀ : R)) : Paid R := by
  obtain ⟨u, hu⟩ := h
  let d : R := ↑(u⁻¹)
  have hd : (D₀ : R) * d = 1 := by rw [←hu]; exact Units.mul_inv u
  exact ⟨ERK8RationalEleven.A d, ERK8RationalEleven.b d,
    ERK8RationalEleven.explicit d, ERK8RationalEleven.order_eight d hd⟩

private theorem base_den_cast (S : Type*) [CommRing S] :
    (D₀.natAbs : S) = (D₀ : S) := by
  have h : (D₀.natAbs : Int) = D₀ := by decide +kernel
  simpa only [Int.cast_natCast] using congrArg (fun z : Int => (z : S)) h

private theorem lift_unit_prime_pow {p k a : Nat} (h : IsUnit (a : ZMod p)) :
    IsUnit (a : ZMod (p^k)) := by
  exact (ZMod.isUnit_iff_coprime _ _).mpr (((ZMod.isUnit_iff_coprime _ _).mp h).pow_right _)

/-- A local coefficient ring only needs to invert the factorial. -/
theorem local_paid [IsLocalRing R] (h : IsUnit (Nat.factorial 8 : R)) : Paid R := by
  rcases select_denom h with h₀ | h₁ | h₂
  · exact base_paid h₀
  · exact ERK8LocalPortfolio1.exists_order_eight_of_denom_unit h₁
  · exact ERK8LocalPortfolio2.exists_order_eight_of_denom_unit h₂

theorem local_exact [IsLocalRing R] (h : IsUnit (Nat.factorial 8 : R)) :
    Exact R := (local_paid h).exact

/-- A possibly composite positive characteristic is a product of local
prime-power coefficient rings; the eleven original slots are shared. -/
theorem zmod_paid :
    ∀ n : Nat, 0 < n → (Nat.factorial 8).Coprime n → Paid (ZMod n) := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n => 0 < n → (Nat.factorial 8).Coprime n → Paid (ZMod n)) ?_ ?_ ?_ ?_
  · intro p k hp hk _ hcop
    let _ : Fact p.Prime := ⟨hp⟩
    have hm : IsUnit (Nat.factorial 8 : ZMod p) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hcop.coprime_dvd_right (dvd_pow_self p hk.ne'))
    rcases select_denom hm with h₀ | h₁ | h₂
    · rw [←base_den_cast (ZMod p)] at h₀
      exact base_paid (by rw [←base_den_cast]; exact lift_unit_prime_pow h₀)
    · exact ERK8LocalPortfolio1.exists_order_eight_of_denom_unit (lift_unit_prime_pow h₁)
    · exact ERK8LocalPortfolio2.exists_order_eight_of_denom_unit (lift_unit_prime_pow h₂)
  · omega
  · intro _ _
    refine ⟨0,0,?_,?_⟩
    · intro i j hij; simp
    · intro t ht; exact Subsingleton.elim _ _
  · intro a b ha hb hcop Hₐ Hᵦ _ hc
    have Pa := Hₐ (by omega) (hc.coprime_dvd_right (show a ∣ a*b from ⟨b,rfl⟩))
    have Pb := Hᵦ (by omega) (hc.coprime_dvd_right (show b ∣ a*b from ⟨a,Nat.mul_comm a b⟩))
    exact (Pa.prod Pb).map (ZMod.chineseRemainder hcop).symm.toRingHom

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

theorem positive_characteristic_exact [Nontrivial R] (n : Nat) [CharP R n]
    (hn : 0 < n) (h : IsUnit (Nat.factorial 8 : R)) : Exact R :=
  ((zmod_paid n hn (coprime_of_isUnit hn h)).map (ZMod.castHom (dvd_refl n) R)).exact

end RKResearch.Certified.ERK8LocalPortfolio

#print axioms RKResearch.Certified.ERK8LocalPortfolio.local_exact
#print axioms RKResearch.Certified.ERK8LocalPortfolio.positive_characteristic_exact
