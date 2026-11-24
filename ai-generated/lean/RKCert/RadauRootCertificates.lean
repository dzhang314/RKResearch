module
public import RKCert.RootTupleSpecialization
public import RKCert.LobattoFactorTables
public import RKCert.ERKOrderNineRadau

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial RKCert.Paired
universe u v
variable {ι : Type v} {K : Type u} [Field K] [CharZero K]

def radauDigits : List ℤ := [10001880,-952560,26460,-280,1]
noncomputable def radauIntegral := intHorner radauDigits
def radauKnots : List (ZMod 191) := [45,57,80,98]
instance prime191 : Fact (Nat.Prime 191) := ⟨by decide +kernel⟩

theorem degree_radau_integral : radauIntegral.natDegree=4 := by
  apply le_antisymm (degree_horner_le radauDigits 4 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner radauDigits).coeff 4 ≠ 0
  rw [coeff_horner]; decide

theorem monic_radau_integral : radauIntegral.Monic := by
  rw [Monic,leadingCoeff,degree_radau_integral,radauIntegral,coeff_horner]; decide

theorem split_radau191 :
    radauIntegral.map (Int.castRingHom (ZMod 191))=linearProduct id radauKnots := by
  apply z_grid_split _ _ (by decide); intro i hi
  change i≤4 at hi; interval_cases i <;> decide

theorem scaled_radau_eval (x : K) : (radauIntegral.map (Int.castRingHom K)).eval (126*x)=
    126^4*(radauQuartic.eval x) := by
  norm_num [radauIntegral,radauDigits,intHorner,radauQuartic]
  ring

/-- An explicit integer polynomial test on the 126-scaled Radau roots, with
arbitrary pairwise distinction requirements. It suffices to check only the
split root set in the prime field, even when K is nonordered. -/
theorem radau_root_certificate_at (p : ℕ) [Fact p.Prime] (knots : List (ZMod p))
    (split : radauIntegral.map (Int.castRingHom (ZMod p))=linearProduct id knots)
    (nd : knots.Nodup) (test : MvPolynomial ι ℤ) (mask : ι→ι→Prop)
    (check : ∀z : ι→ZMod p, (∀i, z i∈knots) →
      (∀i j, mask i j → z i≠z j) → zEval test z≠0)
    (w : ι→K) (roots : ∀i, radauQuartic.eval (w i)=0)
    (distinct : ∀i j, mask i j → w i≠w j) :
    zEval test (fun i=>126*w i)≠0 := by
  apply split_prime_root_tuple p radauIntegral monic_radau_integral knots
    split _ test mask check
  · intro i
    rw [scaled_radau_eval,roots,mul_zero]
  · intro i j e
    exact fun d=>distinct i j e (mul_left_cancel₀ (by norm_num : (126:K)≠0) d)
  · intro a ha
    rw [split]
    exact simple_product_of_nodup _ nd ha

theorem radau_root_certificate (test : MvPolynomial ι ℤ) (mask : ι→ι→Prop)
    (check : ∀z : ι→ZMod 191, (∀i, z i∈radauKnots) →
      (∀i j, mask i j → z i≠z j) → zEval test z≠0)
    (w : ι→K) (roots : ∀i, radauQuartic.eval (w i)=0)
    (distinct : ∀i j, mask i j → w i≠w j) :
    zEval test (fun i=>126*w i)≠0 :=
  radau_root_certificate_at 191 radauKnots split_radau191 (by decide) test mask check w roots distinct

def radauKnots353 : List (ZMod 353) := [41,111,161,320]
instance prime353 : Fact (Nat.Prime 353) := ⟨by decide +kernel⟩
theorem split_radau353 :
    radauIntegral.map (Int.castRingHom (ZMod 353))=linearProduct id radauKnots353 := by
  apply z_grid_split _ _ (by decide); intro i hi
  change i≤4 at hi; interval_cases i <;> decide

theorem radau_root_certificate353 (test : MvPolynomial ι ℤ) (mask : ι→ι→Prop)
    (check : ∀z : ι→ZMod 353, (∀i, z i∈radauKnots353) →
      (∀i j, mask i j → z i≠z j) → zEval test z≠0)
    (w : ι→K) (roots : ∀i, radauQuartic.eval (w i)=0)
    (distinct : ∀i j, mask i j → w i≠w j) :
    zEval test (fun i=>126*w i)≠0 :=
  radau_root_certificate_at 353 radauKnots353 split_radau353 (by decide) test mask check w roots distinct

noncomputable def radauTriplePoly : MvPolynomial (Fin 3) ℤ :=
  3*(MvPolynomial.X 2)^2-4*(MvPolynomial.X 0+MvPolynomial.X 1)*MvPolynomial.X 2+
  6*MvPolynomial.X 0*MvPolynomial.X 1

theorem eval_triple {S : Type*} [CommRing S] (z : Fin 3→S) :
    zEval radauTriplePoly z=3*(z 2)^2-4*(z 0+z 1)*z 2+6*z 0*z 1 := by
  simp [zEval,radauTriplePoly]

theorem checked_radau_triples : radauKnots.all (fun a=>radauKnots.all (fun b=>
    radauKnots.all fun h=>decide (3*h^2-4*(a+b)*h+6*a*b≠0)))=true := by decide +kernel

/-- The paper only requires three distinct root sites; in fact the same
nonvanishing holds at all 4³ triples, without a single distinction premise. -/
theorem radau_triple {a b h : K} (ha : radauQuartic.eval a=0) (hb : radauQuartic.eval b=0)
    (hh : radauQuartic.eval h=0) : 3*h^2-4*(a+b)*h+6*a*b ≠0 := by
  let w : Fin 3→K := ![a,b,h]
  have cert := radau_root_certificate radauTriplePoly (fun _ _=>False) (fun z mem _=>by
    rw [eval_triple]
    have t0 := List.all_eq_true.mp checked_radau_triples _ (mem 0)
    have t1 := List.all_eq_true.mp t0 _ (mem 1)
    exact of_decide_eq_true (List.all_eq_true.mp t1 _ (mem 2))) w
    (by intro i; fin_cases i <;> first | exact ha | exact hb | exact hh)
    (fun _ _ h'=>h'.elim)
  rw [eval_triple] at cert
  intro e
  apply cert
  change 3*(126*h)^2-4*(126*a+126*b)*(126*h)+6*(126*a)*(126*b)=0
  linear_combination 126^2*e

end RKCert.FixedFactor
