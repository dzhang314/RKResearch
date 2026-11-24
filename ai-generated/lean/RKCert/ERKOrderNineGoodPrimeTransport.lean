module

public import RKCert.ERKOrderNineGoodPrimeTerminal
public import Mathlib.RingTheory.Localization.Away.Basic
public import RKCert.IntegralFactorGate

@[expose] public section

/-! # Naturality and characteristic-zero interpretation of the terminal gate -/

namespace RKCert.GoodPrimeDense
open Polynomial RKCert.Paired RKCert.Endpoint

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_pencilAt (f : R→+*S) (l d : R) :
    (pencilAt l d).map f = pencilAt (f l) (f d) := by
  simp [pencilAt,Four.map,map_ofNat]

theorem RootSystem.map {q : Four R} {h u v : R} (hs : RootSystem q h u v)
    (f : R→+*S) : RootSystem (q.map f) (f h) (f u) (f v) := by
  refine ⟨?_,?_,?_⟩
  · simpa [Four.map,Four.eval] using congrArg f hs.four
  · simpa [Four.map,Four.eval,Four.shifted,Three.eval] using congrArg f hs.three
  · simpa [Four.map,Four.eval,Four.shifted,Three.eval,Three.shifted,Two.eval] using congrArg f hs.two

theorem map_terminalAt (f : R→+*S) (h u v l d : R) :
    f (terminalAt h u v l d) = terminalAt (f h) (f u) (f v) (f l) (f d) := by
  classical
  have eq : terminalRecipe (scalar R) h u v l d = terminalAt h u v l d :=
    eval_terminalRecipe (Sound.scalar (RingHom.id R)) h u v l d
  rw [←eq]
  exact eval_terminalRecipe (Sound.scalar f) h u v l d

variable {K : Type*} [Field K] [CharZero K]

theorem cubicAt_legacy (z : K) :
    cubicAt ((84:K)⁻¹) z = RKCert.Paired.lobattoCubic.eval z := by
  simp [cubicAt,RKCert.Paired.lobattoCubic]
  ring

theorem fAt_legacy (u v : K) (P : K→K) :
    fAt ((84:K)⁻¹) u v P = sixOnF u v P := by
  simp [fAt,sixOnF,radauLateD,cubicAt_legacy]

theorem hatPolyAt_legacy (h u v : K) :
    hatPolyAt h u v ((84:K)⁻¹) = sixOnHat h u v := by
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp [hatPolyAt,hatAt,ofCoeffList_cons,sixOnHat,sixOnP0,sixOnP1,
    fAt_legacy,show p0At h=fixedRadauP0 h from rfl,show p1At h=fixedRadauP1 h from rfl]
  ring

omit [CharZero K] in
theorem portAt_legacy (u v : K) : ofCoeffList (portAt u v) = sixOnPort u v := by
  simp [portAt,ofCoeffList_cons,sixOnPort,sub_eq_add_neg,add_comm,mul_comm]

theorem qAt_legacy (l : K) : qAt l ((84:K)⁻¹) = X*lobattoPencil l := by
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp [qAt,pencilAt,ofCoeffList_cons,lobattoPencil]
  ring_nf
  simp

theorem w5At_legacy (h u v : K) :
    w5At h u v = sixOnPort u v*(X^2*(X-C h)^2) := by
  rw [w5At,portAt_legacy]
  congr 1
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp [ofCoeffList_cons]
  ring

theorem w6At_legacy (u v : K) (p : K[X]) (hp : p.natDegree ≤ 2) :
    w6At u v ((84:K)⁻¹) p = sixOnPort u v * primitive (X*p) := by
  rw [w6At,portAt_legacy]
  congr 1
  ext n
  by_cases hn : n≤4
  · interval_cases n <;> norm_num [List.getD_eq_getElem?_getD,coeff_X_mul_zero,coeff_X_mul,
      primitive_coeff_zero,primitive_coeff_succ] <;> ring
  · rw [coeff_ofCoeffList]
    have hz : (primitive (X*p)).natDegree ≤ 4 := by
      apply primitive_natDegree_le
      apply natDegree_mul_le_of_le ?_ hp
      simp
    rw [coeff_eq_zero_of_natDegree_lt (by omega : (primitive (X*p)).natDegree < n)]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by change 5≤n; omega)]
    rfl

omit [CharZero K] in
theorem pseudoAt_legacy (p w : K[X]) : pseudoAt p w = quadraticPrem5 p w := rfl

theorem terminalAt_legacy (h u v l : K) :
    terminalAt h u v l ((84:K)⁻¹) = sixOnTerminalProduct h u v l := by
  unfold terminalAt sixOnTerminalProduct sixOnO5 sixOnO6
  dsimp only
  rw [hatPolyAt_legacy, qAt_legacy, w5At_legacy,
    w6At_legacy _ _ _ (sixOnHat_degree ..)]
  simp only [detAt,pseudoAt_legacy,quadraticPremDet,sixOnHc,hcAt,fAt_legacy,
    show p0At h=fixedRadauP0 h from rfl,show p1At h=fixedRadauP1 h from rfl,
    sixOnCollisionA2,sixOnCollisionA1,sixOnCollisionA0]

end RKCert.GoodPrimeDense
