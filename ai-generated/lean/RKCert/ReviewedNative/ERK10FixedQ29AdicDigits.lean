module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicResidues
public import Mathlib.Algebra.Polynomial.Identities

@[expose] public section

/-! Elementary compatible Hensel digits, independent of analytic p-adic
imports. The polynomial at each level may itself have lifted coefficients. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Digits

open Polynomial

abbrev modulus (n : ℕ) : ℕ := (29:ℕ)^(n+1)
abbrev Level (n : ℕ) := ZMod (modulus n)

instance positive (n : ℕ) : NeZero (modulus n) :=
  ⟨pow_ne_zero _ (by decide : (29:ℕ) ≠ 0)⟩

theorem modulus_succ (n : ℕ) : modulus (n+1) = modulus n*29 := by
  change (29:ℕ)^(n+1+1) = 29^(n+1)*29
  rw [pow_succ]

theorem base_dvd (n : ℕ) : 29 ∣ modulus n := by
  change (29:ℕ)^1 ∣ 29^(n+1)
  exact pow_dvd_pow _ (by omega)

theorem down_dvd (n : ℕ) : modulus n ∣ modulus (n+1) :=
  ⟨29, modulus_succ n⟩

def down (n : ℕ) : Level (n+1) →+* Level n := ZMod.castHom (down_dvd n) _
def res (n : ℕ) : Level n →+* F := ZMod.castHom (base_dvd n) _

@[simp] theorem res_zero : res 0 = RingHom.id F := Subsingleton.elim _ _

theorem res_comp_down (n : ℕ) : (res n).comp (down n) = res (n+1) :=
  ZMod.castHom_comp (base_dvd n) (down_dvd n)

@[simp] theorem res_down (n : ℕ) (z : Level (n+1)) :
    res n (down n z) = res (n+1) z :=
  DFunLike.congr_fun (res_comp_down n) z

instance local_res (n : ℕ) : IsLocalHom (res n) where
  map_nonunit z hz := by
    have hnd : ¬ 29 ∣ z.val := by
      intro h
      apply hz.ne_zero
      rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff]
      exact h
    rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
    exact ((prime29.out.coprime_iff_not_dvd.mpr hnd).symm).pow_right _

private theorem kill_residue_zero {n : ℕ} {z : Level (n+1)}
    (hz : res (n+1) z = 0) : (modulus n : Level (n+1))*z = 0 := by
  have ht : 29 ∣ z.val := by
    rwa [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at hz
  rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact (congrArg (fun M : ℕ => M ∣ modulus n * z.val) (modulus_succ n)).mpr
    (Nat.mul_dvd_mul_left (modulus n) ht)

theorem step (n : ℕ) (P : Polynomial (Level (n+1))) (r : Level n)
    (hr : (P.map (down n)).eval r = 0)
    (hd : (P.map (res (n+1))).derivative.eval (res n r) ≠ 0) :
    ∃ x : Level (n+1), P.eval x = 0 ∧ down n x = r := by
  let y : Level (n+1) := r.val
  have hy : down n y = r := by
    rw [show y = (r.val : Level (n+1)) by rfl, map_natCast, ZMod.natCast_zmod_val]
  have hpy : down n (P.eval y) = 0 := by
    rwa [← eval_map_apply, hy]
  have hvd : modulus n ∣ (P.eval y).val := by
    rw [← ZMod.natCast_eq_zero_iff, ← map_natCast (down n), ZMod.natCast_zmod_val]
    exact hpy
  obtain ⟨e, he⟩ := hvd
  have hv : P.eval y = (modulus n : Level (n+1)) * (e : Level (n+1)) := by
    rw [← ZMod.natCast_zmod_val (P.eval y), he, Nat.cast_mul]
  let D : F := res (n+1) (P.derivative.eval y)
  have hne : D ≠ 0 := by
    change res (n+1) (P.derivative.eval y) ≠ 0
    rw [← eval_map_apply, ← derivative_map, ← res_down, hy]
    exact hd
  let digit : F := -(e : F) * D⁻¹
  let z : Level (n+1) := digit.val
  have hz : res (n+1) z = digit := by
    rw [show z = (digit.val : Level (n+1)) by rfl, map_natCast, ZMod.natCast_zmod_val]
  have hlin : res (n+1) ((e : Level (n+1)) + P.derivative.eval y*z) = 0 := by
    rw [map_add, map_natCast, map_mul, hz]
    change (e:F)+D*((-(e:F))*D⁻¹) = 0
    calc
      _ = (e:F)+(-(e:F))*(D*D⁻¹) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hne, mul_one, add_neg_cancel]
  have hm : res (n+1) (modulus n : Level (n+1)) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact base_dvd n
  have hm₂ : (modulus n : Level (n+1))^2 = 0 := by
    simpa only [pow_two] using kill_residue_zero hm
  have hmm : down n (modulus n : Level (n+1)) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
  refine ⟨y + (modulus n : Level (n+1))*z, ?_, ?_⟩
  · obtain ⟨q,hq⟩ := P.binomExpansion y ((modulus n : Level (n+1))*z)
    rw [hq,hv]
    calc
      _ = (modulus n : Level (n+1))*((e:Level (n+1))+P.derivative.eval y*z)
          + q*(modulus n : Level (n+1))^2*z^2 := by ring
      _ = 0 := by rw [kill_residue_zero hlin, hm₂, mul_zero, zero_mul, add_zero]
  · simp only [map_add, map_mul, hmm, zero_mul, add_zero, hy]

end RKResearch.Certified.ERK10FixedQ29Adic.Digits

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Digits.step
