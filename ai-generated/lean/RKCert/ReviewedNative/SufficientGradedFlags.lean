module

public import RKCert.ReviewedNative.GradedColumns
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

@[expose] public section

/-! A denominator-free sufficient flag criterion for the full reviewed
rooted-tree order. The concrete family of submodules can be supplied
without first proving that each band is the complete actual defect space. -/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {ι R : Type*} [Fintype ι] [CommRing R]

structure SufficientFlags (p : Nat) (A : Matrix ι ι R) (b : ι → R) where
  band : Nat → Submodule R (ι → R)
  stepA : ∀ {d} (_hd : d+1 < p) {v}, v ∈ band d → mat A v ∈ band (d+1)
  stepC : ∀ {d} (_hd : d+1 < p) {v}, v ∈ band d → nodes A * v ∈ band (d+1)
  mulBand : ∀ {d e} (_hd : d+e < p) {v w}, v ∈ band d → w ∈ band e → v*w ∈ band (d+e)
  primitive : ∀ d, d+1 < p →
    ((d+1 : Nat) : R) • mat A ((nodes A)^d) - (nodes A)^(d+1) ∈ band (d+1)
  silent : ∀ {d} (_hd : d < p) {v}, v ∈ band d → row b v = 0
  scalar : ∀ d, d < p → ((d+1 : Nat) : R) * row b ((nodes A)^d) = 1

namespace SufficientFlags

variable {p : Nat} {A : Matrix ι ι R} {b : ι → R}
variable (S : SufficientFlags p A b)

theorem clockPow {d : Nat} {v : ι → R} (hv : v ∈ S.band d) (k : Nat)
    (hk : d+k < p) : (nodes A)^k*v ∈ S.band (d+k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    have h := S.stepC (d:=d+k) (by omega) (ih (by omega))
    rw [pow_succ', mul_assoc]
    exact h

theorem normalized_join (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    normTree A (t ◂ u) =
      normTree A t * (((u.order : Nat) : R) • mat A (normTree A u)) := by
  ext i
  simp only [normTree, forestFactorial, PNat.mul_coe, Nat.cast_mul, Φ,
    mat_apply, Matrix.mulVec_smul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ac_rfl

theorem defect_mem (t : FiniteRootedTree) (ht : (t.order : Nat) ≤ p) :
    normTree A t - (nodes A)^((t.order : Nat)-1) ∈ S.band ((t.order : Nat)-1) := by
  induction t with
  | leaf => simp [order]
  | butcherProduct t u iht ihu =>
    let d := (t.order : Nat)-1
    let e := (u.order : Nat)-1
    have pt := t.order.pos
    have pu := u.order.pos
    have o : ((t ◂ u).order : Nat)-1 = d+(e+1) := by
      simp only [order, PNat.add_coe, d, e]
      omega
    have bound : d+(e+1) < p := by
      simp only [order, PNat.add_coe] at ht
      dsimp [d,e]
      omega
    have ht' : (t.order : Nat) ≤ p := by dsimp [d,e] at bound; omega
    have hu' : (u.order : Nat) ≤ p := by dsimp [d,e] at bound; omega
    have eu : (u.order : Nat)=e+1 := by dsimp [e]; omega
    let c := nodes A
    let v := normTree A t-c^d
    let w := ((e+1 : Nat):R) • mat A (normTree A u)-c^(e+1)
    have hv : v ∈ S.band d := iht ht'
    have hw₀ : normTree A u-c^e ∈ S.band e := ihu hu'
    have hw₁ := S.stepA (d:=e) (by omega) hw₀
    have hw₂ := S.primitive e (by omega)
    have hw : w ∈ S.band (e+1) := by
      have z := (S.band (e+1)).add_mem hw₂
        ((S.band (e+1)).smul_mem (((e+1 : Nat):R)) hw₁)
      convert z using 1
      dsimp [w,c]
      rw [Matrix.mulVec_sub, smul_sub]
      abel
    have hvc : c^(e+1)*v ∈ S.band (d+(e+1)) :=
      S.clockPow hv (e+1) bound
    have hwc : c^d*w ∈ S.band (d+(e+1)) := by
      simpa [Nat.add_comm] using S.clockPow hw d (by omega)
    have hp : v*w ∈ S.band (d+(e+1)) := S.mulBand bound hv hw
    rw [o, normalized_join, eu]
    have identify : normTree A t * (((e+1 : Nat):R) • mat A (normTree A u)) -
        c^(d+(e+1)) = c^d*w + c^(e+1)*v + v*w := by
      rw [pow_add]
      dsimp [v,w,c]
      ring
    change normTree A t * (((e+1 : Nat):R) • mat A (normTree A u)) -
        c^(d+(e+1)) ∈ S.band (d+(e+1))
    rw [identify]
    exact (S.band _).add_mem ((S.band _).add_mem hwc hvc) hp

theorem hasOrder (S : SufficientFlags p A b) : HasOrder p A b := by
  intro t ht
  have pt := t.order.pos
  let d := (t.order : Nat)-1
  have hdp : d < p := by dsimp [d]; omega
  have hd : d+1 = (t.order : Nat) := by dsimp [d]; omega
  have hs := S.silent hdp (S.defect_mem t ht)
  rw [map_sub] at hs
  have eq := sub_eq_zero.mp hs
  have scalar := S.scalar d hdp
  have hf :
      row b (normTree A t) = ((t.forestFactorial : Nat) : R) * (b ⬝ᵥ Φ t A) := by
    rw [normTree, map_smul, smul_eq_mul, row_apply]
  rw [←eq, hf, hd] at scalar
  simpa only [factorial, PNat.mul_coe, Nat.cast_mul, mul_assoc] using scalar

end SufficientFlags

end RKResearch.Certified.Graded

#print axioms RKResearch.Certified.Graded.SufficientFlags.hasOrder
