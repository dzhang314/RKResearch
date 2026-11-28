import Mathlib.Tactic.Ring.Basic

/-! Split-free paired-star scalar gate, without dividing any physical weight. -/

namespace RKResearch.Certified.SDIRKEightEightZeroStarEqualCardinal

variable {R : Type*} [CommRing R]

theorem split_free_cleared {g w d Bp Bq j m : R}
    (h₀ : w*d=g*(Bp-Bq)) (h₁ : w*j=g*m) :
    g*((Bp-Bq)*j-d*m)=0 := by
  calc
    _ = (g*(Bp-Bq))*j-d*(g*m) := by ring1
    _ = 0 := by rw [← h₀, ← h₁]; ring1

theorem split_free [IsDomain R] {g w d Bp Bq j m : R}
    (hg : g ≠ 0) (h₀ : w*d=g*(Bp-Bq)) (h₁ : w*j=g*m) :
    (Bp-Bq)*j=d*m := by
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp (split_free_cleared h₀ h₁)).resolve_left hg

theorem equal_cardinal_mean [IsDomain R] {g w d Bp Bq j m : R}
    (hg : g ≠ 0) (hd : d ≠ 0) (hb : Bp=Bq)
    (h₀ : w*d=g*(Bp-Bq)) (h₁ : w*j=g*m) : m=0 := by
  have h := split_free hg h₀ h₁
  rw [hb,sub_self,zero_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hd

end RKResearch.Certified.SDIRKEightEightZeroStarEqualCardinal
