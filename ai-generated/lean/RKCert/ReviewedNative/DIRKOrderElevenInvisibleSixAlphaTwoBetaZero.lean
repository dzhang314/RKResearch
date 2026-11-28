import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoBetaZero

/-- Undivided fifth-clean gate with exactly two nonzero weighted input
coordinates available in reverse, and fourth diagonal already zero. -/
theorem adjacent_gate {K : Type*} [CommRing K] [IsDomain K]
    {u s F p d Δ tap J : K}
    (hp : p≠0) (hS : u*s=F*p) (hJ : d*u=J)
    (hT : tap=s-d*p) (hC : (Δ-d)*tap=d^2*p) :
    (Δ*u-J)*F-Δ*J*u=0 := by
  have hc : (Δ-d)*s-Δ*d*p=0 := by
    linear_combination hC-(Δ-d)*hT
  have h : p*((Δ*u-J)*F-Δ*J*u)=0 := by
    calc
      p*((Δ*u-J)*F-Δ*J*u) =
          ((Δ*u-J)*(F*p)-Δ*J*u*p) := by ring
      _ = u^2*((Δ-d)*s-Δ*d*p) := by
        rw [← hS,← hJ]
        ring
      _ = 0 := by rw [hc,mul_zero]
  exact (mul_eq_zero.mp h).resolve_left hp

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoBetaZero
