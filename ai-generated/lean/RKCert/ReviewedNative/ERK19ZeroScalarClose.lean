module

public import RKCert.ReviewedNative.ERK19ZeroGlobalLocation
public import RKCert.ReviewedNative.ERK19ZeroLocalWindows

@[expose] public section

namespace RKCert.ReviewedNative.ERK19ZeroScalar

open Polynomial
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem opposed_quintic_windows_impossible {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) : False := by
  obtain ⟨ha, hd, hb, hc⟩ := opposed_quintic_clock_location H
  exact OpposedQuinticWindows.local_impossible H ha hd hb hc

end RKCert.ReviewedNative.ERK19ZeroScalar
