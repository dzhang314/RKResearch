module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA6From0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA6From2
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA6From4
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA7From0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA7From2
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA7From4
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA7From6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA8From0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA8From2
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA8From4
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA8From6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA8From8
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A6 : blockA 6 = true := by
  apply List.all_eq_true.mpr
  intro i _
  have he : packet.size 6 = 5 := by decide +kernel
  obtain ⟨j, hj⟩ : ∃ j : Fin 5, Fin.cast he.symm j = i :=
    ⟨Fin.cast he i, Fin.ext rfl⟩
  rw [←hj]
  fin_cases j
  · exact chk_A6i0
  · exact chk_A6i1
  · exact chk_A6i2
  · exact chk_A6i3
  · exact chk_A6i4
theorem chk_A7 : blockA 7 = true := by
  apply List.all_eq_true.mpr
  intro i _
  have he : packet.size 7 = 8 := by decide +kernel
  obtain ⟨j, hj⟩ : ∃ j : Fin 8, Fin.cast he.symm j = i :=
    ⟨Fin.cast he i, Fin.ext rfl⟩
  rw [←hj]
  fin_cases j
  · exact chk_A7i0
  · exact chk_A7i1
  · exact chk_A7i2
  · exact chk_A7i3
  · exact chk_A7i4
  · exact chk_A7i5
  · exact chk_A7i6
  · exact chk_A7i7
theorem chk_A8 : blockA 8 = true := by
  apply List.all_eq_true.mpr
  intro i _
  have he : packet.size 8 = 9 := by decide +kernel
  obtain ⟨j, hj⟩ : ∃ j : Fin 9, Fin.cast he.symm j = i :=
    ⟨Fin.cast he i, Fin.ext rfl⟩
  rw [←hj]
  fin_cases j
  · exact chk_A8i0
  · exact chk_A8i1
  · exact chk_A8i2
  · exact chk_A8i3
  · exact chk_A8i4
  · exact chk_A8i5
  · exact chk_A8i6
  · exact chk_A8i7
  · exact chk_A8i8

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
