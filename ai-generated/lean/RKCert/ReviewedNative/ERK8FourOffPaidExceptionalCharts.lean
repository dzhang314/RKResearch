module

public import RKCert.ReviewedNative.ERK8FourOffPaidGenericGuards
public import Mathlib.Algebra.CharP.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal specializations at the five exceptional outside-eleven primes
Each reduction is an integer polynomial identity after multiplying
by a power of the paid primes. There are no point-search assumptions. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K]

theorem castNe_of_prime_char {p n : ℕ} (pp : p.Prime) (hz : (p:K)=0)
    (hn : ¬p∣n) : (n:K)≠0 := by
  haveI := (CharP.charP_iff_prime_eq_zero pp).mpr hz
  exact fun h=>hn ((CharP.cast_eq_zero_iff K p n).mp h)

theorem chart_tests_mod_17 [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (hp : (17:K)=0) (o : CleanOrientation) : ChartResult o u := by
  have roots : (u-(4:K))*(u-(14:K))=0 := by
    apply mul_left_cancel₀ (seven_paid K)
    rw [mul_zero]
    linear_combination hq+((-7:K)*u+(23:K))*hp
  cases o
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(4:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(4:K))=(2:K) by
          linear_combination (5:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(4:K))=(8:K) by
          linear_combination (3:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(4:K))=(15:K) by
          linear_combination (-11:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(4:K))=(2:K) by
          linear_combination (-3:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(4:K))=(15:K) by
          linear_combination (-5:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(4:K))=(15:K) by
          linear_combination (-255:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(4:K))=(10:K) by
          linear_combination (-12770:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(4:K))=(14:K) by
          linear_combination (-14638:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=14) (by decide) hp (by decide)
    · have ur : u=(14:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(14:K))=(8:K) by
          linear_combination (17:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(14:K))=(15:K) by
          linear_combination (12:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(14:K))=(16:K) by
          linear_combination (-44:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(14:K))=(15:K) by
          linear_combination (-12:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(14:K))=(16:K) by
          linear_combination (-38:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(14:K))=(15:K) by
          linear_combination (-975:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(14:K))=(7:K) by
          linear_combination (-58511:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(14:K))=(10:K) by
          linear_combination (-62666:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(4:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(4:K))=(16:K) by
          linear_combination (-5:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(4:K))=(15:K) by
          linear_combination (2:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(4:K))=(10:K) by
          linear_combination (-6:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(4:K))=(9:K) by
          linear_combination (2:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=9) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(4:K))=(10:K) by
          linear_combination (-36:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(4:K))=(5:K) by
          linear_combination (-373:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=5) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(4:K))=(9:K) by
          linear_combination (5679:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=9) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(4:K))=(16:K) by
          linear_combination (-10064:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=16) (by decide) hp (by decide)
    · have ur : u=(14:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(14:K))=(10:K) by
          linear_combination (-17:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(14:K))=(2:K) by
          linear_combination (11:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(14:K))=(2:K) by
          linear_combination (-22:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(14:K))=(13:K) by
          linear_combination (10:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(14:K))=(5:K) by
          linear_combination (-151:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=5) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(14:K))=(7:K) by
          linear_combination (-1559:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(14:K))=(14:K) by
          linear_combination (23594:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(14:K))=(2:K) by
          linear_combination (-42082:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(4:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(4:K))=(12:K) by
          linear_combination (24:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=12) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(4:K))=(11:K) by
          linear_combination (33:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=11) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(4:K))=(16:K) by
          linear_combination (-142:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(4:K))=(7:K) by
          linear_combination (-28:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(4:K))=(4:K) by
          linear_combination (-244:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(4:K))=(10:K) by
          linear_combination (-11834:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(4:K))=(8:K) by
          linear_combination (-57228616:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(4:K))=(7:K) by
          linear_combination (-784919:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=7) (by decide) hp (by decide)
    · have ur : u=(14:K) := sub_eq_zero.mp u0
      refine ChartResult.sharedLast ?_ ?_ ?_ ?_ ?_
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(14:K))=(15:K) by
          linear_combination (-1167:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(14:K))=(2:K) by
          linear_combination (74:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=2) (by decide) hp (by decide)
      · apply mul_left_cancel₀ (show (1:K)≠0 from one_ne_zero)
        rw [mul_zero,chartValue3b hq,ur]
        linear_combination (-594:K)*hp
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(14:K))=(4:K) by
          linear_combination (124:K)*hp]
        exact castNe_of_prime_char (p:=17) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(14:K))=(1:K) by
          linear_combination (-110:K)*hp]
        exact one_ne_zero

theorem chart_tests_mod_37 [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (hp : (37:K)=0) (o : CleanOrientation) : ChartResult o u := by
  have roots : (u-(12:K))*(u-(26:K))=0 := by
    apply mul_left_cancel₀ (seven_paid K)
    rw [mul_zero]
    linear_combination hq+((-7:K)*u+(59:K))*hp
  cases o
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(12:K) := sub_eq_zero.mp u0
      refine ChartResult.linear ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(12:K))=(33:K) by
          linear_combination (6:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=33) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(12:K))=(2:K) by
          linear_combination (5:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(12:K))=(9:K) by
          linear_combination (-17:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=9) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(12:K))=(24:K) by
          linear_combination (-5:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=24) (by decide) hp (by decide)
      · apply mul_left_cancel₀ (show (1:K)≠0 from one_ne_zero)
        rw [mul_zero,chartValue1p2 hq,ur]
        linear_combination (-14:K)*hp
      · apply scaled_ne_of_rhs_ne (chartValue1p1 hq)
        rw [ur,show ((-69:K)+(-42:K)*(12:K))=(19:K) by
          linear_combination (-16:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=19) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(12:K))=(22:K) by
          linear_combination (-382:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=22) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(26:K))=(31:K) by
          linear_combination (14:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=31) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(26:K))=(4:K) by
          linear_combination (11:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(26:K))=(2:K) by
          linear_combination (-38:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(26:K))=(13:K) by
          linear_combination (-10:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(26:K))=(30:K) by
          linear_combination (-36:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=30) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(26:K))=(17:K) by
          linear_combination (-845:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=17) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(26:K))=(11:K) by
          linear_combination (-52103:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=11) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(26:K))=(13:K) by
          linear_combination (-55273:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(12:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(12:K))=(22:K) by
          linear_combination (-7:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=22) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(12:K))=(13:K) by
          linear_combination (4:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(12:K))=(17:K) by
          linear_combination (-9:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=17) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(12:K))=(7:K) by
          linear_combination (4:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(12:K))=(13:K) by
          linear_combination (-59:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(12:K))=(32:K) by
          linear_combination (-608:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=32) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(12:K))=(22:K) by
          linear_combination (9194:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=22) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(12:K))=(13:K) by
          linear_combination (-16393:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(26:K))=(24:K) by
          linear_combination (-15:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=24) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(26:K))=(24:K) by
          linear_combination (9:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=24) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(26:K))=(32:K) by
          linear_combination (-20:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=32) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(26:K))=(18:K) by
          linear_combination (9:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=18) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(26:K))=(7:K) by
          linear_combination (-133:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(26:K))=(2:K) by
          linear_combination (-1370:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(26:K))=(18:K) by
          linear_combination (20718:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=18) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(26:K))=(17:K) by
          linear_combination (-36989:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=17) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(12:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(12:K))=(19:K) by
          linear_combination (29:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=19) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(12:K))=(28:K) by
          linear_combination (48:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=28) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(12:K))=(26:K) by
          linear_combination (-232:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=26) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(12:K))=(2:K) by
          linear_combination (-43:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(12:K))=(36:K) by
          linear_combination (-452:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=36) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(12:K))=(11:K) by
          linear_combination (-18623:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=11) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(12:K))=(19:K) by
          linear_combination (-93564055:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=19) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(12:K))=(22:K) by
          linear_combination (-1396318:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=22) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(26:K))=(11:K) by
          linear_combination (61:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=11) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(26:K))=(1:K) by
          linear_combination (107:K)*hp]
        exact one_ne_zero
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(26:K))=(13:K) by
          linear_combination (-523:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(26:K))=(3:K) by
          linear_combination (-96:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=3) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(26:K))=(25:K) by
          linear_combination (-1045:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=25) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(26:K))=(10:K) by
          linear_combination (-41698:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(26:K))=(18:K) by
          linear_combination (-211286250:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=18) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(26:K))=(4:K) by
          linear_combination (-3208756:K)*hp]
        exact castNe_of_prime_char (p:=37) (n:=4) (by decide) hp (by decide)

theorem chart_tests_mod_41 [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (hp : (41:K)=0) (o : CleanOrientation) : ChartResult o u := by
  have roots : (u-(16:K))*(u-(26:K))=0 := by
    apply mul_left_cancel₀ (seven_paid K)
    rw [mul_zero]
    linear_combination hq+((-7:K)*u+(71:K))*hp
  cases o
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(16:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(16:K))=(11:K) by
          linear_combination (8:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=11) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(16:K))=(5:K) by
          linear_combination (6:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=5) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(16:K))=(17:K) by
          linear_combination (-21:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=17) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(16:K))=(29:K) by
          linear_combination (-6:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(16:K))=(37:K) by
          linear_combination (-19:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=37) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(16:K))=(16:K) by
          linear_combination (-464:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(16:K))=(14:K) by
          linear_combination (-28054:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(16:K))=(39:K) by
          linear_combination (-29967:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=39) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(26:K))=(16:K) by
          linear_combination (13:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=16) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(26:K))=(1:K) by
          linear_combination (10:K)*hp]
        exact one_ne_zero
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(26:K))=(31:K) by
          linear_combination (-35:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=31) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(26:K))=(12:K) by
          linear_combination (-9:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=12) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(26:K))=(10:K) by
          linear_combination (-32:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(26:K))=(35:K) by
          linear_combination (-763:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(26:K))=(20:K) by
          linear_combination (-47020:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=20) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(26:K))=(33:K) by
          linear_combination (-49881:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=33) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(16:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(16:K))=(7:K) by
          linear_combination (-8:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(16:K))=(12:K) by
          linear_combination (5:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=12) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(16:K))=(23:K) by
          linear_combination (-11:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=23) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(16:K))=(6:K) by
          linear_combination (5:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=6) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(16:K))=(39:K) by
          linear_combination (-73:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=39) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(16:K))=(17:K) by
          linear_combination (-745:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=17) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(16:K))=(36:K) by
          linear_combination (11268:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=36) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(16:K))=(8:K) by
          linear_combination (-20104:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=8) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(26:K))=(2:K) by
          linear_combination (-13:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(26:K))=(29:K) by
          linear_combination (8:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(26:K))=(30:K) by
          linear_combination (-18:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=30) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(26:K))=(23:K) by
          linear_combination (8:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=23) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(26:K))=(6:K) by
          linear_combination (-120:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=6) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(26:K))=(29:K) by
          linear_combination (-1237:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(26:K))=(7:K) by
          linear_combination (18697:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(26:K))=(4:K) by
          linear_combination (-33380:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=4) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(16:K) := sub_eq_zero.mp u0
      refine ChartResult.linear ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(16:K))=(34:K) by
          linear_combination (34:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=34) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(16:K))=(1:K) by
          linear_combination (59:K)*hp]
        exact one_ne_zero
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(16:K))=(6:K) by
          linear_combination (-284:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=6) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(16:K))=(24:K) by
          linear_combination (-53:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=24) (by decide) hp (by decide)
      · apply mul_left_cancel₀ (show (1:K)≠0 from one_ne_zero)
        rw [mul_zero,chartValue3p2 hq,ur]
        linear_combination (-560:K)*hp
      · apply scaled_ne_of_rhs_ne (chartValue3p1 hq)
        rw [ur,show ((-1050:K)+(336:K)*(16:K))=(21:K) by
          linear_combination (105:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=21) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(16:K))=(20:K) by
          linear_combination (-22756:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=20) (by decide) hp (by decide)
    · have ur : u=(26:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(26:K))=(13:K) by
          linear_combination (55:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(26:K))=(24:K) by
          linear_combination (96:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=24) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(26:K))=(14:K) by
          linear_combination (-472:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(26:K))=(18:K) by
          linear_combination (-87:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=18) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(26:K))=(23:K) by
          linear_combination (-943:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=23) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(26:K))=(14:K) by
          linear_combination (-37630:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(26:K))=(5:K) by
          linear_combination (-190672957:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=5) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(26:K))=(19:K) by
          linear_combination (-2895707:K)*hp]
        exact castNe_of_prime_char (p:=41) (n:=19) (by decide) hp (by decide)

theorem chart_tests_mod_43 [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (hp : (43:K)=0) (o : CleanOrientation) : ChartResult o u := by
  have roots : (u-(3:K))*(u-(41:K))=0 := by
    apply mul_left_cancel₀ (seven_paid K)
    rw [mul_zero]
    linear_combination hq+((-7:K)*u+(20:K))*hp
  cases o
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(3:K) := sub_eq_zero.mp u0
      refine ChartResult.sharedFirst ?_ ?_ ?_ ?_ ?_
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(3:K))=(29:K) by
          linear_combination (-1:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(3:K))=(23:K) by
          linear_combination (1:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=23) (by decide) hp (by decide)
      · apply mul_left_cancel₀ (show (1:K)≠0 from one_ne_zero)
        rw [mul_zero,chartValue1a hq,ur]
        linear_combination (1:K)*hp
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(3:K))=(13:K) by
          linear_combination (-3:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=13) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(3:K))=(8:K) by
          linear_combination (-1:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=8) (by decide) hp (by decide)
    · have ur : u=(41:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(41:K))=(4:K) by
          linear_combination (20:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(41:K))=(6:K) by
          linear_combination (15:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=6) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(41:K))=(35:K) by
          linear_combination (-53:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(41:K))=(35:K) by
          linear_combination (-14:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(41:K))=(8:K) by
          linear_combination (-50:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(41:K))=(14:K) by
          linear_combination (-1154:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(41:K))=(37:K) by
          linear_combination (-71959:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=37) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(41:K))=(41:K) by
          linear_combination (-76043:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=41) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(3:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(3:K))=(38:K) by
          linear_combination (-2:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=38) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(3:K))=(35:K) by
          linear_combination (0:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(3:K))=(22:K) by
          linear_combination (-2:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=22) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(3:K))=(29:K) by
          linear_combination (0:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(3:K))=(24:K) by
          linear_combination (-10:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=24) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(3:K))=(23:K) by
          linear_combination (-101:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=23) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(3:K))=(5:K) by
          linear_combination (1537:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=5) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(3:K))=(19:K) by
          linear_combination (-2713:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=19) (by decide) hp (by decide)
    · have ur : u=(41:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(41:K))=(14:K) by
          linear_combination (-20:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=14) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(41:K))=(8:K) by
          linear_combination (13:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(41:K))=(33:K) by
          linear_combination (-27:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=33) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(41:K))=(2:K) by
          linear_combination (13:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(41:K))=(15:K) by
          linear_combination (-183:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(41:K))=(41:K) by
          linear_combination (-1883:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=41) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(41:K))=(31:K) by
          linear_combination (28451:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=31) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(41:K))=(32:K) by
          linear_combination (-50816:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=32) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(3:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(3:K))=(35:K) by
          linear_combination (7:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(3:K))=(31:K) by
          linear_combination (9:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=31) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(3:K))=(6:K) by
          linear_combination (-38:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=6) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(3:K))=(15:K) by
          linear_combination (-8:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(3:K))=(4:K) by
          linear_combination (-60:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(3:K))=(39:K) by
          linear_combination (-3261:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=39) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(3:K))=(30:K) by
          linear_combination (-15389850:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=30) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(3:K))=(3:K) by
          linear_combination (-198921:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=3) (by decide) hp (by decide)
    · have ur : u=(41:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(41:K))=(2:K) by
          linear_combination (82:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(41:K))=(35:K) by
          linear_combination (145:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=35) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(41:K))=(29:K) by
          linear_combination (-719:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(41:K))=(27:K) by
          linear_combination (-132:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=27) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(41:K))=(18:K) by
          linear_combination (-1446:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=18) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(41:K))=(3:K) by
          linear_combination (-57153:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=3) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(41:K))=(9:K) by
          linear_combination (-290335707:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=9) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(41:K))=(29:K) by
          linear_combination (-4431959:K)*hp]
        exact castNe_of_prime_char (p:=43) (n:=29) (by decide) hp (by decide)

theorem chart_tests_mod_79 [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (hp : (79:K)=0) (o : CleanOrientation) : ChartResult o u := by
  have roots : (u-(28:K))*(u-(52:K))=0 := by
    apply mul_left_cancel₀ (seven_paid K)
    rw [mul_zero]
    linear_combination hq+((-7:K)*u+(129:K))*hp
  cases o
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(28:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(28:K))=(38:K) by
          linear_combination (7:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=38) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(28:K))=(48:K) by
          linear_combination (5:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=48) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(28:K))=(64:K) by
          linear_combination (-20:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=64) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(28:K))=(10:K) by
          linear_combination (-5:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(28:K))=(8:K) by
          linear_combination (-18:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=8) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(28:K))=(37:K) by
          linear_combination (-427:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=37) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(28:K))=(68:K) by
          linear_combination (-26372:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=68) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(28:K))=(61:K) by
          linear_combination (-27955:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=61) (by decide) hp (by decide)
    · have ur : u=(52:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
        rw [ur,show ((3:K)+(21:K)*(52:K))=(68:K) by
          linear_combination (13:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=68) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1a hq)
        rw [ur,show ((-5:K)+(16:K)*(52:K))=(37:K) by
          linear_combination (10:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=37) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1b hq)
        rw [ur,show ((52:K)+(-56:K)*(52:K))=(63:K) by
          linear_combination (-37:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=63) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1d hq)
        rw [ur,show ((7:K)+(-14:K)*(52:K))=(69:K) by
          linear_combination (-10:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=69) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
        rw [ur,show ((154:K)+(-56:K)*(52:K))=(7:K) by
          linear_combination (-35:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
        rw [ur,show ((576:K)+(-1224:K)*(52:K))=(49:K) by
          linear_combination (-799:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=49) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
        rw [ur,show ((93960:K)+(-77760:K)*(52:K))=(45:K) by
          linear_combination (-49995:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=45) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
        rw [ur,show ((77760:K)+(-81648:K)*(52:K))=(25:K) by
          linear_combination (-52759:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=25) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(28:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(28:K))=(59:K) by
          linear_combination (-8:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=59) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(28:K))=(69:K) by
          linear_combination (4:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=69) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(28:K))=(26:K) by
          linear_combination (-10:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=26) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(28:K))=(63:K) by
          linear_combination (4:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=63) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(28:K))=(66:K) by
          linear_combination (-68:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=66) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(28:K))=(27:K) by
          linear_combination (-693:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=27) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(28:K))=(50:K) by
          linear_combination (10474:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=50) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(28:K))=(18:K) by
          linear_combination (-18702:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=18) (by decide) hp (by decide)
    · have ur : u=(52:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
        rw [ur,show ((15:K)+(-21:K)*(52:K))=(29:K) by
          linear_combination (-14:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=29) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2a hq)
        rw [ur,show ((-7:K)+(14:K)*(52:K))=(10:K) by
          linear_combination (9:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=10) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2b hq)
        rw [ur,show ((20:K)+(-28:K)*(52:K))=(65:K) by
          linear_combination (-19:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=65) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2d hq)
        rw [ur,show ((-13:K)+(14:K)*(52:K))=(4:K) by
          linear_combination (9:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=4) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
        rw [ur,show ((182:K)+(-196:K)*(52:K))=(23:K) by
          linear_combination (-127:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=23) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
        rw [ur,show ((1728:K)+(-2016:K)*(52:K))=(70:K) by
          linear_combination (-1306:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=70) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
        rw [ur,show ((-25272:K)+(30456:K)*(52:K))=(7:K) by
          linear_combination (19727:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=7) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
        rw [ur,show ((46656:K)+(-54432:K)*(52:K))=(73:K) by
          linear_combination (-35239:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=73) (by decide) hp (by decide)
  · rcases mul_eq_zero.mp roots with u0|u0
    · have ur : u=(28:K) := sub_eq_zero.mp u0
      refine ChartResult.quadratic ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(28:K))=(66:K) by
          linear_combination (30:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=66) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(28:K))=(2:K) by
          linear_combination (54:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=2) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(28:K))=(57:K) by
          linear_combination (-265:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=57) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3d hq)
        rw [ur,show ((91:K)+(-140:K)*(28:K))=(42:K) by
          linear_combination (-49:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=42) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(28:K))=(15:K) by
          linear_combination (-529:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=15) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
        rw [ur,show ((42768:K)+(-60984:K)*(28:K))=(62:K) by
          linear_combination (-21074:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=62) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
        rw [ur,show ((271605312:K)+(-311122944:K)*(28:K))=(58:K) by
          linear_combination (-106833382:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=58) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
        rw [ur,show ((5816448:K)+(-4790016:K)*(28:K))=(58:K) by
          linear_combination (-1624102:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=58) (by decide) hp (by decide)
    · have ur : u=(52:K) := sub_eq_zero.mp u0
      refine ChartResult.sharedMiddle ?_ ?_ ?_ ?_ ?_
      · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
        rw [ur,show ((2128:K)+(-1568:K)*(52:K))=(66:K) by
          linear_combination (-1006:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=66) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
        rw [ur,show ((84:K)+(84:K)*(52:K))=(28:K) by
          linear_combination (56:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=28) (by decide) hp (by decide)
      · apply mul_left_cancel₀ (show (1:K)≠0 from one_ne_zero)
        rw [mul_zero,chartValue3d hq,ur]
        linear_combination (-91:K)*hp
      · apply scaled_ne_of_rhs_ne (chartValue3a hq)
        rw [ur,show ((-44:K)+(154:K)*(52:K))=(64:K) by
          linear_combination (100:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=64) (by decide) hp (by decide)
      · apply scaled_ne_of_rhs_ne (chartValue3b hq)
        rw [ur,show ((682:K)+(-770:K)*(52:K))=(63:K) by
          linear_combination (-499:K)*hp]
        exact castNe_of_prime_char (p:=79) (n:=63) (by decide) hp (by decide)

end RKResearch.Certified.Graded.FourOffNewton
