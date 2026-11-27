module

public import RKCert.ReviewedNative.ERK8FourOffPaidGates
public import Mathlib.Algebra.CharP.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact affine reductions of the outside-eleven scalar chart values
Each reduction is an integer polynomial identity after multiplying
by a power of the paid primes. There are no point-search assumptions. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K]

theorem chartValue1p0 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftCenterRight u).p0=(3:K)+(21:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue1p1 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftCenterRight u).p1=(-69:K)+(-42:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue1p2 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftCenterRight u).p2=(154:K)+(-56:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue1a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capFirst .leftCenterRight u=(-5:K)+(16:K)*u := by
  simp only [capFirst,chartQuadratic,Quad.eval]
  linear_combination (8 - 8*u)*hq

theorem chartValue1b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capLast .leftCenterRight u=(52:K)+(-56:K)*u := by
  simp only [capLast,chartQuadratic,Quad.eval]
  linear_combination (36 - 8*u)*hq

theorem chartValue1d [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capMiddle .leftCenterRight u=(7:K)+(-14:K)*u := by
  simp only [capMiddle,chartQuadratic,Quad.eval]
  have hc : 2*midClock K-1=0 := by rw [mul_div_cancel₀ _ (two_paid K),sub_self]
  generalize _c : midClock K = c at hc ⊢
  linear_combination (-28*c*u + 77*c - 35*u + 4)*hc

theorem chartValue1f4 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (7:K)*firstCleanFourGate .leftCenterRight u=(576:K)+(-1224:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftCenterRight u=(-5:K)+(16:K)*u := by
    simpa only [one_mul] using chartValue1a hq
  have b : capLast .leftCenterRight u=(52:K)+(-56:K)*u := by
    simpa only [one_mul] using chartValue1b hq
  have d : capMiddle .leftCenterRight u=(7:K)+(-14:K)*u := by
    simpa only [one_mul] using chartValue1d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (7168*u^3 - 5824*u^2 - 1184*u + 1104)*hq

theorem chartValue1f5a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (7:K)*firstCleanFiveGram .leftCenterRight u=(93960:K)+(-77760:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftCenterRight u=(-5:K)+(16:K)*u := by
    simpa only [one_mul] using chartValue1a hq
  have b : capLast .leftCenterRight u=(52:K)+(-56:K)*u := by
    simpa only [one_mul] using chartValue1b hq
  have d : capMiddle .leftCenterRight u=(7:K)+(-14:K)*u := by
    simpa only [one_mul] using chartValue1d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (1204224*u^4 - 5408256*u^3 + 6991488*u^2 - 3641088*u + 746880)*hq

theorem chartValue1f5b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (7:K)*firstCleanFiveGate .leftCenterRight u=(77760:K)+(-81648:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftCenterRight u=(-5:K)+(16:K)*u := by
    simpa only [one_mul] using chartValue1a hq
  have b : capLast .leftCenterRight u=(52:K)+(-56:K)*u := by
    simpa only [one_mul] using chartValue1b hq
  have d : capMiddle .leftCenterRight u=(7:K)+(-14:K)*u := by
    simpa only [one_mul] using chartValue1d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (-451584*u^4 + 1674624*u^3 - 1755936*u^2 + 451920*u + 105360)*hq

theorem chartValue2p0 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftRightCenter u).p0=(15:K)+(-21:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue2p1 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftRightCenter u).p1=(-147:K)+(168:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue2p2 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .leftRightCenter u).p2=(182:K)+(-196:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue2a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capFirst .leftRightCenter u=(-7:K)+(14:K)*u := by
  simp only [capFirst,chartQuadratic,Quad.eval]
  linear_combination (22 - 28*u)*hq

theorem chartValue2b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capLast .leftRightCenter u=(20:K)+(-28:K)*u := by
  simp only [capLast,chartQuadratic,Quad.eval]
  linear_combination (30 - 28*u)*hq

theorem chartValue2d [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capMiddle .leftRightCenter u=(-13:K)+(14:K)*u := by
  simp only [capMiddle,chartQuadratic,Quad.eval]
  have hc : 2*midClock K-1=0 := by rw [mul_div_cancel₀ _ (two_paid K),sub_self]
  generalize _c : midClock K = c at hc ⊢
  linear_combination (-98*c*u + 91*c + 35*u - 28)*hc

theorem chartValue2f4 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (7:K)*firstCleanFourGate .leftRightCenter u=(1728:K)+(-2016:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftRightCenter u=(-7:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2a hq
  have b : capLast .leftRightCenter u=(20:K)+(-28:K)*u := by
    simpa only [one_mul] using chartValue2b hq
  have d : capMiddle .leftRightCenter u=(-13:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (-6272*u^3 + 18368*u^2 - 16352*u + 5328)*hq

theorem chartValue2f5a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*firstCleanFiveGram .leftRightCenter u=(-25272:K)+(30456:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftRightCenter u=(-7:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2a hq
  have b : capLast .leftRightCenter u=(20:K)+(-28:K)*u := by
    simpa only [one_mul] using chartValue2b hq
  have d : capMiddle .leftRightCenter u=(-13:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (-263424*u^4 + 809088*u^3 - 943488*u^2 + 508992*u - 116688)*hq

theorem chartValue2f5b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*firstCleanFiveGate .leftRightCenter u=(46656:K)+(-54432:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .leftRightCenter u=(-7:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2a hq
  have b : capLast .leftRightCenter u=(20:K)+(-28:K)*u := by
    simpa only [one_mul] using chartValue2b hq
  have d : capMiddle .leftRightCenter u=(-13:K)+(14:K)*u := by
    simpa only [one_mul] using chartValue2d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (131712*u^4 - 329280*u^3 + 336672*u^2 - 208752*u + 81360)*hq

theorem chartValue3p0 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .centerLeftRight u).p0=(84:K)+(84:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue3p1 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .centerLeftRight u).p1=(-1050:K)+(336:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue3p2 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*(chartQuadratic .centerLeftRight u).p2=(2128:K)+(-1568:K)*u := by
  try simp only [chartQuadratic]
  ring

theorem chartValue3a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capFirst .centerLeftRight u=(-44:K)+(154:K)*u := by
  simp only [capFirst,chartQuadratic,Quad.eval]
  linear_combination (128 - 224*u)*hq

theorem chartValue3b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capLast .centerLeftRight u=(682:K)+(-770:K)*u := by
  simp only [capLast,chartQuadratic,Quad.eval]
  linear_combination (480 - 224*u)*hq

theorem chartValue3d [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*capMiddle .centerLeftRight u=(91:K)+(-140:K)*u := by
  simp only [capMiddle,chartQuadratic,Quad.eval]
  have hc : 2*midClock K-1=0 := by rw [mul_div_cancel₀ _ (two_paid K),sub_self]
  generalize _c : midClock K = c at hc ⊢
  linear_combination (-784*c*u + 1064*c - 224*u + 7)*hc

theorem chartValue3f4 [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (7:K)*firstCleanFourGate .centerLeftRight u=(42768:K)+(-60984:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .centerLeftRight u=(-44:K)+(154:K)*u := by
    simpa only [one_mul] using chartValue3a hq
  have b : capLast .centerLeftRight u=(682:K)+(-770:K)*u := by
    simpa only [one_mul] using chartValue3b hq
  have d : capMiddle .centerLeftRight u=(91:K)+(-140:K)*u := by
    simpa only [one_mul] using chartValue3d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  have hc : 2*midClock K-1=0 := by rw [mul_div_cancel₀ _ (two_paid K),sub_self]
  generalize _c : midClock K = c at hc ⊢
  linear_combination (3622080*c*u^3 - 2483712*c*u^2 - 1474704*c*u + 728112*c - 4829440*u^4 + 7537376*u^3 - 4346496*u^2 + 1573880*u - 251944)*hc + (1034880*u^3 - 1658272*u^2 + 800800*u - 98824)*hq

theorem chartValue3f5a [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*firstCleanFiveGram .centerLeftRight u=(271605312:K)+(-311122944:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .centerLeftRight u=(-44:K)+(154:K)*u := by
    simpa only [one_mul] using chartValue3a hq
  have b : capLast .centerLeftRight u=(682:K)+(-770:K)*u := by
    simpa only [one_mul] using chartValue3b hq
  have d : capMiddle .centerLeftRight u=(91:K)+(-140:K)*u := by
    simpa only [one_mul] using chartValue3d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (6374860800*u^4 - 20262950400*u^3 + 22908517632*u^2 - 11313565824*u + 2218818624)*hq

theorem chartValue3f5b [EightUnits K] {u : K} (hq : 7*u^2-7*u+1=0) :
    (1:K)*firstCleanFiveGate .centerLeftRight u=(5816448:K)+(-4790016:K)*u := by
  simp only [firstCleanFourGate,firstCleanFiveGram,firstCleanFiveGate,clearedMoment,chartH]
  have a : capFirst .centerLeftRight u=(-44:K)+(154:K)*u := by
    simpa only [one_mul] using chartValue3a hq
  have b : capLast .centerLeftRight u=(682:K)+(-770:K)*u := by
    simpa only [one_mul] using chartValue3b hq
  have d : capMiddle .centerLeftRight u=(91:K)+(-140:K)*u := by
    simpa only [one_mul] using chartValue3d hq
  rw [a,b,d]
  try simp only [chartQuadratic]
  linear_combination (-231813120*u^4 + 531514368*u^3 - 411941376*u^2 + 84978432*u + 18784128)*hq

end RKResearch.Certified.Graded.FourOffNewton
