module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def wronskianH (v : K) : K :=
  35 - 1155*v + 25410*v^2 - 182182*v^3 + 570999*v^4 - 797511*v^5 + 408980*v^6

private theorem hslot0 (v : K) (hl : 0 ≤ (8*v - 0)) (hu : 0 ≤ (1 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 9175040*(8*v - 0)^0*(1 - 8*v)^6 + 17203200*(8*v - 0)^1*(1 - 8*v)^5 + 52469760*(8*v - 0)^2*(1 - 8*v)^4 + 128070656*(8*v - 0)^3*(1 - 8*v)^3 + 140343744*(8*v - 0)^4*(1 - 8*v)^2 + 69008712*(8*v - 0)^5*(1 - 8*v)^1 + 12703004*(8*v - 0)^6*(1 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 9175040*(8*v - 0)^0*(1 - 8*v)^6 + 17203200*(8*v - 0)^1*(1 - 8*v)^5 + 52469760*(8*v - 0)^2*(1 - 8*v)^4 + 128070656*(8*v - 0)^3*(1 - 8*v)^3 + 140343744*(8*v - 0)^4*(1 - 8*v)^2 + 69008712*(8*v - 0)^5*(1 - 8*v)^1 + 12703004*(8*v - 0)^6*(1 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot1 (v : K) (hl : 0 ≤ (8*v - 1)) (hu : 0 ≤ (2 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 12703004*(8*v - 1)^0*(2 - 8*v)^6 + 83427336*(8*v - 1)^1*(2 - 8*v)^5 + 212436864*(8*v - 1)^2*(2 - 8*v)^4 + 266811456*(8*v - 1)^3*(2 - 8*v)^3 + 180319680*(8*v - 1)^4*(2 - 8*v)^2 + 65107584*(8*v - 1)^5*(2 - 8*v)^1 + 10295808*(8*v - 1)^6*(2 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 12703004*(8*v - 1)^0*(2 - 8*v)^6 + 83427336*(8*v - 1)^1*(2 - 8*v)^5 + 212436864*(8*v - 1)^2*(2 - 8*v)^4 + 266811456*(8*v - 1)^3*(2 - 8*v)^3 + 180319680*(8*v - 1)^4*(2 - 8*v)^2 + 65107584*(8*v - 1)^5*(2 - 8*v)^1 + 10295808*(8*v - 1)^6*(2 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot2 (v : K) (hl : 0 ≤ (8*v - 2)) (hu : 0 ≤ (3 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 10295808*(8*v - 2)^0*(3 - 8*v)^6 + 58442112*(8*v - 2)^1*(3 - 8*v)^5 + 146992320*(8*v - 2)^2*(3 - 8*v)^4 + 218771904*(8*v - 2)^3*(3 - 8*v)^3 + 201627648*(8*v - 2)^4*(3 - 8*v)^2 + 103000824*(8*v - 2)^5*(3 - 8*v)^1 + 21708044*(8*v - 2)^6*(3 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 10295808*(8*v - 2)^0*(3 - 8*v)^6 + 58442112*(8*v - 2)^1*(3 - 8*v)^5 + 146992320*(8*v - 2)^2*(3 - 8*v)^4 + 218771904*(8*v - 2)^3*(3 - 8*v)^3 + 201627648*(8*v - 2)^4*(3 - 8*v)^2 + 103000824*(8*v - 2)^5*(3 - 8*v)^1 + 21708044*(8*v - 2)^6*(3 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot3 (v : K) (hl : 0 ≤ (8*v - 3)) (hu : 0 ≤ (4 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 21708044*(8*v - 3)^0*(4 - 8*v)^6 + 157495704*(8*v - 3)^1*(4 - 8*v)^5 + 474102048*(8*v - 3)^2*(4 - 8*v)^4 + 747503360*(8*v - 3)^3*(4 - 8*v)^3 + 643289088*(8*v - 3)^4*(4 - 8*v)^2 + 284227584*(8*v - 3)^5*(4 - 8*v)^1 + 50536448*(8*v - 3)^6*(4 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 21708044*(8*v - 3)^0*(4 - 8*v)^6 + 157495704*(8*v - 3)^1*(4 - 8*v)^5 + 474102048*(8*v - 3)^2*(4 - 8*v)^4 + 747503360*(8*v - 3)^3*(4 - 8*v)^3 + 643289088*(8*v - 3)^4*(4 - 8*v)^2 + 284227584*(8*v - 3)^5*(4 - 8*v)^1 + 50536448*(8*v - 3)^6*(4 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot4 (v : K) (hl : 0 ≤ (8*v - 4)) (hu : 0 ≤ (5 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 50536448*(8*v - 4)^0*(5 - 8*v)^6 + 322209792*(8*v - 4)^1*(5 - 8*v)^5 + 833200128*(8*v - 4)^2*(5 - 8*v)^4 + 1115537664*(8*v - 4)^3*(5 - 8*v)^3 + 818560800*(8*v - 4)^4*(5 - 8*v)^2 + 318914280*(8*v - 4)^5*(5 - 8*v)^1 + 54773340*(8*v - 4)^6*(5 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 50536448*(8*v - 4)^0*(5 - 8*v)^6 + 322209792*(8*v - 4)^1*(5 - 8*v)^5 + 833200128*(8*v - 4)^2*(5 - 8*v)^4 + 1115537664*(8*v - 4)^3*(5 - 8*v)^3 + 818560800*(8*v - 4)^4*(5 - 8*v)^2 + 318914280*(8*v - 4)^5*(5 - 8*v)^1 + 54773340*(8*v - 4)^6*(5 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot5 (v : K) (hl : 0 ≤ (8*v - 5)) (hu : 0 ≤ (6 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 54773340*(8*v - 5)^0*(6 - 8*v)^6 + 338365800*(8*v - 5)^1*(6 - 8*v)^5 + 915818400*(8*v - 5)^2*(6 - 8*v)^4 + 1440111936*(8*v - 5)^3*(6 - 8*v)^3 + 1417892544*(8*v - 5)^4*(6 - 8*v)^2 + 821423232*(8*v - 5)^5*(6 - 8*v)^1 + 211825664*(8*v - 5)^6*(6 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 54773340*(8*v - 5)^0*(6 - 8*v)^6 + 338365800*(8*v - 5)^1*(6 - 8*v)^5 + 915818400*(8*v - 5)^2*(6 - 8*v)^4 + 1440111936*(8*v - 5)^3*(6 - 8*v)^3 + 1417892544*(8*v - 5)^4*(6 - 8*v)^2 + 821423232*(8*v - 5)^5*(6 - 8*v)^1 + 211825664*(8*v - 5)^6*(6 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot6 (v : K) (hl : 0 ≤ (8*v - 6)) (hu : 0 ≤ (7 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 211825664*(8*v - 6)^0*(7 - 8*v)^6 + 1720484736*(8*v - 6)^1*(7 - 8*v)^5 + 5913200064*(8*v - 6)^2*(7 - 8*v)^4 + 10938205376*(8*v - 6)^3*(7 - 8*v)^3 + 11428868640*(8*v - 6)^4*(7 - 8*v)^2 + 6372794904*(8*v - 6)^5*(7 - 8*v)^1 + 1477999628*(8*v - 6)^6*(7 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 211825664*(8*v - 6)^0*(7 - 8*v)^6 + 1720484736*(8*v - 6)^1*(7 - 8*v)^5 + 5913200064*(8*v - 6)^2*(7 - 8*v)^4 + 10938205376*(8*v - 6)^3*(7 - 8*v)^3 + 11428868640*(8*v - 6)^4*(7 - 8*v)^2 + 6372794904*(8*v - 6)^5*(7 - 8*v)^1 + 1477999628*(8*v - 6)^6*(7 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

private theorem hslot7 (v : K) (hl : 0 ≤ (8*v - 7)) (hu : 0 ≤ (8 - 8*v)) : 0 ≤ wronskianH v := by
  have cert : 262144 * wronskianH v = 1477999628*(8*v - 7)^0*(8 - 8*v)^6 + 11363200632*(8*v - 7)^1*(8 - 8*v)^5 + 36380897280*(8*v - 7)^2*(8 - 8*v)^4 + 62060888064*(8*v - 7)^3*(8 - 8*v)^3 + 59473133568*(8*v - 7)^4*(8 - 8*v)^2 + 30349983744*(8*v - 7)^5*(8 - 8*v)^1 + 6442450944*(8*v - 7)^6*(8 - 8*v)^0 := by unfold wronskianH; ring
  have nonneg : 0 ≤ 1477999628*(8*v - 7)^0*(8 - 8*v)^6 + 11363200632*(8*v - 7)^1*(8 - 8*v)^5 + 36380897280*(8*v - 7)^2*(8 - 8*v)^4 + 62060888064*(8*v - 7)^3*(8 - 8*v)^3 + 59473133568*(8*v - 7)^4*(8 - 8*v)^2 + 30349983744*(8*v - 7)^5*(8 - 8*v)^1 + 6442450944*(8*v - 7)^6*(8 - 8*v)^0 := by positivity
  linarith only [cert, nonneg]

/-- All 56 homogeneous Bernstein ordinates are strictly positive. Only
nonnegativity is needed, including v=0 and v=1. No field completeness is used. -/
theorem wronskianH_nonneg {v : K} (hv : v ∈ Set.Icc 0 1) : 0 ≤ wronskianH v := by
  by_cases c0 : 8*v ≤ 1
  · exact hslot0 v (by linarith only [hv.1]) (by linarith only [c0])
  by_cases c1 : 8*v ≤ 2
  · exact hslot1 v (by linarith only [c0]) (by linarith only [c1])
  by_cases c2 : 8*v ≤ 3
  · exact hslot2 v (by linarith only [c1]) (by linarith only [c2])
  by_cases c3 : 8*v ≤ 4
  · exact hslot3 v (by linarith only [c2]) (by linarith only [c3])
  by_cases c4 : 8*v ≤ 5
  · exact hslot4 v (by linarith only [c3]) (by linarith only [c4])
  by_cases c5 : 8*v ≤ 6
  · exact hslot5 v (by linarith only [c4]) (by linarith only [c5])
  by_cases c6 : 8*v ≤ 7
  · exact hslot6 v (by linarith only [c5]) (by linarith only [c6])
  exact hslot7 v (by linarith only [c6]) (by linarith only [hv.2])

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
