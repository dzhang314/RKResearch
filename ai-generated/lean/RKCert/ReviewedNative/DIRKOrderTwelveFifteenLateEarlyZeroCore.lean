import Lean.Elab.Tactic.Omega

/-! Denominator-cleared arithmetic for the late ordinary ghost with an
earlier numerical zero. The actual stage-space argument and finite
projection are proved separately in the research note. -/

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.LateEarlyZeroCore

/-- The actual normalized late primitive ratio, after cancelling its
nonzero clock, forces the nonzero parameter m. -/
theorem lateRatioNonzero (m H T0 : Int) (hT : T0 ≠ 0) (hr : -m * H = T0) :
    m ≠ 0 := by
  intro hm
  rw [hm] at hr
  simp at hr
  exact hT hr.symm

/-- Numerator identity at the fourth ghost in the proper-rational
partial fraction transform. P, N, Q, E are their readings
at the same late clock z, not polynomial unknowns. -/
theorem residueNumerator (z P N Q E m T0 σ : Int)
    (hB : Q * N + E * P = 1)
    (hT : T0 = (z - 1) * P - m * N)
    (hσ : σ = (z - 1) * Q + m * E) :
    m + Q * T0 = P * σ := by
  have hh : m * (Q * N + E * P) = m := by rw [hB, Int.mul_one]
  simp only [Int.mul_add] at hh
  have hx : Q * ((z - 1) * P) = P * ((z - 1) * Q) := by
    calc
      Q * ((z - 1) * P) = (Q * (z - 1)) * P := (Int.mul_assoc ..).symm
      _ = P * (Q * (z - 1)) := Int.mul_comm ..
      _ = P * ((z - 1) * Q) := congrArg (P * ·) (Int.mul_comm ..)
  have hy : Q * (m * N) = m * (Q * N) := by
    rw [← Int.mul_assoc, Int.mul_comm Q m, Int.mul_assoc]
  have hz : P * (m * E) = m * (E * P) := by
    calc
      P * (m * E) = (P * m) * E := (Int.mul_assoc ..).symm
      _ = (m * P) * E := congrArg (· * E) (Int.mul_comm ..)
      _ = m * (P * E) := Int.mul_assoc ..
      _ = m * (E * P) := congrArg (m * ·) (Int.mul_comm ..)
  rw [hT, hσ, Int.mul_sub, Int.mul_add, hx, hy, hz]
  omega

/-- Degree-six primitive coefficient after multiplying the live-only
moment functional by 600, with the actual extra tail 1/600. -/
theorem bareQuinticPayment (p1 p2 p3 p4 p5 : Int) :
    (300*p1+200*p2+150*p3+120*p4+99*p5)+p5 =
      300*p1+200*p2+150*p3+120*p4+100*p5 := by
  omega

#print axioms lateRatioNonzero
#print axioms residueNumerator
#print axioms bareQuinticPayment

end RKResearch.Certified.Graded.OrderTwelveFifteen.LateEarlyZeroCore
