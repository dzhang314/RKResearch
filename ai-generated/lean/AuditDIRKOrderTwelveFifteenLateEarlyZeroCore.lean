import RKCert.ReviewedNative.DIRKOrderTwelveFifteenLateEarlyZeroCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.LateEarlyZeroCore

example (m H T0 : Int) (hT : T0 ≠ 0) (hr : -m * H = T0) :
    m ≠ 0 := lateRatioNonzero m H T0 hT hr

example (z P N Q E m T0 σ : Int)
    (hB : Q * N + E * P = 1)
    (hT : T0 = (z - 1) * P - m * N)
    (hσ : σ = (z - 1) * Q + m * E) :
    m + Q * T0 = P * σ := residueNumerator z P N Q E m T0 σ hB hT hσ

example (p1 p2 p3 p4 p5 : Int) :
    (300*p1+200*p2+150*p3+120*p4+99*p5)+p5 =
      300*p1+200*p2+150*p3+120*p4+100*p5 :=
  bareQuinticPayment p1 p2 p3 p4 p5
