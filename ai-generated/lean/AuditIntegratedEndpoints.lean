import RKCert.ReviewedOrderFifteen
import RKCert.ReviewedOrderBridge
import RKCert.Dirk15Replay.Final
import RKCert.ERKOddOrdered17

/-! Co-load the endpoints. These local consumer examples translate reviewed order with the single existing bridge. -/
example {R : Type*} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ha : ∀ i j : Fin s, i < j → A i j = 0)
    (ho : RKResearch.HasOrder p A b) (hp : 15 ≤ p) : 21 ≤ s :=
  RKCert.dirk_order15_twenty_one_charZero_ring ha
    ((RKCert.ReviewedOrderBridge.hasOrder_iff A b p).mp ho) hp

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j : Fin s, i ≤ j → A i j = 0)
    (ho : RKResearch.HasOrder p A b) (hp : 17 ≤ p) : 27 ≤ s :=
  RKCert.Paired.FiniteMidpoint.ordered_erk17_stage_bound ha
    (fun t ht => ((RKCert.ReviewedOrderBridge.hasOrder_iff A b p).mp ho) t (ht.trans hp))
