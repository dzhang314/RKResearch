module
public import RKCert.Dirk15FirstReplayPair
public import RKCert.Dirk15Replay.PairF5K2E0
public import RKCert.Dirk15Replay.PairF5K3E0
public import RKCert.Dirk15Replay.PairF5K4E0
public import RKCert.Dirk15Replay.PairF5K1E1
public import RKCert.Dirk15Replay.PairF5K2E1
public import RKCert.Dirk15Replay.PairF5K3E1
public import RKCert.Dirk15Replay.PairR5K1E0
public import RKCert.Dirk15Replay.PairR5K2E0
public import RKCert.Dirk15Replay.PairR5K3E0
public import RKCert.Dirk15Replay.PairA5K1E0
public import RKCert.Dirk15Replay.PairA5K2E0
public import RKCert.Dirk15Replay.PairA5K3E0
public import RKCert.Dirk15Replay.PairA5K4E0
public import RKCert.Dirk15Replay.PairsG
public import RKCert.Dirk15Replay.PairG5K2E0
public import RKCert.Dirk15Replay.PairG5K3E0
public import RKCert.Dirk15Replay.PairG5K1E1
public import RKCert.Dirk15Replay.PairG5K2E1
public import RKCert.Dirk15Replay.PairH5K1E0
public import RKCert.Dirk15Replay.PairH5K2E0
public import RKCert.Dirk15Replay.PairH5K3E0
public import RKCert.Dirk15Replay.PairF6K1E0
public import RKCert.Dirk15Replay.PairF6K2E0
public import RKCert.Dirk15Replay.PairF6K3E0
public import RKCert.Dirk15Replay.PairF6K4E0
public import RKCert.Dirk15Replay.PairF6K1E1
public import RKCert.Dirk15Replay.PairF6K2E1
public import RKCert.Dirk15Replay.PairF6K3E1
public import RKCert.Dirk15Replay.PairR6K1E0
public import RKCert.Dirk15Replay.PairR6K2E0
public import RKCert.Dirk15Replay.PairR6K3E0
public import RKCert.Dirk15Replay.PairA6K1E0
public import RKCert.Dirk15Replay.PairA6K2E0
public import RKCert.Dirk15Replay.PairA6K3E0
public import RKCert.Dirk15Replay.PairA6K4E0
public import RKCert.Dirk15Replay.PairG6K1E0
public import RKCert.Dirk15Replay.PairG6K2E0
public import RKCert.Dirk15Replay.PairG6K3E0
public import RKCert.Dirk15Replay.PairG6K1E1
public import RKCert.Dirk15Replay.PairG6K2E1
public import RKCert.Dirk15Replay.PairH6K1E0
public import RKCert.Dirk15Replay.PairH6K2E0
public import RKCert.Dirk15Replay.PairH6K3E0
public import RKCert.Dirk15ArithmeticDispatch

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
private theorem F5K1E0 : Order15GoodPrimePair (nodeMomentNorm 5 1 1 0) (nodeMomentNorm 5 1 2 0) 10 10 := Order15Smoke.one_checked_pair

theorem exactOrder15FiniteReplay : Order15FiniteReplay where
  forwardMoments n k e ns kp e1 kg := by
    rcases ns with rfl | rfl
    · rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
      · have kMax : k≤4 := by omega
        interval_cases k
        · exact F5K1E0
        · exact F5K2E0
        · exact F5K3E0
        · exact F5K4E0
      · have kMax : k≤3 := by omega
        interval_cases k
        · exact F5K1E1
        · exact F5K2E1
        · exact F5K3E1
    · rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
      · have kMax : k≤4 := by omega
        interval_cases k
        · exact F6K1E0
        · exact F6K2E0
        · exact F6K3E0
        · exact F6K4E0
      · have kMax : k≤3 := by omega
        interval_cases k
        · exact F6K1E1
        · exact F6K2E1
        · exact F6K3E1
  reflectedMoments n k ns kp kg := by
    rcases ns with rfl | rfl
    · interval_cases k
      · exact R5K1E0
      · exact R5K2E0
      · exact R5K3E0
    · interval_cases k
      · exact R6K1E0
      · exact R6K2E0
      · exact R6K3E0
  fixedMoments n k ns kp kg := by
    rcases ns with rfl | rfl
    · interval_cases k
      · exact A5K1E0
      · exact A5K2E0
      · exact A5K3E0
      · exact A5K4E0
    · interval_cases k
      · exact A6K1E0
      · exact A6K2E0
      · exact A6K3E0
      · exact A6K4E0
  gramBothRoots n k e ns kp e1 kg := by
    rcases ns with rfl | rfl
    · rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
      · have kMax : k≤3 := by omega
        interval_cases k
        · exact G5K1E0
        · exact G5K2E0
        · exact G5K3E0
      · have kMax : k≤2 := by omega
        interval_cases k
        · exact G5K1E1
        · exact G5K2E1
    · rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
      · have kMax : k≤3 := by omega
        interval_cases k
        · exact G6K1E0
        · exact G6K2E0
        · exact G6K3E0
      · have kMax : k≤2 := by omega
        interval_cases k
        · exact G6K1E1
        · exact G6K2E1
  gramFixedReverse n k ns kp kg := by
    rcases ns with rfl | rfl
    · interval_cases k
      · exact H5K1E0
      · exact H5K2E0
      · exact H5K3E0
    · interval_cases k
      · exact H6K1E0
      · exact H6K2E0
      · exact H6K3E0

end RKCert.FixedPolynomial.FixedReplay


namespace RKCert.Paired

/-- Every original lower-triangular tableau of tree order at least
fifteen has at least twenty-one physical stages over a characteristic-zero field. -/
theorem dirk_order15_twenty_one_charZero_field {K : Type*} [Field K] [CharZero K]
    {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s} (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 15≤p) : 21≤s :=
  dirk_order15_ge21_of_finite_replay
    RKCert.FixedPolynomial.FixedReplay.exactOrder15FiniteReplay ha
    (fun t ht => ho t (ht.trans hp))

end RKCert.Paired

namespace RKCert

/-- The actual all-tree array specializes into a characteristic-zero field,
preserving the number of physical rows and lower triangularity. -/
theorem dirk_order15_twenty_one_charZero_ring {R : Type*} [CommRing R] [CharZero R]
    {s p : ℕ} {A : Fin s→Fin s→R} {b : Fin s→R}
    (ha : ∀ i j, i.val<j.val → A i j=0) (ho : HasTreeOrderAtLeast A b p) (hp : 15≤p) :
    21≤s :=
  lowerTriangular_of_charZero_fields (fun _ _ _ _ _ ht hs =>
    Paired.dirk_order15_twenty_one_charZero_field ht hs hp) ha ho

end RKCert

#print axioms RKCert.FixedPolynomial.FixedReplay.exactOrder15FiniteReplay
#print axioms RKCert.Paired.dirk_order15_twenty_one_charZero_field
#print axioms RKCert.dirk_order15_twenty_one_charZero_ring
