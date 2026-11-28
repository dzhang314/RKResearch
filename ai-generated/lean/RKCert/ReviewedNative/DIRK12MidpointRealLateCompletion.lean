module

public import RKCert.ReviewedNative.DIRK12MidpointLateCompletion
public import RKCert.ReviewedNative.DIRK12MidpointRealForwardWiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! The late Vandermonde adapter on the actual physical real row sums
and aggregate weights established for the midpoint construction. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Late

open RKResearch Graded
open DIRK12MidpointRealInterval DirectedRatBox
open scoped Matrix BigOperators

section Actual
variable (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => realFeed x f alpha mu nu L
local notation "Yrefl" => DualSupport12.reflected (Feed.tableau (realFeed x f alpha mu nu L))
local notation "Bphys" => Feed.b (realFeed x f alpha mu nu L)

theorem real_late_profile (hx : Encloses xBox x) (hf : Encloses fBox f)
    (w : Fin 15 → ℝ) (early : ∀ i : Fin 15, i.val<10 → Bphys i*w i=0)
    (pair : w 11=w 13)
    (probes : ∀ k : Fin 3,
      row (DualSupport12.moment (thisFeed).tableau Bphys (k.val+1)) w=0) :
    w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0 := by
  let s := site x f
  have q (i : Fin 15) (hi : ¬ghostRow i) : Yrefl i=s (stageTag i) :=
    real_nodes x f alpha mu nu L i hi
  have yclocks : Yrefl 10=s 9 ∧ Yrefl 11=s 7 ∧ Yrefl 12=s 8 ∧
      Yrefl 13=s 7 ∧ Yrefl 14=0 :=
    ⟨q 10 (by decide),q 11 (by decide),q 12 (by decide),q 13 (by decide),q 14 (by decide)⟩
  have src := site_distinct hx hf
  have hh {i j : Fin 10} (h : i≠j) : s i≠s j := fun e => h (src e)
  have b10 := real_weight_guard x f alpha mu nu L hx hf 10 (by decide)
  have b12 := real_weight_guard x f alpha mu nu L hx hf 12 (by decide)
  have bPair : Bphys 11+Bphys 13≠0 := by
    change cardinalWeight x f 7/2+cardinalWeight x f 7/2≠0
    rw [show cardinalWeight x f 7/2+cardinalWeight x f 7/2=cardinalWeight x f 7 by ring]
    exact cardinalWeight_nonzero hx hf 7
  apply remaining_three_clocks Bphys Yrefl w (s 9) (s 7) (s 8)
    yclocks b10 b12 bPair
    (hh (j:=0) (by decide)) (hh (j:=0) (by decide)) (hh (j:=0) (by decide))
    (hh (by decide)) (hh (by decide)) (hh (by decide)) early pair
  intro k
  have h := probes k
  simp only [DualSupport12.moment,row_apply,dotProduct,Pi.mul_apply,Pi.pow_apply] at h
  simpa only [mul_comm, mul_left_comm,mul_assoc] using h

theorem real_late_primitive (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (m : Nat) (hm : m≤7)
    (early : ∀ i : Fin 15, i.val<10 →
      Bphys i*DualSupport12.forward (thisFeed).tableau m i=0)
    (sigma scale : ℝ) (H : Fin 15 → ℝ) (nonzero : sigma≠0)
    (adj : mat (thisFeed).tableau.transpose (physicalPair sigma) =
      scale • physicalPair sigma+H)
    (annih : row H ((nodes (thisFeed).tableau)^m)=0)
    (rev : ∀ j : Fin 3, row (DualSupport12.reverse (thisFeed).tableau Bphys (j.val+1))
        ((nodes (thisFeed).tableau)^m)=0) :
    let w := DualSupport12.forward (thisFeed).tableau m
    w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0 := by
  have c : nodes (thisFeed).tableau 11=nodes (thisFeed).tableau 13 := by
    have a := real_nodes x f alpha mu nu L 11 (by decide)
    have b := real_nodes x f alpha mu nu L 13 (by decide)
    change 1-nodes (thisFeed).tableau 11=site x f 7 at a
    change 1-nodes (thisFeed).tableau 13=site x f 7 at b
    linear_combination b-a
  apply real_late_profile x f alpha mu nu L hx hf _ early
    (paired_primitive_equal (thisFeed).tableau sigma scale H m nonzero c annih adj)
  intro k
  have sc : ∀ j < 12, ((j+1:Nat):ℝ)*row Bphys ((nodes (thisFeed).tableau)^j)=1 := by
    rw [(thisFeed).nodes_tableau]
    exact real_scalar x f alpha mu nu L hx hf hx0 hf0
  exact paid_reverse_to_forward_moment sc (k.val+1) m (by have hk := k.isLt; omega) (rev k)

end Actual
end RKResearch.Certified.DIRK12MidpointForward.Late

#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.real_late_profile
#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.real_late_primitive
