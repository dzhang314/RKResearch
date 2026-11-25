module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveRemainingScalarCases
public import RKCert.ReviewedNative.WeakFiveSoleInnerFiniteRank

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The two actual SoleInner orientations reduce to one structural packet

The last remaining premise is a joint cubic-kernel obstruction on an
exact positive Radau rule. No contradiction for that premise is assumed
or proved in this adapter. Both original SoleInner directions are kept. -/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.WeakFiveSoleInner
open scoped Polynomial BigOperators Classical

noncomputable section
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1500000

private theorem cubic_of_index (r : Fin 3 → K) :
    indexedHull r Finset.univ=cubic (r 0) (r 1) (r 2) := by
  unfold indexedHull
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  change (X-C (r 0))*((X-C (r 1))*(X-C (r 2)))=_
  unfold cubic
  ring

private theorem normalized_layout_moments {p Z : K[X]} {c : Fin 5 → K}
    {r : Fin 3 → K} {e l h : K} (M : Moments p Z c) (P : ExteriorRootLayout p r e l h) :
    Moments (profile e (r 0) (r 1) (r 2)) Z c := by
  let F := profile e (r 0) (r 1) (r 2)
  let t := p.leadingCoeff
  have tn : t ≠ 0 := leadingCoeff_ne_zero.mpr M.qNonzero
  have mf : p=C t*F := by
    simpa only [t,F,profile,cubic_of_index] using P.factor
  have n : p*C t⁻¹=F := by
    calc
      _=(C t*C t⁻¹)*F := by rw [mf]; ring
      _=F := by rw [← map_mul,mul_inv_cancel₀ tn,map_one,one_mul]
  have out := moments_scale_nonzero M (inv_ne_zero tn)
  change Moments (p*C t⁻¹) Z c at out
  rwa [n] at out

private theorem orient_ports {Z : K[X]} {c : Fin 5 → K} {e r₀ r₁ r₂ : K}
    (M : Moments (profile e r₀ r₁ r₂) Z c)
    (ae : c 2 < e) (eNeg : e < 0)
    (z : MarkInterior c 4) (u : MarkInterior c 1) (h : MarkInterior c 3)
    (zu : c 4 < c 1)
    (r0 : r₀ ∈ Set.Ioo 0 1) (r1 : r₁ ∈ Set.Ioo 0 1) (r2 : r₂ ∈ Set.Ioo 0 1)
    (r01 : r₀ < r₁) (r12 : r₁ < r₂) :
    OrientedPorts (c 2) e (c 1) (c 3) (c 4) r₀ r₁ r₂ := by
  have hz : c 3 ≠ c 4 := fun eq => (by decide : (3:Fin 5)≠4) (M.clockSimple eq)
  have hu : c 3 ≠ c 1 := fun eq => (by decide : (3:Fin 5)≠1) (M.clockSimple eq)
  refine ⟨ae,eNeg,z,u,h,zu,hz,hu,r0,r1,r2,r01,r12,?_,M.forwardFirst,
    M.forwardSecond,M.forwardInner,M.reverseFirst,M.reverseSecond,M.reverseInner,
    paidSix_of_actual_moments M⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact (M.active 4).2
  · exact (M.active 3).2
  · exact (M.active 1).2

private theorem unit_reflect {x : K} (h : x ∈ Set.Ioo (0:K) 1) :
    1-x ∈ Set.Ioo (0:K) 1 :=
  ⟨sub_pos.mpr h.2,by linarith only [h.1]⟩

private theorem profile_at_one_of_right {e r₀ r₁ r₂ : K}
    (e1 : 1 < e) (h₀ : r₀ < 1) (h₁ : r₁ < 1) (h₂ : r₂ < 1) :
    (profile e r₀ r₁ r₂).eval 1 ≠ 0 := by
  simp only [profile,cubic,eval_mul,eval_sub,eval_one,eval_X,eval_C]
  exact mul_ne_zero (sub_ne_zero.mpr e1.ne)
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₀.ne') (sub_ne_zero.mpr h₁.ne'))
      (sub_ne_zero.mpr h₂.ne'))

private theorem profile_reflect (e r₀ r₁ r₂ : K) :
    (profile e r₀ r₁ r₂).comp (1-X) = profile (1-e) (1-r₂) (1-r₁) (1-r₀) := by
  simp only [profile,cubic,mul_comp,sub_comp,X_comp,C_comp,map_sub,map_one]
  ring

/-- Preserve the actual extension, exterior root, and sorted unit roots
from either supplied arm. The output is a strict parameter inequality,
all six original local tests, and a positive degree-twelve rule with the
literal seven sites. No extra uniqueness or root placement is presumed. -/
theorem actual_sole_inner_has_rank_packet {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (S : SoleInner q c) :
    ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      RankedPacket (E.embed (c 2)) e (E.embed (c 1)) (E.embed (c 3)) (E.embed (c 4))
        (r 0) (r 1) (r 2) ∨
      RankedPacket (1-E.embed (c 3)) (1-e) (1-E.embed (c 4)) (1-E.embed (c 2))
        (1-E.embed (c 1)) (1-r 2) (1-r 1) (1-r 0) := by
  rcases S with ⟨overlap,left | right⟩
  · obtain ⟨_,u,h,z,E,r,e,P⟩ := left
    let d : Fin 5 → E.carrier := fun j=>E.embed (c j)
    have mapped : Moments (q.map E.embed) (Z.map E.embed) d := moments_along_field E.embed M
    have N := normalized_layout_moments mapped P
    have transfer {j : Fin 5} (b : MarkInterior c j) : MarkInterior d j :=
      ⟨by simpa only [d,map_zero] using E.mono b.1,by simpa only [d,map_one] using E.mono b.2⟩
    have OP := orient_ports N P.edge.1 P.edge.2 (transfer z) (transfer u) (transfer h)
      (E.mono overlap) (P.unit 0) (P.unit 1) (P.unit 2)
      (P.sorted (by decide : (0:Fin 3) < 1)) (P.sorted (by decide : (1:Fin 3) < 2))
    exact ⟨E,r,e,Or.inl OP.ranked⟩
  · obtain ⟨_,u,h,z,E,r,e,P⟩ := right
    let d : Fin 5 → E.carrier := fun j=>E.embed (c j)
    have mapped : Moments (q.map E.embed) (Z.map E.embed) d := moments_along_field E.embed M
    have N := normalized_layout_moments mapped P
    have atOne : (profile e (r 0) (r 1) (r 2)).eval 1 ≠ 0 :=
      profile_at_one_of_right P.edge.1 (P.unit 0).2 (P.unit 1).2 (P.unit 2).2
    have R := reflected_moments N atOne
    rw [profile_reflect] at R
    have transfer {j : Fin 5} (b : MarkInterior c j) : MarkInterior d j :=
      ⟨by simpa only [d,map_zero] using E.mono b.1,by simpa only [d,map_one] using E.mono b.2⟩
    have ha : mirrorClock d 2 < 1-e := by
      change 1-d 3 < 1-e
      have pre : e < d 3 := P.edge.2
      linarith only [pre]
    have hz : MarkInterior (mirrorClock d) 4 := unit_reflect (transfer u)
    have hu : MarkInterior (mirrorClock d) 1 := unit_reflect (transfer z)
    have hh : MarkInterior (mirrorClock d) 3 := unit_reflect (transfer h)
    have around : mirrorClock d 4 < mirrorClock d 1 := by
      change 1-d 1 < 1-d 4
      have before : d 4 < d 1 := E.mono overlap
      linarith only [before]
    have rr : 1-r 2 < 1-r 1 := by
      have ht := P.sorted (by decide : (1:Fin 3) < 2)
      linarith only [ht]
    have sr : 1-r 1 < 1-r 0 := by
      have ht := P.sorted (by decide : (0:Fin 3) < 1)
      linarith only [ht]
    have en : 1-e < 0 := sub_neg.mpr P.edge.1
    have OP := orient_ports R ha en hz hu hh around (unit_reflect (P.unit 2))
      (unit_reflect (P.unit 1)) (unit_reflect (P.unit 0)) rr sr
    exact ⟨E,r,e,Or.inr OP.ranked⟩

/-- Exact remaining gate: in the positive Radau packet the stated
monic cubic cannot satisfy all six true window functionals. This
theorem is conditional on a proof of that gate. -/
theorem no_actual_sole_inner_of_structural_gate {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (S : SoleInner q c)
    (cut : ∀ {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
      {a e u h z r₀ r₁ r₂ : L}, RankedPacket a e u h z r₀ r₁ r₂ → False) : False := by
  obtain ⟨E,r,e,P | P⟩ := actual_sole_inner_has_rank_packet M S
  · exact cut P
  · exact cut P

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
