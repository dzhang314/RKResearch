module

public import RKCert.ReviewedNative.LobattoDIRK88PayCheck180
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK88

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 2800000
set_option maxRecDepth 12000

private theorem gradeOK_all (i : Fin Count) (hi : i.val < 200) : gradeOK i = true := by
  have hsplit : List.range 200 = List.range' 0 40 ++ List.range' 40 40 ++ List.range' 80 40 ++ List.range' 120 40 ++ List.range' 160 40 := by
    decide +kernel
  have allok : (List.range 200).all (fun n => gradeOK (tag n)) = true := by
    have h0 := gradeOK_span0
    have h40 := gradeOK_span40
    have h80 := gradeOK_span80
    have h120 := gradeOK_span120
    have h160 := gradeOK_span160
    unfold checkSpan at h0 h40 h80 h120 h160
    simp only [hsplit, List.all_append, h0, h40, h80, h120, h160, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem joinOK_all (i : Fin Count) (hi : i.val < 85) : joinOK i = true := by
  have hsplit : List.range 85 = List.range' 0 16 ++ List.range' 16 16 ++ List.range' 32 16 ++ List.range' 48 16 ++ List.range' 64 16 ++ List.range' 80 5 := by
    decide +kernel
  have allok : (List.range 85).all (fun n => joinOK (tag n)) = true := by
    have h0 := joinOK_span0
    have h16 := joinOK_span16
    have h32 := joinOK_span32
    have h48 := joinOK_span48
    have h64 := joinOK_span64
    have h80 := joinOK_span80
    unfold checkSpan at h0 h16 h32 h48 h64 h80
    simp only [hsplit, List.all_append, h0, h16, h32, h48, h64, h80, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem derivOK_all (i : Fin Count) (hi : i.val < 85) : derivOK i = true := by
  have hsplit : List.range 85 = List.range' 0 12 ++ List.range' 12 12 ++ List.range' 24 12 ++ List.range' 36 12 ++ List.range' 48 12 ++ List.range' 60 12 ++ List.range' 72 12 ++ List.range' 84 1 := by
    decide +kernel
  have allok : (List.range 85).all (fun n => derivOK (tag n)) = true := by
    have h0 := derivOK_span0
    have h12 := derivOK_span12
    have h24 := derivOK_span24
    have h36 := derivOK_span36
    have h48 := derivOK_span48
    have h60 := derivOK_span60
    have h72 := derivOK_span72
    have h84 := derivOK_span84
    unfold checkSpan at h0 h12 h24 h36 h48 h60 h72 h84
    simp only [hsplit, List.all_append, h0, h12, h24, h36, h48, h60, h72, h84, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem payOK_all (i : Fin Count) (hi : i.val < 200) : payOK i = true := by
  have hsplit : List.range 200 = List.range' 0 20 ++ List.range' 20 20 ++ List.range' 40 20 ++ List.range' 60 20 ++ List.range' 80 20 ++ List.range' 100 20 ++ List.range' 120 20 ++ List.range' 140 20 ++ List.range' 160 20 ++ List.range' 180 20 := by
    decide +kernel
  have allok : (List.range 200).all (fun n => payOK (tag n)) = true := by
    have h0 := payOK_span0
    have h20 := payOK_span20
    have h40 := payOK_span40
    have h60 := payOK_span60
    have h80 := payOK_span80
    have h100 := payOK_span100
    have h120 := payOK_span120
    have h140 := payOK_span140
    have h160 := payOK_span160
    have h180 := payOK_span180
    unfold checkSpan at h0 h20 h40 h60 h80 h100 h120 h140 h160 h180
    simp only [hsplit, List.all_append, h0, h20, h40, h60, h80, h100, h120, h140, h160, h180, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

theorem roots_correct : keys roots = ⟨1, 1, []⟩ := by decide +kernel

private theorem grade_pos (i : Fin Count) : 0 < (keys i).order :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (gradeOK_all i i.isLt)).1

private theorem grade_cut (i : Fin Count) {q : ℕ} (hq : q < 9)
    (hi : (keys i).order ≤ q) : i.val < cutoff q := by
  have h := (Bool.and_eq_true_iff.mp (gradeOK_all i i.isLt)).2
  exact (of_decide_eq_true (List.all_eq_true.mp h q (List.mem_range.mpr hq))) hi

private theorem before_seven_cut (i : Fin Count) (hi : (keys i).order < 8) :
    i.val < 85 := by
  have h := grade_cut i (q := 7) (by decide) (by omega)
  exact h

theorem joins_correct (i j : Fin Count) (hg : (keys i).order+(keys j).order ≤ 8) :
    keys (joins i j) = merged (keys i) (keys j) j := by
  have hj := grade_pos j
  have hi := before_seven_cut i (by omega)
  have hcut := grade_cut j (q := 8 - (keys i).order) (by omega) (by omega)
  have hjok := joinOK_all i hi
  have h := List.all_eq_true.mp hjok j.val (List.mem_range.mpr hcut)
  exact of_decide_eq_true (by simpa only [tag_val] using h)

theorem deriv_correct {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21)
    (i : Fin Count) (hi : (keys i).order < 8) :
    VecVal s (deriv i) = numA s *ᵥ decode (keys i) (fun j => VecVal s (deriv j)) := by
  have h := QExpr.checkVec_sound (derivOK_all i (before_seven_cut i hi))
    (y := s) (inner_zero (K := K))
  change VecVal s (act (stage i)) = VecVal s (deriv i) at h
  rw [act_val hs] at h
  simpa only [decode, stage, prodPacked_val hs] using h.symm

theorem pay_correct {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21) (i : Fin Count) :
    (((keys i).order*(keys i).forest:ℕ):K) *
      (VecVal s rawB ⬝ᵥ decode (keys i) (fun j => VecVal s (deriv j))) =
      (weightDen:K) * (stageDen:K)^((keys i).order-1) := by
  have h := QExpr.eqMod_sound (payOK_all i i.isLt) (y := s) (inner_zero (K := K))
  rw [QExpr.val_scale, sumWord_val hs, QExpr.val_const] at h
  have hh : (Expr.atom [((keys i).order*(keys i).forest:ℕ)]).val (0:K) =
        (((keys i).order*(keys i).forest:ℕ):K) := by simp [Expr.val, coeval, horner]
  rw [hh, Int.cast_mul, Int.cast_pow] at h
  simpa only [decode, stage, prodPacked_val hs] using h

theorem moments {K : Type*} [CommRing K] {s : K} (hs : s^2 = 21) :
    ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 8 →
      (t.factorial:K) * (VecVal s rawB ⬝ᵥ Φ t (numA s)) =
      (weightDen:K) * (stageDen:K)^((t.order:ℕ)-1) := by
  intro t ht
  obtain ⟨i, ho, hf, hv⟩ :=
    cover (p := 8) roots_correct joins_correct (deriv_correct hs) t ht
  have hfac : (t.factorial:ℕ) = (keys i).order*(keys i).forest := by
    rw [factorial, PNat.mul_coe, ho, hf]
  change ((t.factorial:ℕ):K) * (VecVal s rawB ⬝ᵥ Φ t (numA s)) = _
  rw [hv, hfac, ← ho]
  exact pay_correct hs i

end RKResearch.Certified.LobattoDIRK88
