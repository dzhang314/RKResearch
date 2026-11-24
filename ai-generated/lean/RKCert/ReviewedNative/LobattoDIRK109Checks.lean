module

public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck0
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck64
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck128
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck192
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck256
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck320
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck384
public import RKCert.ReviewedNative.LobattoDIRK109GradeCheck448
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck0
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck4
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck28
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck52
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck76
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck100
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck124
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck148
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck172
public import RKCert.ReviewedNative.LobattoDIRK109JoinCheck196
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck0
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck8
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck16
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck24
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck32
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck40
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck48
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck56
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck64
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck72
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck80
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck88
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck96
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck104
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck112
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck120
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck128
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck136
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck144
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck152
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck160
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck168
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck176
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck184
public import RKCert.ReviewedNative.LobattoDIRK109DerivCheck192
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck0
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck16
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck32
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck48
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck64
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck80
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck96
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck112
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck128
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck144
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck160
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck176
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck192
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck208
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck224
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck240
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck256
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck272
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck288
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck304
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck320
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck336
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck352
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck368
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck384
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck400
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck416
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck432
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck448
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck464
public import RKCert.ReviewedNative.LobattoDIRK109PayCheck480
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 3500000
set_option maxRecDepth 14000

private theorem gradeOK_all (i : Fin Count) (hi : i.val < 486) : gradeOK i = true := by
  have hsplit : List.range 486 = List.range' 0 64 ++ List.range' 64 64 ++ List.range' 128 64 ++ List.range' 192 64 ++ List.range' 256 64 ++ List.range' 320 64 ++ List.range' 384 64 ++ List.range' 448 38 := by
    decide +kernel
  have allok : (List.range 486).all (fun n => gradeOK (tag n)) = true := by
    have h0 := gradeOK_span0
    have h64 := gradeOK_span64
    have h128 := gradeOK_span128
    have h192 := gradeOK_span192
    have h256 := gradeOK_span256
    have h320 := gradeOK_span320
    have h384 := gradeOK_span384
    have h448 := gradeOK_span448
    unfold checkSpan at h0 h64 h128 h192 h256 h320 h384 h448
    simp only [hsplit, List.all_append, h0, h64, h128, h192, h256, h320, h384, h448, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem joinOK_all (i : Fin Count) (hi : i.val < 200) : joinOK i = true := by
  have hsplit : List.range 200 = List.range' 0 4 ++ List.range' 4 24 ++ List.range' 28 24 ++ List.range' 52 24 ++ List.range' 76 24 ++ List.range' 100 24 ++ List.range' 124 24 ++ List.range' 148 24 ++ List.range' 172 24 ++ List.range' 196 4 := by
    decide +kernel
  have allok : (List.range 200).all (fun n => joinOK (tag n)) = true := by
    have h0 := joinOK_span0
    have h4 := joinOK_span4
    have h28 := joinOK_span28
    have h52 := joinOK_span52
    have h76 := joinOK_span76
    have h100 := joinOK_span100
    have h124 := joinOK_span124
    have h148 := joinOK_span148
    have h172 := joinOK_span172
    have h196 := joinOK_span196
    unfold checkSpan at h0 h4 h28 h52 h76 h100 h124 h148 h172 h196
    simp only [hsplit, List.all_append, h0, h4, h28, h52, h76, h100, h124, h148, h172, h196, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem derivOK_all (i : Fin Count) (hi : i.val < 200) : derivOK i = true := by
  have hsplit : List.range 200 = List.range' 0 8 ++ List.range' 8 8 ++ List.range' 16 8 ++ List.range' 24 8 ++ List.range' 32 8 ++ List.range' 40 8 ++ List.range' 48 8 ++ List.range' 56 8 ++ List.range' 64 8 ++ List.range' 72 8 ++ List.range' 80 8 ++ List.range' 88 8 ++ List.range' 96 8 ++ List.range' 104 8 ++ List.range' 112 8 ++ List.range' 120 8 ++ List.range' 128 8 ++ List.range' 136 8 ++ List.range' 144 8 ++ List.range' 152 8 ++ List.range' 160 8 ++ List.range' 168 8 ++ List.range' 176 8 ++ List.range' 184 8 ++ List.range' 192 8 := by
    decide +kernel
  have allok : (List.range 200).all (fun n => derivOK (tag n)) = true := by
    have h0 := derivOK_span0
    have h8 := derivOK_span8
    have h16 := derivOK_span16
    have h24 := derivOK_span24
    have h32 := derivOK_span32
    have h40 := derivOK_span40
    have h48 := derivOK_span48
    have h56 := derivOK_span56
    have h64 := derivOK_span64
    have h72 := derivOK_span72
    have h80 := derivOK_span80
    have h88 := derivOK_span88
    have h96 := derivOK_span96
    have h104 := derivOK_span104
    have h112 := derivOK_span112
    have h120 := derivOK_span120
    have h128 := derivOK_span128
    have h136 := derivOK_span136
    have h144 := derivOK_span144
    have h152 := derivOK_span152
    have h160 := derivOK_span160
    have h168 := derivOK_span168
    have h176 := derivOK_span176
    have h184 := derivOK_span184
    have h192 := derivOK_span192
    unfold checkSpan at h0 h8 h16 h24 h32 h40 h48 h56 h64 h72 h80 h88 h96 h104 h112 h120 h128 h136 h144 h152 h160 h168 h176 h184 h192
    simp only [hsplit, List.all_append, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80, h88, h96, h104, h112, h120, h128, h136, h144, h152, h160, h168, h176, h184, h192, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

private theorem payOK_all (i : Fin Count) (hi : i.val < 486) : payOK i = true := by
  have hsplit : List.range 486 = List.range' 0 16 ++ List.range' 16 16 ++ List.range' 32 16 ++ List.range' 48 16 ++ List.range' 64 16 ++ List.range' 80 16 ++ List.range' 96 16 ++ List.range' 112 16 ++ List.range' 128 16 ++ List.range' 144 16 ++ List.range' 160 16 ++ List.range' 176 16 ++ List.range' 192 16 ++ List.range' 208 16 ++ List.range' 224 16 ++ List.range' 240 16 ++ List.range' 256 16 ++ List.range' 272 16 ++ List.range' 288 16 ++ List.range' 304 16 ++ List.range' 320 16 ++ List.range' 336 16 ++ List.range' 352 16 ++ List.range' 368 16 ++ List.range' 384 16 ++ List.range' 400 16 ++ List.range' 416 16 ++ List.range' 432 16 ++ List.range' 448 16 ++ List.range' 464 16 ++ List.range' 480 6 := by
    decide +kernel
  have allok : (List.range 486).all (fun n => payOK (tag n)) = true := by
    have h0 := payOK_span0
    have h16 := payOK_span16
    have h32 := payOK_span32
    have h48 := payOK_span48
    have h64 := payOK_span64
    have h80 := payOK_span80
    have h96 := payOK_span96
    have h112 := payOK_span112
    have h128 := payOK_span128
    have h144 := payOK_span144
    have h160 := payOK_span160
    have h176 := payOK_span176
    have h192 := payOK_span192
    have h208 := payOK_span208
    have h224 := payOK_span224
    have h240 := payOK_span240
    have h256 := payOK_span256
    have h272 := payOK_span272
    have h288 := payOK_span288
    have h304 := payOK_span304
    have h320 := payOK_span320
    have h336 := payOK_span336
    have h352 := payOK_span352
    have h368 := payOK_span368
    have h384 := payOK_span384
    have h400 := payOK_span400
    have h416 := payOK_span416
    have h432 := payOK_span432
    have h448 := payOK_span448
    have h464 := payOK_span464
    have h480 := payOK_span480
    unfold checkSpan at h0 h16 h32 h48 h64 h80 h96 h112 h128 h144 h160 h176 h192 h208 h224 h240 h256 h272 h288 h304 h320 h336 h352 h368 h384 h400 h416 h432 h448 h464 h480
    simp only [hsplit, List.all_append, h0, h16, h32, h48, h64, h80, h96, h112, h128, h144, h160, h176, h192, h208, h224, h240, h256, h272, h288, h304, h320, h336, h352, h368, h384, h400, h416, h432, h448, h464, h480, Bool.and_self]
  simpa only [tag_val] using (List.all_eq_true.mp allok i.val (List.mem_range.mpr hi))

theorem roots_correct : keys roots = ⟨1, 1, []⟩ := by decide +kernel

private theorem grade_pos (i : Fin Count) : 0 < (keys i).order :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (gradeOK_all i i.isLt)).1

private theorem grade_cut (i : Fin Count) {q : ℕ} (hq : q < 10)
    (hi : (keys i).order ≤ q) : i.val < cutoff q := by
  have h := (Bool.and_eq_true_iff.mp (gradeOK_all i i.isLt)).2
  exact (of_decide_eq_true (List.all_eq_true.mp h q (List.mem_range.mpr hq))) hi

private theorem before_eight_cut (i : Fin Count) (hi : (keys i).order < 9) :
    i.val < 200 := by
  have h := grade_cut i (q := 8) (by decide) (by omega)
  exact h

theorem joins_correct (i j : Fin Count) (hg : (keys i).order+(keys j).order ≤ 9) :
    keys (joins i j) = merged (keys i) (keys j) j := by
  have hj := grade_pos j
  have hi := before_eight_cut i (by omega)
  have hcut := grade_cut j (q := 9 - (keys i).order) (by omega) (by omega)
  have hjok := joinOK_all i hi
  have h := List.all_eq_true.mp hjok j.val (List.mem_range.mpr hcut)
  exact of_decide_eq_true (by simpa only [tag_val] using h)

theorem deriv_correct {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) (i : Fin Count) (hi : (keys i).order < 9) :
    VecVal x y (deriv i) = numA x y *ᵥ decode (keys i) (fun j => VecVal x y (deriv j)) := by
  have h := QExpr.checkVec_sound (derivOK_all i (before_eight_cut i hi)) (y := y) hx
  change VecVal x y (act (stage i)) = VecVal x y (deriv i) at h
  rw [act_val hy] at h
  simpa only [decode, stage, prodPacked_val hy] using h.symm

theorem pay_correct {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) (i : Fin Count) :
    (((keys i).order*(keys i).forest:ℕ):K) *
      (VecVal x y rawB ⬝ᵥ decode (keys i) (fun j => VecVal x y (deriv j))) =
      (weightDen:K) * (stageDen:K)^((keys i).order-1) := by
  have h := QExpr.eqMod_sound (payOK_all i i.isLt) (y := y) hx
  rw [QExpr.val_scale, sumWord_val hy, QExpr.val_const] at h
  have hh : (Expr.atom [((keys i).order*(keys i).forest:ℕ)]).val x =
        (((keys i).order*(keys i).forest:ℕ):K) := by simp [Expr.val, coeval, horner]
  rw [hh, Int.cast_mul, Int.cast_pow] at h
  simpa only [decode, stage, prodPacked_val hy] using h

theorem moments {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 9 →
      (t.factorial:K) * (VecVal x y rawB ⬝ᵥ Φ t (numA x y)) =
      (weightDen:K) * (stageDen:K)^((t.order:ℕ)-1) := by
  intro t ht
  obtain ⟨i, ho, hf, hv⟩ :=
    cover (p := 9) roots_correct joins_correct (deriv_correct hx hy) t ht
  have hfac : (t.factorial:ℕ) = (keys i).order*(keys i).forest := by
    rw [factorial, PNat.mul_coe, ho, hf]
  change ((t.factorial:ℕ):K) * (VecVal x y rawB ⬝ᵥ Φ t (numA x y)) = _
  rw [hv, hfac, ← ho]
  exact pay_correct hx hy i

end RKResearch.Certified.LobattoDIRK109
