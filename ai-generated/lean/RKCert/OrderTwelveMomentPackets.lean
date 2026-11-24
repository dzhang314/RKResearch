module

public import RKCert.PolynomialEndpointMoments
public import RKCert.StagePrimitives
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! # Fixed characteristic-zero moment packets for explicit order 12
All packets are certified by exact row combinations, not positivity.
The first coefficient is a stage-zero test, and the endpoint sample at one
is a chronological last-active-stage test. -/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 7000000

def mesh6Coeffs : Fin 7 → K := ![0, -1, 20, -120, 300, -330, 132]
noncomputable def mesh6 : K[X] := by classical exact Polynomial.ofFn 7 (mesh6Coeffs (K:=K))
omit [CharZero K] in
theorem mesh6_coeff (i : Fin 7) : (mesh6 (K:=K)).coeff i.val = mesh6Coeffs i := by
  classical
  unfold mesh6
  simp

omit [CharZero K] in
theorem mesh6_natDegree : (mesh6 (K:=K)).natDegree ≤ 6 := by
  classical
  unfold mesh6
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide) _)

def ghost7Coeffs : Fin 7 → K := ![0, -6, 105, -560, 1260, -1260, 462]
noncomputable def ghost7 : K[X] := by classical exact Polynomial.ofFn 7 (ghost7Coeffs (K:=K))
omit [CharZero K] in
theorem ghost7_coeff (i : Fin 7) : (ghost7 (K:=K)).coeff i.val = ghost7Coeffs i := by
  classical
  unfold ghost7
  simp

omit [CharZero K] in
theorem ghost7_natDegree : (ghost7 (K:=K)).natDegree ≤ 6 := by
  classical
  unfold ghost7
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide) _)

def ghost8Coeffs : Fin 7 → K := ![0, 5, -75, 350, -700, 630, -210]
noncomputable def ghost8 : K[X] := by classical exact Polynomial.ofFn 7 (ghost8Coeffs (K:=K))
omit [CharZero K] in
theorem ghost8_coeff (i : Fin 7) : (ghost8 (K:=K)).coeff i.val = ghost8Coeffs i := by
  classical
  unfold ghost8
  simp

omit [CharZero K] in
theorem ghost8_natDegree : (ghost8 (K:=K)).natDegree ≤ 6 := by
  classical
  unfold ghost8
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by decide) _)

theorem last_zero_decoder (a : Fin 7 → K) (h0 : a 0 = 0) (h1 : (∑ i, a i) = 0)
    (hh : ∀ k : Fin 5, moment a 1 k.val = 0) : a = 0 := by
  norm_num [Fin.sum_univ_succ] at h1
  have h2 := hh 0
  have h3 := hh 1
  have h4 := hh 2
  have h5 := hh 3
  have h6 := hh 4
  norm_num [moment, Fin.sum_univ_succ] at h2 h3 h4 h5 h6
  have e0 : a 0 = 0 := by linear_combination 1 * h0
  have e1 : a 1 = 0 := by linear_combination (-36) * h0 + (-6) * h1 + 630 * h2 + (-6720) * h3 + 22680 * h4 + (-30240) * h5 + 13860 * h6
  have e2 : a 2 = 0 := by linear_combination 315 * h0 + 105 * h1 + (-7350) * h2 + 88200 * h3 + (-317520) * h4 + 441000 * h5 + (-207900) * h6
  have e3 : a 3 = 0 := by linear_combination (-1120) * h0 + (-560) * h1 + 29400 * h2 + (-376320) * h3 + 1411200 * h4 + (-2016000) * h5 + 970200 * h6
  have e4 : a 4 = 0 := by linear_combination 1890 * h0 + 1260 * h1 + (-52920) * h2 + 705600 * h3 + (-2721600) * h4 + 3969000 * h5 + (-1940400) * h6
  have e5 : a 5 = 0 := by linear_combination (-1512) * h0 + (-1260) * h1 + 44100 * h2 + (-604800) * h3 + 2381400 * h4 + (-3528000) * h5 + 1746360 * h6
  have e6 : a 6 = 0 := by linear_combination 462 * h0 + 462 * h1 + (-13860) * h2 + 194040 * h3 + (-776160) * h4 + 1164240 * h5 + (-582120) * h6
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

theorem terminal_decoder (a : Fin 7 → K) (h0 : a 0 = 0) (h1 : (∑ i, a i) = 1)
    (hh : ∀ k : Fin 5, moment a 1 k.val - moment a 1 (k.val+1) = 0) : a = mesh6Coeffs := by
  norm_num [Fin.sum_univ_succ] at h1
  have h2 := hh 0
  have h3 := hh 1
  have h4 := hh 2
  have h5 := hh 3
  have h6 := hh 4
  norm_num [moment, Fin.sum_univ_succ] at h2 h3 h4 h5 h6
  have e0 : a 0 = 0 := by linear_combination 1 * h0
  have e1 : a 1 = (-1) := by linear_combination (-41) * h0 + (-1) * h1 + 840 * h2 + (-10080) * h3 + 37800 * h4 + (-55440) * h5 + 27720 * h6
  have e2 : a 2 = 20 := by linear_combination 400 * h0 + 20 * h1 + (-10920) * h2 + 148680 * h3 + (-597240) * h4 + 914760 * h5 + (-471240) * h6
  have e3 : a 3 = (-120) := by linear_combination (-1560) * h0 + (-120) * h1 + 47880 * h2 + (-698040) * h3 + 2930760 * h4 + (-4629240) * h5 + 2439360 * h6
  have e4 : a 4 = 300 := by linear_combination 2850 * h0 + 300 * h1 + (-93240) * h2 + 1418760 * h3 + (-6141240) * h4 + 9923760 * h5 + (-5322240) * h6
  have e5 : a 5 = (-330) := by linear_combination (-2442) * h0 + (-330) * h1 + 83160 * h2 + (-1302840) * h3 + 5765760 * h4 + (-9480240) * h5 + 5155920 * h6
  have e6 : a 6 = 132 := by linear_combination 792 * h0 + 132 * h1 + (-27720) * h2 + 443520 * h3 + (-1995840) * h4 + 3326400 * h5 + (-1829520) * h6
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

theorem ghost7_decoder (a : Fin 7 → K) (h0 : a 0 = 0)
    (hh : ∀ k : Fin 5, moment a 1 k.val = 0) : a = (a 6 / 462) • ghost7Coeffs := by
  have h2 := hh 0
  have h3 := hh 1
  have h4 := hh 2
  have h5 := hh 3
  have h6 := hh 4
  norm_num [moment, Fin.sum_univ_succ] at h2 h3 h4 h5 h6
  have e0 : a 0 = 0 * a 6 := by linear_combination 1 * h0
  have e1 : a 1 = (-1 / 77) * a 6 := by linear_combination (-30) * h0 + 450 * h2 + (-4200) * h3 + 12600 * h4 + (-15120) * h5 + 6300 * h6
  have e2 : a 2 = (5 / 22) * a 6 := by linear_combination 210 * h0 + (-4200) * h2 + 44100 * h3 + (-141120) * h4 + 176400 * h5 + (-75600) * h6
  have e3 : a 3 = (-40 / 33) * a 6 := by linear_combination (-560) * h0 + 12600 * h2 + (-141120) * h3 + 470400 * h4 + (-604800) * h5 + 264600 * h6
  have e4 : a 4 = (30 / 11) * a 6 := by linear_combination 630 * h0 + (-15120) * h2 + 176400 * h3 + (-604800) * h4 + 793800 * h5 + (-352800) * h6
  have e5 : a 5 = (-30 / 11) * a 6 := by linear_combination (-252) * h0 + 6300 * h2 + (-75600) * h3 + 264600 * h4 + (-352800) * h5 + 158760 * h6
  funext i
  fin_cases i
  · change a 0 = (a 6 / (462:K)) * (0:K)
    linear_combination e0
  · change a 1 = (a 6 / (462:K)) * (-6:K)
    linear_combination e1
  · change a 2 = (a 6 / (462:K)) * (105:K)
    linear_combination e2
  · change a 3 = (a 6 / (462:K)) * (-560:K)
    linear_combination e3
  · change a 4 = (a 6 / (462:K)) * (1260:K)
    linear_combination e4
  · change a 5 = (a 6 / (462:K)) * (-1260:K)
    linear_combination e5
  · change a 6 = (a 6 / (462:K)) * (462:K)
    ring

theorem ghost8_decoder (a : Fin 7 → K) (h0 : a 0 = 0) (h1 : (∑ i, a i) = 0)
    (hh : ∀ k : Fin 4, moment a 1 k.val = 0) : a = (a 6 / -210) • ghost8Coeffs := by
  norm_num [Fin.sum_univ_succ] at h1
  have h2 := hh 0
  have h3 := hh 1
  have h4 := hh 2
  have h5 := hh 3
  norm_num [moment, Fin.sum_univ_succ] at h2 h3 h4 h5
  have e0 : a 0 = 0 * a 6 := by linear_combination 1 * h0
  have e1 : a 1 = (-1 / 42) * a 6 := by linear_combination (-25) * h0 + 5 * h1 + 300 * h2 + (-2100) * h3 + 4200 * h4 + (-2520) * h5
  have e2 : a 2 = (5 / 14) * a 6 := by linear_combination 150 * h0 + (-60) * h1 + (-2400) * h2 + 18900 * h3 + (-40320) * h4 + 25200 * h5
  have e3 : a 3 = (-5 / 3) * a 6 := by linear_combination (-350) * h0 + 210 * h1 + 6300 * h2 + (-52920) * h3 + 117600 * h4 + (-75600) * h5
  have e4 : a 4 = (10 / 3) * a 6 := by linear_combination 350 * h0 + (-280) * h1 + (-6720) * h2 + 58800 * h3 + (-134400) * h4 + 88200 * h5
  have e5 : a 5 = (-3) * a 6 := by linear_combination (-126) * h0 + 126 * h1 + 2520 * h2 + (-22680) * h3 + 52920 * h4 + (-35280) * h5
  funext i
  fin_cases i
  · change a 0 = (a 6 / (-210:K)) * (0:K)
    linear_combination e0
  · change a 1 = (a 6 / (-210:K)) * (5:K)
    linear_combination e1
  · change a 2 = (a 6 / (-210:K)) * (-75:K)
    linear_combination e2
  · change a 3 = (a 6 / (-210:K)) * (350:K)
    linear_combination e3
  · change a 4 = (a 6 / (-210:K)) * (-700:K)
    linear_combination e4
  · change a 5 = (a 6 / (-210:K)) * (630:K)
    linear_combination e5
  · change a 6 = (a 6 / (-210:K)) * (-210:K)
    ring

end RKCert.Paired.OrderTwelve
