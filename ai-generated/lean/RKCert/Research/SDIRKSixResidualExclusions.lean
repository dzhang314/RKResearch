module
public import RKCert.Research.SDIRKSixResidualCharts
public import RKCert.ReviewedNative.CommonDiagonalGoodScalar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
public section

namespace RKResearch.Certified.Graded.SDIRKSix
open scoped Matrix
variable {K : Type*} [Field K]

private theorem unpackSix (f : Fin 6 → K) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ]
  ring

private theorem scaledMoment {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K}
    (ho : HasOrder 6 A b) (z : K) (j : ℕ) (hj : j < 6) :
    (j.succ : K) * ∑ i, b i * (nodes (scaleTable z A) i)^j = z^j := by
  have h := ho.hasQuadratureOrder j hj
  change (j.succ : K) * ∑ i, b i * ((A *ᵥ 1) i)^j = 1 at h
  have he : (∑ i, b i * (nodes (scaleTable z A) i)^j) =
      z^j * ∑ i, b i * ((A *ᵥ 1) i)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [nodes_scaleTable]
    change b i * (z*((A *ᵥ 1) i))^j = _
    rw [mul_pow]
    ring
  rw [he]
  linear_combination z^j * h

private theorem scaledSeedSum {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K}
    (ho : HasOrder 6 A b) (z : K) :
    (∑ i, b i * seed (scaleTable z A) i) = 0 := by
  have hs := probe_zeroSpace ho (by decide : 0+2+1≤6) (seed_zero A)
  change (∑ i, (b i*(nodes A i)^0)*seed A i) = 0 at hs
  simp only [pow_zero, mul_one] at hs
  rw [seed_scaleTable]
  change (∑ i, b i * (z^2 * seed A i)) = 0
  conv_lhs => enter [2, i]; rw [mul_left_comm]
  rw [← Finset.mul_sum, hs, mul_zero]

private theorem zero_first_weight_of_last_seed_zero {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) (hseed : seed A 5 = 0) : b 0 = 0 := by
  obtain ⟨μ,hμ⟩ := weighted_seed_proportional ho ha he hγ
  have h5 := LinearMap.congr_fun hμ (coord 5)
  change μ * probe A b 0 (volterra A (coord 5)) = probe A b 0 (diag (seed A) (coord 5)) at h5
  rw [commutator_coord_five ha he, diag_coord] at h5
  simp only [map_smul,smul_eq_mul,probe_coord,pow_zero,mul_one,hseed,zero_mul] at h5
  have hb5 := (order_six_terminal_chronology ho ha he hγ).1
  have hm : μ = 0 := (mul_eq_zero.mp h5).resolve_right (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hγ)) hb5)
  have h0 := LinearMap.congr_fun hμ (coord 0)
  change μ * probe A b 0 (volterra A (coord 0)) = probe A b 0 (diag (seed A) (coord 0)) at h0
  rw [hm, zero_mul, diag_coord, map_smul, probe_coord, seed0 ha he] at h0
  simp only [pow_zero, mul_one, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left (pow_ne_zero 2 hγ)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
theorem six_strict_impossible_241 [CharP K 241] {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) : False := by
  obtain ⟨z,u,v,h⟩ := order_six_six_stage_chart ho ha he hγ
  obtain ⟨hz,hu,hv⟩ := chartValues_241 h
  subst z u v
  have hchar : (241 : K) = 0 := CharP.cast_eq_zero K 241
  let B := scaleTable (2:K) A
  let c := nodes B
  let g := seed B
  have h10 : B 1 0 = (82:K) := h.u_eq.symm
  have hc0 : c 0 = 1 := h.clock₀
  have hc1 : c 1 = 83 := by
    calc c 1 = 1+(82:K) := h.clock₁
         _ = _ := by ring
  have hc2 : c 2 = 165 := by
    calc c 2 = 1+2*(82:K) := h.clock₂
         _ = _ := by ring
  have hc4 : c 4 = 160 := by
    calc c 4 = (2:K)-1-82 := h.clock₄
         _ = _ := by linear_combination (norm := ring) (-1) * hchar
  have hc5 : c 5 = 1 := by
    calc c 5 = (2:K)-1 := h.clock₅
         _ = _ := by ring
  have m0 := scaledMoment ho (2:K) 0 (by decide)
  change ((Nat.succ 0 : ℕ):K) * (∑ i, b i * (c i)^0) = (2:K)^0 at m0
  rw [unpackSix] at m0
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m0
  have m1 := scaledMoment ho (2:K) 1 (by decide)
  change ((Nat.succ 1 : ℕ):K) * (∑ i, b i * (c i)^1) = (2:K)^1 at m1
  rw [unpackSix] at m1
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m1
  have m2 := scaledMoment ho (2:K) 2 (by decide)
  change ((Nat.succ 2 : ℕ):K) * (∑ i, b i * (c i)^2) = (2:K)^2 at m2
  rw [unpackSix] at m2
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m2
  have m3 := scaledMoment ho (2:K) 3 (by decide)
  change ((Nat.succ 3 : ℕ):K) * (∑ i, b i * (c i)^3) = (2:K)^3 at m3
  rw [unpackSix] at m3
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m3
  have m4 := scaledMoment ho (2:K) 4 (by decide)
  change ((Nat.succ 4 : ℕ):K) * (∑ i, b i * (c i)^4) = (2:K)^4 at m4
  rw [unpackSix] at m4
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m4
  have m5 := scaledMoment ho (2:K) 5 (by decide)
  change ((Nat.succ 5 : ℕ):K) * (∑ i, b i * (c i)^5) = (2:K)^5 at m5
  rw [unpackSix] at m5
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5] at m5
  have hmask0 : (b 3)*((c 3)^4 + 73*(c 3)^3 + 40*(c 3)^2 + 99*(c 3) + 28) = 201 := by
    linear_combination (norm := ring) (28) * m0 + (170) * m1 + (174) * m2 + (199) * m3 + (193) * m4 + (-11*(b 0) - 191933803*(b 1) - 2982774283*(b 2) - 4*(b 3)*(c 3)^4 - 3*(b 3)*(c 3)^3 - 2*(b 3)*(c 3)^2 - (b 3)*(c 3) - 2637743708*(b 4) - 11*(b 5) + 23) * hchar
  have hmask1 : (b 3)*(c 3)*((c 3)^4 + 73*(c 3)^3 + 40*(c 3)^2 + 99*(c 3) + 28) = 13 := by
    linear_combination (norm := ring) (14) * m1 + (33) * m2 + (10) * m3 + (111) * m4 + (201) * m5 + (-8*(b 0) - 19820937508*(b 1) - 613705647720*(b 2) - 5*(b 3)*(c 3)^5 - 2*(b 3)*(c 3)^4 - 526233015680*(b 4) - 8*(b 5) + 35) * hchar
  have hc3 : c 3 = 78 := by
    linear_combination (norm := ring) (6) * hmask1 + (-6*(c 3)) * hmask0 + (-5*(c 3)) * hchar
  rw [hc3] at m0 m1 m2 m3 m4 m5
  have hg0 : g 0 = 1 := by simpa only [one_pow] using seed0 h.front_data.tri h.front_data.single
  have hg1 : g 1 = 189 := by
    have hC := h.front_data.clock 1
    change (c 1 - 1) * g 1 = kap (B 1 0) * tapMap B 1 g 1 at hC
    rw [h10,hc1] at hC
    simp only [kap] at hC
    have hP := h.front_data.profile 1
    change B 1 0 * leg 2 (c 1) =
      B 1 0 * leg 2 1 * g 1 +
      (leg 2 (1+B 1 0) - kap (B 1 0) * leg 2 1) * tapMap B 1 g 1 at hP
    rw [h10,hc1] at hP
    simp only [leg,kap] at hP
    linear_combination (norm := ring) (97) * hC + (189) * hP + (-33*(g 1) + 8644601*(tapMap B 1 g 1) - 709073757) * hchar
  have hg2 : g 2 = 172 := by
    have hC := h.front_data.clock 2
    change (c 2 - 1) * g 2 = kap (B 1 0) * tapMap B 1 g 2 at hC
    rw [h10,hc2] at hC
    simp only [kap] at hC
    have hP := h.front_data.profile 2
    change B 1 0 * leg 2 (c 2) =
      B 1 0 * leg 2 1 * g 2 +
      (leg 2 (1+B 1 0) - kap (B 1 0) * leg 2 1) * tapMap B 1 g 2 at hP
    rw [h10,hc2] at hP
    simp only [leg,kap] at hP
    linear_combination (norm := ring) (169) * hC + (215) * hP + (-115*(g 2) + 9832209*(tapMap B 1 g 2) - 6453378252) * hchar
  have hg3 : g 3 = 172 := by
    have hC := h.front_data.clock 3
    change (c 3 - 1) * g 3 = kap (B 1 0) * tapMap B 1 g 3 at hC
    rw [h10,hc3] at hC
    simp only [kap] at hC
    have hP := h.front_data.profile 3
    change B 1 0 * leg 2 (c 3) =
      B 1 0 * leg 2 1 * g 3 +
      (leg 2 (1+B 1 0) - kap (B 1 0) * leg 2 1) * tapMap B 1 g 3 at hP
    rw [h10,hc3] at hP
    simp only [leg,kap] at hP
    linear_combination (norm := ring) (72) * hC + (26) * hP + (-23*(g 3) + 1187608*(tapMap B 1 g 3) - 80765964) * hchar
  have hg4 : g 4 = 189 := by
    have hC := h.front_data.clock 4
    change (c 4 - 1) * g 4 = kap (B 1 0) * tapMap B 1 g 4 at hC
    rw [h10,hc4] at hC
    simp only [kap] at hC
    have hP := h.front_data.profile 4
    change B 1 0 * leg 2 (c 4) =
      B 1 0 * leg 2 1 * g 4 +
      (leg 2 (1+B 1 0) - kap (B 1 0) * leg 2 1) * tapMap B 1 g 4 at hP
    rw [h10,hc4] at hP
    simp only [leg,kap] at hP
    linear_combination (norm := ring) (144) * hC + (52) * hP + (-95*(g 4) + 2375216*(tapMap B 1 g 4) - 1422365517) * hchar
  have hg5 : g 5 = 1 := by
    have hr := h.seed_ratio
    change g 4 = kap 82 * g 5 at hr
    rw [hg4] at hr
    simp only [kap] at hr
    linear_combination (norm := ring) (-190) * hr + (5171*(g 5) + 149) * hchar
  have hs := scaledSeedSum ho (2:K)
  change (∑ i, b i * g i) = 0 at hs
  rw [unpackSix] at hs
  simp only [hg0,hg1,hg2,hg3,hg4,hg5] at hs
  have bad : (1:K) = 0 := by
    linear_combination (norm := ring) (77) * m0 + (235) * m1 + (58) * m2 + (199) * m3 + (153) * m4 + (-113) * hs + (-9*(b 0) - 152539313*(b 1) - 2367630726*(b 2) - 119067789*(b 3) - 2093839520*(b 4) - 9*(b 5) + 20) * hchar
  exact one_ne_zero bad

theorem seven_le_of_strict_order_six_char_241 [CharP K 241] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) : 7 ≤ s := by
  have hh := nonsingular_stageFloor_field ho ha (fun i => he i ▸ hγ) (by decide)
  change 6 ≤ s at hh
  by_contra hs
  have hsix : s = 6 := by omega
  subst s
  exact six_strict_impossible_241 ho ha he hγ

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
theorem six_strict_impossible_255919 [CharP K 255919] {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) : False := by
  obtain ⟨z,u,v,h⟩ := order_six_six_stage_chart ho ha he hγ
  obtain ⟨hz,hu,hv⟩ := chartValues_255919 h
  subst z u v
  have hchar : (255919 : K) = 0 := CharP.cast_eq_zero K 255919
  let B := scaleTable (47708:K) A
  let c := nodes B
  let g := seed B
  have h10 : B 1 0 = (250912:K) := h.u_eq.symm
  have hc0 : c 0 = 1 := h.clock₀
  have hc1 : c 1 = 250913 := by
    calc c 1 = 1+(250912:K) := h.clock₁
         _ = _ := by ring
  have hc2 : c 2 = 245906 := by
    calc c 2 = 1+2*(250912:K) := h.clock₂
         _ = _ := by linear_combination (norm := ring) (1) * hchar
  have hc4 : c 4 = 52714 := by
    calc c 4 = (47708:K)-1-250912 := h.clock₄
         _ = _ := by linear_combination (norm := ring) (-1) * hchar
  have hc5 : c 5 = 47707 := by
    calc c 5 = (47708:K)-1 := h.clock₅
         _ = _ := by ring
  have hg5 : g 5 = 0 := by
    have hC := h.front_data.clock 5
    change (c 5 - 1) * g 5 = kap (B 1 0) * tapMap B 1 g 5 at hC
    rw [h10,hc5] at hC
    simp only [kap] at hC
    linear_combination (norm := ring) (25873) * hC + (-4823*(g 5) - 6364783873*(tapMap B 1 g 5)) * hchar
  have hs5 : seed A 5 = 0 := by
    have h0 : (47708 : K)^2 * seed A 5 = 0 := by
      simpa only [g,B,seed_scaleTable,Pi.smul_apply,smul_eq_mul] using hg5
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 h.z_ne)
  have hb0 := zero_first_weight_of_last_seed_zero ho ha he hγ hs5
  have m0 := scaledMoment ho (47708:K) 0 (by decide)
  change ((Nat.succ 0 : ℕ):K) * (∑ i, b i * (c i)^0) = (47708:K)^0 at m0
  rw [unpackSix] at m0
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m0
  have m1 := scaledMoment ho (47708:K) 1 (by decide)
  change ((Nat.succ 1 : ℕ):K) * (∑ i, b i * (c i)^1) = (47708:K)^1 at m1
  rw [unpackSix] at m1
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m1
  have m2 := scaledMoment ho (47708:K) 2 (by decide)
  change ((Nat.succ 2 : ℕ):K) * (∑ i, b i * (c i)^2) = (47708:K)^2 at m2
  rw [unpackSix] at m2
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m2
  have m3 := scaledMoment ho (47708:K) 3 (by decide)
  change ((Nat.succ 3 : ℕ):K) * (∑ i, b i * (c i)^3) = (47708:K)^3 at m3
  rw [unpackSix] at m3
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m3
  have m4 := scaledMoment ho (47708:K) 4 (by decide)
  change ((Nat.succ 4 : ℕ):K) * (∑ i, b i * (c i)^4) = (47708:K)^4 at m4
  rw [unpackSix] at m4
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m4
  have m5 := scaledMoment ho (47708:K) 5 (by decide)
  change ((Nat.succ 5 : ℕ):K) * (∑ i, b i * (c i)^5) = (47708:K)^5 at m5
  rw [unpackSix] at m5
  simp only [Nat.cast_succ,Nat.cast_zero,hc0,hc1,hc2,hc4,hc5,hb0] at m5
  have hmask0 : (b 3)*((c 3)^4 - 85402*(c 3)^3 + 39326*(c 3)^2 + 28077*(c 3) + 66467) = 158780 := by
    linear_combination (norm := ring) (66467) * m0 + (141998) * m1 + (98415) * m2 + (106609) * m3 + (51184) * m4 + (-3963667660122176073728*(b 1) - 3656631041285791029761*(b 2) - (b 3)*(c 3)^4 - 2*(b 3)*(c 3)^3 - (b 3)*(c 3)^2 - (b 3)*(c 3) - 7721813602378710465*(b 4) - 5180185298380956648*(b 5) + 1036132975468862737) * hchar
  have hmask1 : (b 3)*(c 3)*((c 3)^4 - 85402*(c 3)^3 + 39326*(c 3)^2 + 28077*(c 3) + 66467) = 225071 := by
    linear_combination (norm := ring) (161193) * m1 + (9359) * m2 + (137791) * m3 + (136471) * m4 + (213266) * m5 + (-4972640718968848868545690438*(b 1) - 4495902794816488193914608952*(b 2) - 5*(b 3)*(c 3)^5 - 3*(b 3)*(c 3)^4 - 2*(b 3)*(c 3)^3 - (b 3)*(c 3) - 2035188304898476007438184*(b 4) - 1235622291763253518126266*(b 5) + 205959093445721302844755) * hchar
  have hc3 : c 3 = 57721 := by
    linear_combination (norm := ring) (188677) * hmask1 + (-188677*(c 3)) * hmask0 + (165934 - 117061*(c 3)) * hchar
  rw [hc3] at m0 m1 m2 m3 m4 m5
  have hb5 : b 5 = 0 := by
    linear_combination (norm := ring) (136821) * m0 + (182432) * m1 + (136134) * m2 + (204871) * m3 + (165924) * m4 + (-12849050766206290806361*(b 1) - 11853727235639381836339*(b 2) - 35984833810317912089*(b 3) - 25031605757173845875*(b 4) - 16792451572821657442*(b 5) + 3358789300804687611) * hchar
  exact (order_six_terminal_chronology ho ha he hγ).1 hb5

theorem seven_le_of_strict_order_six_char_255919 [CharP K 255919] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) (hγ : γ ≠ 0) : 7 ≤ s := by
  have hh := nonsingular_stageFloor_field ho ha (fun i => he i ▸ hγ) (by decide)
  change 6 ≤ s at hh
  by_contra hs
  have hsix : s = 6 := by omega
  subst s
  exact six_strict_impossible_255919 ho ha he hγ
end RKResearch.Certified.Graded.SDIRKSix

namespace RKResearch

open Certified.Graded.SDIRKSix
private theorem erkFloorSixResidual : erkUniformFloor 6 = 7 := by
  have h := congrArg (fun xs : List ℕ => xs[6]?) erkUniformFloor_through_twenty
  change some (erkUniformFloor 6) = some 7 at h
  exact Option.some.inj h

/-- No unit or even nonzero diagonal assumption is necessary for the
characteristic-241 commutative-ring endpoint. -/
theorem HasOrder.common_diagonal_order_six_stages_char_241
    {R : Type*} [CommRing R] [Nontrivial R] [CharP R 241] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) : 7 ≤ s := by
  have hn : ¬ IsNilpotent (1 : R) := by
    rintro ⟨n, hn⟩
    exact one_ne_zero (by simpa only [one_pow] using hn)
  have hs := ho.common_diagonal_stage_floor_at_scalar (d := (1 : R)) (k := 7) ha he
    (Or.inr hn) (fun K _ f _ ho' ha' he' hg' => by
      have hz : ((241 : ℕ) : K) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg f (CharP.cast_eq_zero R 241)
      let : CharP K 241 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 241)).mpr hz
      exact seven_le_of_strict_order_six_char_241 ho' ha' he' hg')
  simpa only [erkFloorSixResidual, min_self] using hs

/-- No unit or even nonzero diagonal assumption is necessary for the
characteristic-255919 commutative-ring endpoint. -/
theorem HasOrder.common_diagonal_order_six_stages_char_255919
    {R : Type*} [CommRing R] [Nontrivial R] [CharP R 255919] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) : 7 ≤ s := by
  have hn : ¬ IsNilpotent (1 : R) := by
    rintro ⟨n, hn⟩
    exact one_ne_zero (by simpa only [one_pow] using hn)
  have hs := ho.common_diagonal_stage_floor_at_scalar (d := (1 : R)) (k := 7) ha he
    (Or.inr hn) (fun K _ f _ ho' ha' he' hg' => by
      have hz : ((255919 : ℕ) : K) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg f (CharP.cast_eq_zero R 255919)
      let : CharP K 255919 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 255919)).mpr hz
      exact seven_le_of_strict_order_six_char_255919 ho' ha' he' hg')
  simpa only [erkFloorSixResidual, min_self] using hs

end RKResearch
