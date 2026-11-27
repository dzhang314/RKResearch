module
public import RKCert.ReviewedNative.ERK8CharElevenCensus

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual omitted-factor shape in characteristic eleven

This file transports the paid five- and seven-off tableau arguments up to
their omitted-factor data. In characteristic 11 the scalar resultant does
not give a contradiction, but pins the omitted factor and hence the whole
fitted head. These are necessary conditions on the **original Fin 10
tableau**. They are not exclusions of the remaining branches. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Module Polynomial OneOff Reverse ERKTaggedHorizon
open ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

private theorem order8_paid_end (H : ERKEvenHorizon A b 4) :
    b (Fin.last 9) ≠ 0 ∧ nodes A (Fin.last 9) = 1 ∧
      Pi.single (Fin.last 9) 1 ∈ treeSpace A 4 := by
  obtain ⟨t, hmax, hlive, hc, hm⟩ := H.terminal
  have ht : t = Fin.last 9 := le_antisymm (Fin.le_last t) (hmax (Fin.last 9))
  subst t
  exact ⟨hlive.live, hc, by simpa only [coordinate_as_single] using hm⟩

private theorem order8_paid_four_profile {v : Fin 10 → K}
    (ho : HasOrder 8 A b) (hv : v ∈ treeSpace A 4) (hF : zeroSpace A 4 = band A 2) :
    ∃ Q R : K[X], Q.natDegree ≤ 4 ∧ R.natDegree ≤ 2 ∧
      evalNodes A Q + diag (g A) (evalNodes A R) = v := by
  rw [treeSpace_coeff_sup ho (q:=4) (by decide), Submodule.mem_sup] at hv
  obtain ⟨u, ⟨a, rfl⟩, w, hw, rfl⟩ := hv
  obtain ⟨R, hd, he⟩ := band_iff.mp (hF ▸ hw)
  refine ⟨ofFn 5 a, R, Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _), hd, ?_⟩
  rw [ofFn_eval A 4, ←he]

private theorem order8_paid_lobatto_hull (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (hM : (cleanKnots A).card = 5) (h1 : (1 : K) ∈ cleanKnots A)
    (cancel : ∀ x ∈ offKnots A, offMass A b x = 0) :
    nodalHull (((cleanKnots A).erase 1).erase 0) = RKResearch.Certified.Graded.LobattoEight.lobattoCubic := by
  let S := ((cleanKnots A).erase 1).erase 0
  let L := nodalHull S
  have h0 := zero_mem_cleanKnots (s:=9) ha
  have ht := Finset.card_erase_add_one h1
  have hs : S.card + 1 = ((cleanKnots A).erase 1).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one, h0⟩)
  have ld : L.natDegree = 3 := by rw [show L.natDegree = S.card from natDegree_nodalHull S]; omega
  have he := beta_cubic_from_probes_paid ho L ld.le (fun j => by
    change probe A b j.val (evalNodes A ((X^2-X)*nodalHull S)) = 0
    rw [←RKResearch.Certified.Graded.LobattoEight.nodalHull_two_endpoint_factor (cleanKnots A) h0 h1]
    exact probe_zero_of_clean_roots cancel _ (fun _ hx => nodalHull_eval_of_mem hx) j.val)
  have hc : L.coeff 3 = 1 := ld ▸ (monic_nodalHull S).coeff_natDegree
  simpa [hc] using he

private theorem order8_paid_terminal_hull {Q R : K[X]}
    (hv : evalNodes A Q + diag (g A) (evalNodes A R) = Pi.single (Fin.last 9) 1)
    (hQ : Q.natDegree ≤ 4) (hc : nodes A (Fin.last 9) = 1) (hi : g A (Fin.last 9) = 0)
    (hM : (cleanKnots A).card = 5) :
    ∃ a : K, a ≠ 0 ∧ Q = C a * nodalHull ((cleanKnots A).erase 1) := by
  let T := (cleanKnots A).erase 1
  let H := nodalHull T
  let a := (H.eval 1)⁻¹
  have hH : H.eval 1 ≠ 0 := RKResearch.Certified.Graded.LobattoEight.nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)
  have ht : T.card + 1 = (cleanKnots A).card := Finset.card_erase_add_one
    (mem_cleanKnots.mpr ⟨Fin.last 9, hi, hc⟩)
  have hd : H.natDegree = 4 := by rw [show H.natDegree = T.card from natDegree_nodalHull _]; omega
  have hd' := (natDegree_C_mul_le a H).trans hd.le
  refine ⟨a, inv_ne_zero hH, ?_⟩
  change Q = C a * H
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (cleanKnots A) _ (by omega)
  intro x hx
  by_cases he : x = 1
  · rw [he, eval_mul, eval_C, inv_mul_cancel₀ hH]
    have hOne := profile_on_eval Q R hv hi
    rw [hc] at hOne
    simpa using hOne
  · obtain ⟨j, hj, hjc⟩ := mem_cleanKnots.mp hx
    have hne : j ≠ Fin.last 9 := fun h => he (hjc.symm.trans ((congrArg (nodes A) h).trans hc))
    rw [←hjc, profile_on_eval Q R hv hj, eval_mul, eval_C, hjc,
      nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨he, hx⟩)]
    change j ≠ (9 : Fin 10) at hne
    simp [hne]

/-- The first nonzero clean physical row pays both primitives if P(0)=0. -/
private theorem order8_paid_head_nonzero_at_origin {P : K[X]}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b) (hF : zeroSpace A 4 = band A 2)
    (dP : P.natDegree ≤ 2) (nz : P ≠ 0)
    (fit : ∀ i, g A i ≠ 0 → P.eval (nodes A i) = g A i)
    (ex : ∃ i, g A i = 0 ∧ nodes A i ≠ 0) : P.eval 0 ≠ 0 := by
  intro h0
  let U : Set (Fin 10) := {i | g A i = 0 ∧ nodes A i ≠ 0}
  obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min U (show U.Nonempty from ex)
  obtain ⟨hdi, hni⟩ := (show g A i = 0 ∧ nodes A i ≠ 0 from hi)
  let u := nodes A i
  change u ≠ 0 at hni
  have hzero (j : Fin 10) (hj : j < i) (hj' : g A j = 0) : nodes A j = 0 := by
    by_contra h
    exact hmin j ⟨hj', h⟩ hj
  have hg : mat A (g A) i = 0 := clean_four_vanish hF hdi
    (zeroSpace_mono A (by decide : 3 ≤ 4) (mat_zeroSpace ho 2 (by decide) (mDef_mem A 1)))
  have hXd : (X*P).natDegree ≤ 3 :=
    natDegree_mul_le_of_le (show (X : K[X]).natDegree ≤ 1 by simp) dP
  have hxP := on_primitive_zero_paid ha ho hF hdi (X*P) hXd
    (diag (nodes A) (g A)) (clean_mixed_defect_paid ho hF hdi) (fun j hj => by
      by_cases hj' : g A j = 0
      · simp [hj', hzero j hj hj']
      · simp [fit j hj'])
  have hp := on_primitive_zero_paid ha ho hF hdi P (by omega) (g A) hg (fun j hj => by
    by_cases hj' : g A j = 0
    · rw [hzero j hj hj', h0, hj']
    · exact fit j hj')
  rw [RKResearch.Certified.Graded.LobattoEight.primitive_eval_X_quadratic P dP] at hxP
  rw [RKResearch.Certified.Graded.LobattoEight.primitive_eval_quadratic P dP] at hp
  change P.coeff 0*u^2/2 + P.coeff 1*u^3/3 + P.coeff 2*u^4/4 = 0 at hxP
  change P.coeff 0*u + P.coeff 1*u^2/2 + P.coeff 2*u^3/3 = 0 at hp
  have hz : P.coeff 0 = 0 := (coeff_zero_eq_eval_zero P).trans h0
  have n2 := two_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have ex₀ : (P.coeff 0*u^2/2)*2=P.coeff 0*u^2 := div_mul_cancel₀ _ n2
  have ex₁ : (P.coeff 1*u^3/3)*3=P.coeff 1*u^3 := div_mul_cancel₀ _ n3
  have ex₂ : (P.coeff 2*u^4/4)*4=P.coeff 2*u^4 := div_mul_cancel₀ _ n4
  have ep₁ : (P.coeff 1*u^2/2)*2=P.coeff 1*u^2 := div_mul_cancel₀ _ n2
  have ep₂ : (P.coeff 2*u^3/3)*3=P.coeff 2*u^3 := div_mul_cancel₀ _ n3
  have Hx : 6*P.coeff 0*u^2+4*P.coeff 1*u^3+3*P.coeff 2*u^4=0 := by
    linear_combination 12*hxP-6*ex₀-4*ex₁-3*ex₂
  have Hp : 6*P.coeff 0*u+3*P.coeff 1*u^2+2*P.coeff 2*u^3=0 := by
    linear_combination 6*hp-3*ep₁-2*ep₂
  have h2 : P.coeff 2*u^4 = 0 := by linear_combination 3*Hx-4*u*Hp+6*u^2*hz
  have h2' := (mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ hni)
  have h1 : 3*(P.coeff 1*u^2) = 0 := by linear_combination Hp-6*u*hz-2*u^3*h2'
  have h1' := (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left n3)).resolve_right (pow_ne_zero _ hni)
  apply nz
  rw [RKResearch.Certified.Graded.LobattoEight.quadratic_coeff_expand P dP, hz, h1', h2']
  simp

/-- Omitted root and strict physical-prefix evidence, before using a
characteristic on the purely scalar equations. -/
structure OmittedProfile (A : Matrix (Fin 10) (Fin 10) K)
    (P : K[X]) (u a : K) : Prop where
  degree : P.natDegree ≤ 2
  fit : ∀ j, g A j ≠ 0 → P.eval (nodes A j) = g A j
  fourthBand : zeroSpace A 4 = band A 2
  terminal_clean : g A (Fin.last 9) = 0
  terminal_clock : nodes A (Fin.last 9) = 1
  terminal_unique : ∀ j, g A j = 0 → nodes A j = 1 → j = Fin.last 9
  clean_roots : ∀ x ∈ cleanKnots A, x = 0 ∨ x = 1 ∨ lobattoCubic.eval x = 0
  omitted_mem : u ∈ cleanKnots A
  scale_ne : a ≠ 0
  factor : lobattoCubic = (X-C u)*(C a*P)
  primitive_zero : (primitive (X*(C a*P))).eval u = 0

private theorem omitted_primitive_zero
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b) (hF : zeroSpace A 4 = band A 2)
    {P : K[X]} (dP : P.natDegree ≤ 2)
    (fit : ∀ j, g A j ≠ 0 → P.eval (nodes A j) = g A j)
    (last : ∀ j, g A j = 0 → nodes A j = 1 → j = Fin.last 9)
    (on : ∀ x ∈ cleanKnots A, x = 0 ∨ x = 1 ∨ RKResearch.Certified.Graded.LobattoEight.lobattoCubic.eval x = 0)
    {u a : K} (hu : u ∈ cleanKnots A) (an : a ≠ 0)
    (fac : RKResearch.Certified.Graded.LobattoEight.lobattoCubic = (X-C u)*(C a*P)) : (primitive (X*(C a*P))).eval u = 0 := by
  let U : Set (Fin 10) := {j | g A j = 0 ∧ nodes A j = u}
  have hU : U.Nonempty := mem_cleanKnots.mp hu
  obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min U hU
  obtain ⟨hdi, hci⟩ := (show g A i = 0 ∧ nodes A i = u from hi)
  have hpre (j : Fin 10) (hj : j < i) (hdj : g A j = 0) :
      nodes A j = 0 ∨ P.eval (nodes A j) = 0 := by
    have hne : nodes A j ≠ u := fun e => hmin j ⟨hdj, e⟩ hj
    rcases on _ (mem_cleanKnots.mpr ⟨j, hdj, rfl⟩) with h0 | h1 | hr
    · exact Or.inl h0
    · exact False.elim ((ne_of_lt (hj.trans_le (Fin.le_last i))) (last j hdj h1))
    · rw [fac, eval_mul, eval_mul, eval_C, eval_sub, eval_X, eval_C] at hr
      exact Or.inr ((mul_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr hne))).resolve_left an)
  have hdeg : (C a*P).natDegree ≤ 2 := (natDegree_C_mul_le _ _).trans dP
  have hX : (X*(C a*P)).natDegree ≤ 3 :=
    natDegree_mul_le_of_le (show (X : K[X]).natDegree ≤ 1 by simp) hdeg
  have hv : mat A (a • diag (nodes A) (g A)) i = 0 := by
    rw [map_smul, Pi.smul_apply, clean_mixed_defect_paid ho hF hdi, smul_zero]
  have hp := on_primitive_zero_paid ha ho hF hdi _ hX _ hv (fun j hj => by
    by_cases hj' : g A j = 0
    · rcases hpre j hj hj' with h | h <;> simp [hj', h]
    · simp [fit j hj', mul_left_comm])
  rw [hci] at hp
  exact hp

theorem five_off_omitted_profile
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (hN : (offKnots A).card = 5) :
    ∃ P u a, OmittedProfile A P u a := by
  have H := order8_paid_even_horizon ha ho
  obtain ⟨h3, h4, cap⟩ := order8_paid_ranks ha ho H
  obtain ⟨hb, hc, hE⟩ := order8_paid_end H
  obtain ⟨P, dP, nz, _, hF, fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨Q, R, dQ, dR, hv⟩ := order8_paid_four_profile ho hE hF
  have cancel : ∀ x ∈ offKnots A, offMass A b x = 0 :=
    offMass_zero_of_head ho fit (by omega)
  have state : Pi.single (Fin.last 9) 1 ∈ onOffSpace A :=
    hv ▸ pairProfile_mem_onOffSpace fit Q R
  have hi := on_of_state_single state hb cancel
  have h1 : (1 : K) ∈ cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 9, hi, hc⟩
  have hM := order8_paid_five_clean ha ho cap (by omega) cancel
  have hS := order8_paid_lobatto_hull ha ho hM h1 cancel
  obtain ⟨a, an, hQ⟩ := order8_paid_terminal_hull hv dQ hc hi hM
  have h0 : (0 : K) ∈ (cleanKnots A).erase 1 :=
    Finset.mem_erase.mpr ⟨zero_ne_one, zero_mem_cleanKnots (s:=9) ha⟩
  rw [RKResearch.Certified.Graded.LobattoEight.nodalHull_erase_factor _ h0, hS, map_zero, sub_zero] at hQ
  have hL : (RKResearch.Certified.Graded.LobattoEight.lobattoCubic : K[X]) ≠ 0 := by
    intro hz
    have d := lobattoCubic_degree_paid (K:=K)
    simp [hz] at d
  have dQ4 : Q.natDegree = 4 := by
    rw [hQ, natDegree_C_mul an, natDegree_mul X_ne_zero hL, natDegree_X,
      lobattoCubic_degree_paid]
  have hOff := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (Q+P*R)
    (offKnots A) (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := mem_offKnots.mp hx
      have hne : j ≠ Fin.last 9 := fun e => hj (e ▸ hi)
      rw [profile_off_eval hv fit hj]
      change j ≠ (9 : Fin 10) at hne
      simp [hne]) (by
        have d := natDegree_add_le_of_degree_le dQ (natDegree_mul_le_of_le dP dR)
        omega)
  have hD : Q = P*(-R) := by rw [mul_neg, eq_neg_iff_add_eq_zero]; exact hOff
  have hD' := Polynomial.natDegree_mul_le (p:=P) (q:=-R)
  rw [←hD, natDegree_neg, dQ4] at hD'
  have dP2 : P.natDegree = 2 := by omega
  have pn := order8_paid_head_nonzero_at_origin ha ho hF dP nz fit
    (exists_nonzero_on_of_card (A:=A) (by omega))
  have hz : (-R).eval 0 = 0 := by
    have eq := congrArg (fun V : K[X] => V.eval (0 : K)) hD
    have q0 : Q.eval 0 = 0 := by rw [hQ]; simp
    rw [q0, eval_mul] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_left pn
  obtain ⟨W, hW⟩ := Polynomial.X_dvd_iff.mpr ((coeff_zero_eq_eval_zero (-R)).trans hz)
  have hcan : C a*RKResearch.Certified.Graded.LobattoEight.lobattoCubic = P*W := by
    apply mul_left_cancel₀ (X_ne_zero : (X : K[X]) ≠ 0)
    rw [hQ, hW] at hD
    calc
      _ = C a*(X*RKResearch.Certified.Graded.LobattoEight.lobattoCubic) := by ring
      _ = P*(X*W) := hD
      _ = _ := by ring
  have hdiv : P ∣ RKResearch.Certified.Graded.LobattoEight.lobattoCubic := by
    refine ⟨C a⁻¹*W, ?_⟩
    calc
      _ = C a⁻¹*(C a*RKResearch.Certified.Graded.LobattoEight.lobattoCubic) := by
        rw [←mul_assoc, ←map_mul, inv_mul_cancel₀ an, map_one, one_mul]
      _ = _ := by rw [hcan]; ring
  obtain ⟨u, t, tn, fac⟩ := lobatto_divisor_linear_factor_paid dP2 hdiv
  have huS : u ∈ ((cleanKnots A).erase 1).erase 0 := by
    by_contra h
    exact RKResearch.Certified.Graded.LobattoEight.nodalHull_eval_ne_zero_of_notMem h
      (hS.symm ▸ RKResearch.Certified.Graded.LobattoEight.lobatto_isRoot_of_linear fac)
  have on (x : K) (hx : x ∈ cleanKnots A) :
      x = 0 ∨ x = 1 ∨ RKResearch.Certified.Graded.LobattoEight.lobattoCubic.eval x = 0 := by
    by_cases h0x : x = 0
    · exact Or.inl h0x
    by_cases h1x : x = 1
    · exact Or.inr (Or.inl h1x)
    exact Or.inr (Or.inr (hS ▸ nodalHull_eval_of_mem
      (Finset.mem_erase.mpr ⟨h0x, Finset.mem_erase.mpr ⟨h1x, hx⟩⟩)))
  have hu := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huS)
  have last := single_profile_on_unique hv hi hc
  exact ⟨P,u,t,dP,fit,hF,hi,hc,last,on,hu,tn,fac,
    omitted_primitive_zero ha ho hF dP fit last on hu tn fac⟩

theorem seven_off_omitted_profile
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (hN : 7 ≤ (offKnots A).card) (t3 : (cleanKnots A).card = 3) :
    ∃ P u a, OmittedProfile A P u a := by
  have H := order8_paid_even_horizon ha ho
  obtain ⟨h3, h4, _⟩ := order8_paid_ranks ha ho H
  obtain ⟨_, hc, hE⟩ := order8_paid_end H
  obtain ⟨P, dP, nz, _, hF, fit⟩ := two_curve_head h3 h4 (by omega)
  let T := cleanKnots A
  change T.card=3 at t3
  let L := nodalHull T
  have t0 : (0 : K) ∈ T := zero_mem_cleanKnots (s:=9) ha
  obtain ⟨Q, R, dQ, dR, hv⟩ := order8_paid_four_profile ho hE hF
  have d := natDegree_add_le_of_degree_le dQ (natDegree_mul_le_of_le dP dR)
  have margin : (Q+P*R).natDegree + 1 < (offKnots A).card := by omega
  have hi := profile_terminal_on_of_large_off (s:=9) margin fit hv
  have h1 : (1 : K) ∈ T := mem_cleanKnots.mpr ⟨Fin.last 9, hi, hc⟩
  let S := (T.erase 1).erase 0
  have c1 : (T.erase 1).card + 1 = T.card := Finset.card_erase_add_one h1
  have c0 : S.card + 1 = (T.erase 1).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one, t0⟩)
  obtain ⟨u, huS⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
  have hull : L = (X^2-X)*(X-C u) := by
    rw [show L = nodalHull T from rfl, RKResearch.Certified.Graded.LobattoEight.nodalHull_two_endpoint_factor T t0 h1]
    change (X^2-X)*nodalHull S = _
    rw [huS]
    simp [nodalHull]
  let Y := P*(X-C u)
  have eq : (X^2-X)*Y = P*L := by rw [hull]; dsimp [Y]; ring
  have dY : Y.natDegree ≤ 3 := natDegree_mul_le_of_le dP (natDegree_X_sub_C_le u)
  have hY := beta_cubic_from_probes_paid ho Y dY (fun j => by
    rw [eq]
    have pay : j.val + T.card + 3 ≤ 8 := by have := j.isLt; omega
    exact on_hull_times_head_probes ho fit j.val pay)
  let a := Y.coeff 3
  have an : a ≠ 0 := by
    intro z
    change Y = C a*RKResearch.Certified.Graded.LobattoEight.lobattoCubic at hY
    rw [z, map_zero, zero_mul] at hY
    exact mul_ne_zero nz (X_sub_C_ne_zero u) hY
  have fac : RKResearch.Certified.Graded.LobattoEight.lobattoCubic = (X-C u)*(C a⁻¹*P) := by
    calc
      _ = C a⁻¹*(C a*RKResearch.Certified.Graded.LobattoEight.lobattoCubic) := by
        rw [←mul_assoc, ←map_mul, inv_mul_cancel₀ an, map_one, one_mul]
      _ = C a⁻¹*Y := by rw [←hY]
      _ = _ := by dsimp [Y]; ring
  have hus : u ∈ S := by rw [huS]; simp
  have hu := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hus)
  have on (x : K) (hx : x ∈ cleanKnots A) :
      x = 0 ∨ x = 1 ∨ RKResearch.Certified.Graded.LobattoEight.lobattoCubic.eval x = 0 := by
    by_cases h0 : x = 0
    · exact Or.inl h0
    by_cases h1x : x = 1
    · exact Or.inr (Or.inl h1x)
    have hx' : x ∈ S := Finset.mem_erase.mpr ⟨h0, Finset.mem_erase.mpr ⟨h1x, hx⟩⟩
    rw [huS, Finset.mem_singleton] at hx'
    rw [hx']
    exact Or.inr (Or.inr (RKResearch.Certified.Graded.LobattoEight.lobatto_isRoot_of_linear fac))
  have last := single_profile_on_unique hv hi hc
  exact ⟨P,u,a⁻¹,dP,fit,hF,hi,hc,last,on,hu,inv_ne_zero an,fac,
    omitted_primitive_zero ha ho hF dP fit last on hu (inv_ne_zero an) fac⟩

theorem omitted_scalar_equations (ho : HasOrder 8 A b)
    {P : K[X]} (hP : P.natDegree≤2) {u : K} (hu : u≠0)
    (hf : lobattoCubic = (X-C u)*P) (hprim : (primitive (X*P)).eval u=0) :
    14*u^3-21*u^2+9*u-1=0 ∧ 91*u^2-105*u+27=0 := by
  have d0 : ((-1:K)/14)*14=-1 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d1 : ((9:K)/14)*14=9 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d2 : ((-3:K)/2)*2=-3 := div_mul_cancel₀ _ (two_ne ho)
  have rr := lobatto_isRoot_of_linear hf
  simp only [lobattoCubic,eval_add,eval_monomial,pow_zero,pow_one,mul_one,one_mul] at rr
  have root : 14*u^3-21*u^2+9*u-1=0 := by
    linear_combination 14*rr-d0-u*d1-7*u^2*d2
  have hcoef (n : ℕ) : (lobattoCubic : K[X]).coeff (n+1) = P.coeff n-u*P.coeff (n+1) := by
    rw [hf,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
  have h3 := hcoef 2
  have h2 := hcoef 1
  have h1 := hcoef 0
  have uz : P.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [lobattoCubic,coeff_add,coeff_monomial,Finsupp.single_apply,uz] at h3 h2 h1
  have H3 : P.coeff 2-1=0 := by linear_combination -h3
  have H2 : 2*P.coeff 1-2*u*P.coeff 2+3=0 := by linear_combination -2*h2+d2
  have H1 : 14*P.coeff 0-14*u*P.coeff 1-9=0 := by linear_combination -14*h1+d1
  rw [primitive_eval_X_quadratic P hP] at hprim
  have np3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have np4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have e₀ : (P.coeff 0*u^2/2)*2=P.coeff 0*u^2 := div_mul_cancel₀ _ (two_ne ho)
  have e₁ : (P.coeff 1*u^3/3)*3=P.coeff 1*u^3 := div_mul_cancel₀ _ np3
  have e₂ : (P.coeff 2*u^4/4)*4=P.coeff 2*u^4 := div_mul_cancel₀ _ np4
  have m : 6*P.coeff 0*u^2+4*P.coeff 1*u^3+3*P.coeff 2*u^4=0 := by
    linear_combination 12*hprim-6*e₀-4*e₁-3*e₂
  have z : u^2*(91*u^2-105*u+27)=0 := by
    linear_combination 7*m-91*u^4*H3-35*u^3*H2-3*u^2*H1
  have g := (mul_eq_zero.mp z).resolve_left (pow_ne_zero _ hu)
  exact ⟨root,g⟩

/-- The exceptional diagonal-free head, defined over the whole coefficient
field, not only over a finite extension of the prime field. -/
noncomputable def exceptionalQuadratic : K[X] := X^2-X+C 8

@[simp] theorem exceptionalQuadratic_eval (x : K) :
    (exceptionalQuadratic : K[X]).eval x = x^2-x+8 := by
  simp [exceptionalQuadratic]

theorem exceptionalQuadratic_degree : (exceptionalQuadratic : K[X]).natDegree ≤ 2 := by
  unfold exceptionalQuadratic
  apply natDegree_add_le_of_degree_le
  · rw [natDegree_X_pow_sub_X (by decide : 1 < 2)]
  · simp

theorem lobatto_split_eleven (ho : HasOrder 8 A b) (p : (11:K)=0) :
    (lobattoCubic : K[X]) = (X-C 6)*exceptionalQuadratic := by
  have c0 : ((-1:K)/14)=-48 :=
    (div_eq_iff (fourteen_ne ho)).mpr (by linear_combination 61*p)
  have c1 : ((9:K)/14)=14 :=
    (div_eq_iff (fourteen_ne ho)).mpr (by linear_combination -17*p)
  have c2 : ((-3:K)/2)=-7 :=
    (div_eq_iff (ERK8PaidField.two_ne ho)).mpr (by linear_combination p)
  rw [lobattoCubic,c0,c1,c2,exceptionalQuadratic]
  simp only [←C_mul_X_pow_eq_monomial,pow_zero,pow_one,mul_one,map_neg,map_ofNat,map_one,one_mul]
  ring

/-- The fitted head and physical clean-clock consequences of the scalar
root identity. In particular the off values avoid the quadratic zeros. -/
structure ExceptionalHead (A : Matrix (Fin 10) (Fin 10) K) (theta : K) : Prop where
  scale_ne : theta ≠ 0
  fit : ∀ j, g A j ≠ 0 →
    theta * (exceptionalQuadratic : K[X]).eval (nodes A j) = g A j
  fourthBand : zeroSpace A 4 = band A 2
  terminal_clean : g A (Fin.last 9) = 0
  terminal_clock : nodes A (Fin.last 9) = 1
  terminal_unique : ∀ j, g A j = 0 → nodes A j = 1 → j = Fin.last 9
  center_mem : (6:K) ∈ cleanKnots A
  clean_roots : ∀ j, g A j = 0 →
    nodes A j = 0 ∨ nodes A j = 1 ∨ nodes A j = 6 ∨
      (exceptionalQuadratic : K[X]).eval (nodes A j) = 0

theorem exceptional_head_of_omitted (ho : HasOrder 8 A b) (p : (11:K)=0)
    {P : K[X]} {u a : K} (H : OmittedProfile A P u a) :
    u = 6 ∧ P = C a⁻¹*exceptionalQuadratic ∧ ExceptionalHead A a⁻¹ := by
  have d := (natDegree_C_mul_le a P).trans H.degree
  have root := lobatto_isRoot_of_linear H.factor
  have un : u ≠ 0 := fun e => (lobatto_zero_ne ho) (e ▸ root)
  obtain ⟨hr,hs⟩ := omitted_scalar_equations ho d un H.factor H.primitive_zero
  have hu := omitted_root_eq_six p hr hs
  have hf := H.factor
  rw [hu,lobatto_split_eleven ho p] at hf
  have q : C a*P=(exceptionalQuadratic : K[X]) :=
    (mul_left_cancel₀ (X_sub_C_ne_zero (6:K)) hf).symm
  have shape : P=C a⁻¹*exceptionalQuadratic := by
    rw [←q,←mul_assoc,←map_mul,inv_mul_cancel₀ H.scale_ne,map_one,one_mul]
  refine ⟨hu,shape,inv_ne_zero H.scale_ne,?_,H.fourthBand,H.terminal_clean,
    H.terminal_clock,H.terminal_unique,hu ▸ H.omitted_mem,?_⟩
  · intro j gj
    have ev := H.fit j gj
    rw [shape,eval_mul,eval_C] at ev
    exact ev
  · intro j gj
    rcases H.clean_roots _ (mem_cleanKnots.mpr ⟨j,gj,rfl⟩) with h0 | h1 | hr
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · rw [lobatto_split_eleven ho p,eval_mul,eval_sub,eval_X,eval_C] at hr
      rcases mul_eq_zero.mp hr with h|h
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
      · exact Or.inr (Or.inr (Or.inr h))

/-- In the five- and seven-off branches the omitted chronology singles
out 6 and forces the full exceptional quadratic, not just a root guard. -/
theorem order8_paid_five_or_seven_exceptional_head
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (branch : (offKnots A).card=5 ∨
      ((offKnots A).card=7 ∧ (cleanKnots A).card=3)) :
    ∃ theta : K, ExceptionalHead A theta := by
  obtain ⟨P,u,a,Hp⟩ : ∃ P u a, OmittedProfile A P u a := by
    rcases branch with five | ⟨seven,cl⟩
    · exact five_off_omitted_profile ha ho five
    · exact seven_off_omitted_profile ha ho (by omega) cl
  exact ⟨a⁻¹,(exceptional_head_of_omitted ho p Hp).2.2⟩

/-- The first quadratic clean clock cannot be paid by off senders
alone. This is a direct characteristic-11 check of the scaled primitive. -/
theorem primitive_X_exceptional_ne (ho : HasOrder 8 A b) (p : (11:K)=0)
    {u : K} (root : (exceptionalQuadratic : K[X]).eval u = 0) :
    (primitive (X*(exceptionalQuadratic : K[X]))).eval u ≠ 0 := by
  let Q : K[X] := exceptionalQuadratic
  have dQ : Q.natDegree≤2 := exceptionalQuadratic_degree
  have h0 : Q.coeff 0=8 := by simp [Q,exceptionalQuadratic,coeff_X_pow,coeff_X]
  have h1 : Q.coeff 1=-1 := by simp [Q,exceptionalQuadratic,coeff_X_pow,coeff_X]
  have h2 : Q.coeff 2=1 := by simp [Q,exceptionalQuadratic,coeff_X_pow,coeff_X]
  have n2 := ERK8PaidField.two_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  intro z
  change (primitive (X*Q)).eval u=0 at z
  rw [primitive_eval_X_quadratic Q dQ,h0,h1,h2] at z
  have d0 := div_mul_cancel₀ ((8:K)*u^2) n2
  have d1 := div_mul_cancel₀ ((-1:K)*u^3) n3
  have d2 := div_mul_cancel₀ ((1:K)*u^4) n4
  have m : 48*u^2-4*u^3+3*u^4=0 := by linear_combination 12*z-6*d0-4*d1-3*d2
  rw [exceptionalQuadratic_eval] at root
  have l : 3+9*u=0 := by
    linear_combination m-(3*u^2-u+23)*root+(17-2*u)*p
  have e : u=7 := by
    linear_combination 5*l-(2+4*u)*p
  rw [e] at root
  exact one_ne_zero (by linear_combination 2*root-9*p : (1:K)=0)

/-- Actual earliest nonzero clean row for an exceptional fitted head.
No weights, tag ordering, or root splitting are assumed beyond the
independently earned head and terminal data. -/
theorem first_nonzero_clean_is_center (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) (p : (11:K)=0) {theta : K} (H : ExceptionalHead A theta) :
    ∃ i : Fin 10, g A i=0 ∧ nodes A i=6 ∧
      (∀ j, j < i → g A j=0 → nodes A j=0) := by
  have six_ne : (6:K)≠0 := (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  have five_ne : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have six_one : (6:K)≠1 := fun h => five_ne (by linear_combination h)
  obtain ⟨fixed,gf,cf⟩ := mem_cleanKnots.mp H.center_mem
  have fixed_lt : fixed < Fin.last 9 := by
    apply lt_of_le_of_ne (Fin.le_last fixed)
    intro e
    exact six_one (cf.symm.trans ((congrArg (nodes A) e).trans H.terminal_clock))
  let S : Set (Fin 10) := {i | g A i=0 ∧ nodes A i≠0}
  have hnS : S.Nonempty := ⟨fixed,gf,cf.symm ▸ six_ne⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S hnS
  obtain ⟨gi,ni⟩ := (show g A i=0 ∧ nodes A i≠0 from hi)
  have prep (j : Fin 10) (hj : j < i) (gj : g A j=0) : nodes A j=0 := by
    by_contra n
    exact hmin j ⟨gj,n⟩ hj
  have nOne : nodes A i ≠ 1 := by
    intro c1
    exact hmin fixed ⟨gf,cf.symm ▸ six_ne⟩ ((H.terminal_unique i gi c1).symm ▸ fixed_lt)
  refine ⟨i,gi,?_,prep⟩
  rcases H.clean_roots i gi with h0|h1|h6|hq
  · exact (ni h0).elim
  · exact (nOne h1).elim
  · exact h6
  let Q : K[X] := exceptionalQuadratic
  have dQ : Q.natDegree≤2 := exceptionalQuadratic_degree
  have dP := (natDegree_C_mul_le theta Q).trans dQ
  have dXP : (X*(C theta*Q)).natDegree≤3 :=
    natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) dP
  have hz := on_primitive_zero_paid ha ho H.fourthBand gi (X*(C theta*Q)) dXP
    (diag (nodes A) (g A)) (clean_mixed_defect_paid ho H.fourthBand gi) (fun j lj => by
      simp only [eval_mul,eval_X,eval_C,diag_apply]
      by_cases gj : g A j=0
      · simp [prep j lj gj]
      · rw [H.fit j gj])
  have z' : theta*(primitive (X*Q)).eval (nodes A i)=0 := by
    rwa [show X*(C theta*Q)=theta • (X*Q) by rw [smul_eq_C_mul]; ring,
      map_smul,eval_smul,smul_eq_mul] at hz
  exact (primitive_X_exceptional_ne ho p hq
    ((mul_eq_zero.mp z').resolve_left H.scale_ne)).elim

/-- Distinct off clocks in the strict prefix of an actual physical row. -/
noncomputable def offPrefixClocks (A : Matrix (Fin 10) (Fin 10) K) (i : Fin 10) : Finset K :=
  ((Finset.univ : Finset (Fin 10)).filter (fun j => j < i ∧ g A j≠0)).image (nodes A)

/-- Fewer than three earlier off knots would allow a degree-one selector
whose defect-weighted values reproduce c on the whole strict prefix.
Its clean receiver has zero defect action, a contradiction to c²/2. -/
theorem first_nonzero_clean_has_three_off_clocks
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (B : zeroSpace A 4 = band A 2) {P : K[X]}
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    {i : Fin 10} (gi : g A i=0) (ni : nodes A i≠0)
    (clean0 : ∀ j, j < i → g A j=0 → nodes A j=0) :
    3 ≤ (offPrefixClocks A i).card := by
  let S := offPrefixClocks A i
  by_contra! small
  change S.card < 3 at small
  let f : K → K := fun x => x/P.eval x
  let Q : K[X] := Lagrange.interpolate S id f
  have d : Q.natDegree≤1 := by
    by_cases z : Q=0
    · simp [z]
    have d := (natDegree_lt_iff_degree_lt z).mpr
      (Lagrange.degree_interpolate_lt f (Set.injOn_id _) (s:=S))
    change Q.natDegree < S.card at d
    omega
  let v := diag (g A) (evalNodes A Q)
  have mem : v ∈ zeroSpace A 3 := band_le A 1 (band_iff.mpr ⟨Q,d,rfl⟩)
  have killed := clean_four_vanish B gi (mat_zeroSpace ho 3 (by decide) mem)
  have eq : mat A v i = mat A (nodes A) i := by
    apply causal_action_eq ha
    intro j hj
    by_cases gj : g A j=0
    · simp [v,gj,clean0 j hj gj]
    · have m : nodes A j∈S :=
        Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,gj⟩,rfl⟩
      have val := Lagrange.eval_interpolate_at_node f (Set.injOn_id _) m
      change Q.eval (nodes A j) = nodes A j / P.eval (nodes A j) at val
      change g A j*Q.eval (nodes A j)=nodes A j
      rw [val,fit j gj,mul_div_cancel₀ _ gj]
  have gx := (g_apply_paid ho (by decide) i).symm
  rw [gi,←eq,killed,zero_sub,neg_eq_zero] at gx
  exact (div_ne_zero (pow_ne_zero _ ni) (ERK8PaidField.two_ne ho)) gx

/-- Entire literal exceptional prefix package for the five/seven branch. -/
theorem order8_five_seven_exceptional_prefix
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (branch : (offKnots A).card=5 ∨
      ((offKnots A).card=7 ∧ (cleanKnots A).card=3)) :
    ∃ (theta : K) (i : Fin 10), ExceptionalHead A theta ∧
      g A i=0 ∧ nodes A i=6 ∧
      (∀ j, j < i → g A j=0 → nodes A j=0) ∧ 3 ≤ (offPrefixClocks A i).card := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p branch
  obtain ⟨i,gi,ci,cp⟩ := first_nonzero_clean_is_center ha ho p H
  have nz : nodes A i≠0 := by
    rw [ci]
    exact (ho.natCast_isUnit (n:=6) (by decide) (by decide)).ne_zero
  refine ⟨theta,i,H,gi,ci,cp,?_⟩
  apply first_nonzero_clean_has_three_off_clocks ha ho H.fourthBand (P:=C theta*exceptionalQuadratic)
    (fun j gj => by simpa only [eval_mul,eval_C] using H.fit j gj) gi nz cp

/-- When the tag count uses all ten rows, clock equality within a tag
forces physical equality, even if there are equal clocks across tags. -/
theorem order8_tag_injective_of_full_count
    (total : (cleanKnots A).card+(offKnots A).card=10) :
    (∀ i j, g A i=0 → g A j=0 → nodes A i=nodes A j → i=j) ∧
    (∀ i j, g A i≠0 → g A j≠0 → nodes A i=nodes A j → i=j) := by
  let S := (Finset.univ : Finset (Fin 10)).filter (fun i => g A i=0)
  let T := (Finset.univ : Finset (Fin 10)).filter (fun i => g A i≠0)
  have cl : S.image (nodes A)=cleanKnots A := rfl
  have off : T.image (nodes A)=offKnots A := rfl
  have sums : S.card+T.card=10 := by
    simpa [S,T] using (Finset.card_filter_add_card_filter_not
      (s:=Finset.univ) (fun i : Fin 10 => g A i=0))
  have ls := Finset.card_image_le (s:=S) (f:=nodes A)
  have lt := Finset.card_image_le (s:=T) (f:=nodes A)
  rw [cl] at ls
  rw [off] at lt
  have sc : (S.image (nodes A)).card=S.card := by rw [cl]; omega
  have tc : (T.image (nodes A)).card=T.card := by rw [off]; omega
  exact ⟨fun i j gi gj eq => (Finset.card_image_iff.mp sc)
      (by simp [S,gi]) (by simp [S,gj]) eq,
    fun i j gi gj eq => (Finset.card_image_iff.mp tc)
      (by simp [T,gi]) (by simp [T,gj]) eq⟩

/-- Signed cancellation at a five-off tag is actual zero weight because
every tag is physically unique. No sign or distinct-clock assumption
across tags is used. -/
theorem five_off_actual_weights_zero
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (five : (offKnots A).card=5)
    {P : K[X]} (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    (i : Fin 10) (gi : g A i≠0) : b i=0 := by
  have cancel := offMass_zero_of_head ho fit (by omega)
  obtain ⟨_,_,cap⟩ := order8_paid_ranks ha ho (order8_paid_even_horizon ha ho)
  have cl := order8_paid_five_clean ha ho cap (by omega) cancel
  have inj := (order8_tag_injective_of_full_count (A:=A) (by omega)).2
  have hz := cancel (nodes A i) (mem_offKnots.mpr ⟨i,gi,rfl⟩)
  unfold offMass at hz
  rw [Finset.sum_eq_single i] at hz
  · simpa [gi] using hz
  · intro j _ ji
    by_cases gj : g A j=0
    · simp [gj]
    · have nr : ¬ (g A j≠0 ∧ nodes A j=nodes A i) := fun hp => ji (inj j i gj gi hp.2)
      simp [nr]
  · intro h
    exact (h (Finset.mem_univ i)).elim

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_paid_five_or_seven_exceptional_head
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.first_nonzero_clean_is_center

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_five_seven_exceptional_prefix
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_tag_injective_of_full_count
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.five_off_actual_weights_zero
