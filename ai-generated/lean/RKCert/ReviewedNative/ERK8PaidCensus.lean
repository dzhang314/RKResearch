module

public import RKCert.ReviewedNative.ERK8PaidLobatto

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The actual tagged order-eight census in width ten outside characteristic 11
The only extra numerical guard is 11 ≠ 0; all other small denominators
used by this proof are paid by literal order eight.

For a strictly explicit ten-row tableau, the reviewed even horizon pays
all rank and endpoint inputs. A clock is tagged by the actual quadratic
stage defect; a clean row and a defective row at the same clock are not
identified. The disjunction is a necessary condition only, not an exclusion
of either remaining branch and not a numerical stage-floor theorem.
-/
namespace RKResearch.Certified.Graded.ERK8PaidField

open RKResearch Module Polynomial OneOff Reverse ERKTaggedHorizon RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- The certificate uses the original stage count and physical endpoint. -/
theorem order8_paid_even_horizon (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) : ERKEvenHorizon A b 4 :=
  erk_even_horizon_of_stage_cap ha ho (q:=4) (by decide) (by decide) (by decide)

theorem order8_paid_ranks (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (H : ERKEvenHorizon A b 4) :
    finrank K (zeroSpace A 3) = 2 ∧ finrank K (zeroSpace A 4) = 3 ∧
      finrank K (treeSpace A 5) ≤ 9 := by
  have hlo := zeroSpace_finrank ha ho (n:=2) (by decide)
  have sep := explicit_coeff_separated (s:=9) ha ho (q:=4) (by decide)
  have hstep := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_paid ha ho sep (j:=3) (by decide) (by decide) (by decide))
  change 2 ≤ finrank K (zeroSpace A 3) at hlo
  change finrank K (zeroSpace A 3) < finrank K (zeroSpace A 4) at hstep
  have h4 : finrank K (zeroSpace A 4) = 3 := H.defectRank
  have hback := backward_count ha ho 5 1 (by decide)
  omega

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

/-- The origin allows four shifted moments with only order eight paid. -/
private theorem order8_paid_anchored_zero (ho : HasOrder 8 A b) (L : K[X])
    (hd : L.natDegree ≤ 4) (hz : L.eval 0 = 0)
    (pay : ∀ j : Fin 4, probe A b j.val (evalNodes A L) = 0) : L = 0 := by
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero L).trans hz)
  by_cases h0 : Q = 0
  · simp [hQ, h0]
  have hqd : Q.natDegree ≤ 3 := by
    rw [hQ, natDegree_mul X_ne_zero h0, natDegree_X] at hd
    omega
  have hq := anchored_poly_zero_of_probes ho 3 (by decide) Q hqd (fun j => by
    rw [←hQ]
    exact pay j)
  simp [hQ, hq]

private theorem order8_paid_clean_floor (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (cancel : ∀ x ∈ offKnots A, offMass A b x = 0) :
    5 ≤ (cleanKnots A).card := by
  by_contra! small
  let L := nodalHull (cleanKnots A)
  have hL : L.natDegree ≤ 4 := (natDegree_nodalHull (cleanKnots A)).le.trans (by omega)
  have hz : L.eval 0 = 0 := nodalHull_eval_of_mem (zero_mem_cleanKnots (s:=9) ha)
  have pay (j : Fin 4) : probe A b j.val (evalNodes A L) = 0 :=
    probe_zero_of_clean_roots cancel L (fun _ hx => nodalHull_eval_of_mem hx) j.val
  exact (monic_nodalHull _).ne_zero (order8_paid_anchored_zero ho L hL hz pay)

theorem order8_paid_five_clean (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (cap : finrank K (treeSpace A 5) ≤ 9)
    (N : 4 ≤ (offKnots A).card)
    (cancel : ∀ x ∈ offKnots A, offMass A b x = 0) : (cleanKnots A).card = 5 := by
  have lo := order8_paid_clean_floor ha ho cancel
  by_contra hne
  have bigger : 6 ≤ (cleanKnots A).card := by omega
  have rank := gradeFiveState_rank bigger N
  have le := Submodule.finrank_mono (gradeFiveStateSpace_le A)
  omega

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

/-- This is the native chronologically first clean row at the omitted
Lobatto root. The final exclusion consumes only a polynomial scalar gate. -/
private theorem order8_paid_lobatto_factor_impossible
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b) (elev : (11:K)≠0) (hF : zeroSpace A 4 = band A 2)
    {P : K[X]} (dP : P.natDegree ≤ 2)
    (fit : ∀ j, g A j ≠ 0 → P.eval (nodes A j) = g A j)
    (last : ∀ j, g A j = 0 → nodes A j = 1 → j = Fin.last 9)
    (on : ∀ x ∈ cleanKnots A, x = 0 ∨ x = 1 ∨ RKResearch.Certified.Graded.LobattoEight.lobattoCubic.eval x = 0)
    {u a : K} (hu : u ∈ cleanKnots A) (an : a ≠ 0)
    (fac : RKResearch.Certified.Graded.LobattoEight.lobattoCubic = (X-C u)*(C a*P)) : False := by
  have hroot := RKResearch.Certified.Graded.LobattoEight.lobatto_isRoot_of_linear fac
  have un : u ≠ 0 := fun h => lobatto_zero_ne ho (h ▸ hroot)
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
  exact lobatto_first_omitted_scalar_paid ho elev hdeg un fac hp

private theorem order8_paid_five_off_impossible
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (elev : (11:K)≠0) (H : ERKEvenHorizon A b 4) (hN : (offKnots A).card = 5) : False := by
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
  exact order8_paid_lobatto_factor_impossible ha ho elev hF dP fit
    (single_profile_on_unique hv hi hc) on
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase huS)) tn fac

private theorem order8_paid_high_off_impossible
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (elev : (11:K)≠0) (H : ERKEvenHorizon A b 4) (hN : 7 ≤ (offKnots A).card) : False := by
  obtain ⟨h3, h4, _⟩ := order8_paid_ranks ha ho H
  obtain ⟨_, hc, hE⟩ := order8_paid_end H
  obtain ⟨P, dP, nz, _, hF, fit⟩ := two_curve_head h3 h4 (by omega)
  let T := cleanKnots A
  let L := nodalHull T
  have dL : L.natDegree = T.card := natDegree_nodalHull _
  have Ln : L ≠ 0 := (monic_nodalHull T).ne_zero
  have t0 : (0 : K) ∈ T := zero_mem_cleanKnots (s:=9) ha
  have count : T.card + (offKnots A).card ≤ 10 := clean_off_count A
  have t3 : T.card = 3 := by
    by_contra! ne
    have d : (P*L).natDegree ≤ 4 := by
      rw [natDegree_mul nz Ln, dL]
      omega
    have z : (P*L).eval 0 = 0 := by rw [eval_mul, nodalHull_eval_of_mem t0, mul_zero]
    have moments (j : Fin 4) : probe A b j.val (evalNodes A (P*L)) = 0 := by
      have pay : j.val + T.card + 3 ≤ 8 := by have := j.isLt; omega
      exact on_hull_times_head_probes ho fit j.val pay
    exact mul_ne_zero nz Ln (order8_paid_anchored_zero ho (P*L) d z moments)
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
  exact order8_paid_lobatto_factor_impossible ha ho elev hF dP fit
    (single_profile_on_unique hv hi hc) on hu (inv_ne_zero an) fac

/-- The actual even horizon and exact tagged census: if four clocks
are defective, the clean tagged support has exactly five clocks. -/
theorem order8_paid_tagged_census (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (elev : (11:K)≠0) : ERKEvenHorizon A b 4 ∧
      ((offKnots A).card = 1 ∨ (offKnots A).card = 4 ∧ (cleanKnots A).card = 5) := by
  have H := order8_paid_even_horizon ha ho
  obtain ⟨r3, r4, cap⟩ := order8_paid_ranks ha ho H
  have sep : PolySeparated A 4 :=
    PolySeparated.of_coeff (explicit_coeff_separated (s:=9) ha ho (q:=4) (by decide))
  have pos := off_pos_paid ha ho sep
  obtain ⟨no2, no3⟩ := not_two_or_three_paid ha ho sep r3 r4
  have no5 : (offKnots A).card ≠ 5 := order8_paid_five_off_impossible ha ho elev H
  have no6 : (offKnots A).card ≠ 6 := by
    intro h6
    obtain ⟨P, _, _, _, _, fit⟩ := two_curve_head r3 r4 (by omega)
    have cancel : ∀ x ∈ offKnots A, offMass A b x = 0 := offMass_zero_of_head ho fit (by omega)
    have lo := order8_paid_clean_floor ha ho cancel
    have count := clean_off_count A
    omega
  have hi : (offKnots A).card < 7 := by
    by_contra! ng
    exact order8_paid_high_off_impossible ha ho elev H ng
  refine ⟨H, ?_⟩
  by_cases one : (offKnots A).card = 1
  · exact Or.inl one
  · have four : (offKnots A).card = 4 := by omega
    obtain ⟨P, _, _, _, _, fit⟩ := two_curve_head r3 r4 (by omega)
    have cancel : ∀ x ∈ offKnots A, offMass A b x = 0 := offMass_zero_of_head ho fit (by omega)
    exact Or.inr ⟨four, order8_paid_five_clean ha ho cap (by omega) cancel⟩

/-- Compact consumer form of the same census, still with the actual
reviewed even horizon and no rank, seed, clock, or weight assumptions. -/
theorem order8_paid_one_or_four_with_horizon (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder 8 A b) (elev : (11:K)≠0) : ERKEvenHorizon A b 4 ∧
      ((offKnots A).card = 1 ∨ (offKnots A).card = 4) := by
  obtain ⟨H, h⟩ := order8_paid_tagged_census ha ho elev
  rcases h with one | ⟨four, _⟩
  · exact ⟨H, Or.inl one⟩
  · exact ⟨H, Or.inr four⟩

end RKResearch.Certified.Graded.ERK8PaidField

#print axioms RKResearch.Certified.Graded.ERK8PaidField.order8_paid_tagged_census
