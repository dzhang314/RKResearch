module

public import RKCert.ReviewedNative.SDIRK118ForwardProjection

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.ReverseChart

open RKResearch
open RKResearch.Certified.Graded (mat)
open RKResearch.Certified.PaidDefectBridge (Letter wordMap)
open RKResearch.Certified.PaidDefectBridge.ForwardChart
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (Chart PolyBound V8)
open scoped Matrix BigOperators

variable {K : Type*} [Field K]

/-- The linear primitive evaluation on the same quadratic coefficient frame. -/
def primAt (x : K) : Quad K →ₗ[K] K where
  toFun := prim x
  map_add' p q := by
    change (p.1+q.1)*x+(p.2.1+q.2.1)*(x^2/2)+(p.2.2+q.2.2)*(x^3/3) =
      (p.1*x+p.2.1*(x^2/2)+p.2.2*(x^3/3)) +
      (q.1*x+q.2.1*(x^2/2)+q.2.2*(x^3/3))
    ring
  map_smul' k q := by
    change (k*q.1)*x+(k*q.2.1)*(x^2/2)+(k*q.2.2)*(x^3/3) =
      k*(q.1*x+q.2.1*(x^2/2)+q.2.2*(x^3/3))
    ring

def shiftAt (x : K) : Quad K →ₗ[K] K := primAt x - ev x

theorem shiftAt_apply (x : K) (q : Quad K) :
    shiftAt x q = prim x q - ev x q := rfl

def seedQuad (s κ : K) : Quad K :=
  (κ*(s^2/3), -(4/3)*κ*s, κ)

theorem eval_seedQuad [CharZero K] (s κ x : K) :
    ev x (seedQuad s κ) = κ*(x-s)*(x-s/3) := by
  simp only [ev_apply,seedQuad]
  ring

/-- The exact fourth-row action on the interpolated old defect, before
using the small reverse root equation. -/
theorem shift_seedQuad [CharZero K] (s κ t : K) :
    shiftAt t (seedQuad s κ) = κ*(t-s)*(t^2-(s+3)*t+s)/3 := by
  simp only [shiftAt_apply,prim,ev_apply,seedQuad]
  ring

/-- Derive the three normalized defect values from the seed cubic. -/
theorem seedQuad_old_values [CharZero K] (s : K)
    (hs1 : 1-s ≠ 0) (hs3 : 3-s ≠ 0)
    (hs : s^3-9*s^2+18*s-6=0) :
    let a := (1+s)/2
    let h := a-1
    let κ := 3/(2*((1-s)*(3-s)))
    ev 1 (seedQuad s κ) = 1/2 ∧
    ev a (seedQuad s κ) = 1/2+h-h^2/2 ∧ ev s (seedQuad s κ)=0 := by
  dsimp
  refine ⟨?_,?_,?_⟩
  · rw [eval_seedQuad]
    field_simp [hs1,hs3] <;> ring
  · calc
      ev ((1+s)/2) (seedQuad s (3/(2*((1-s)*(3-s))))) = (3+s)/(8*(3-s)) := by
        rw [eval_seedQuad]
        field_simp [hs1,hs3] <;> ring
      _ = _ := by
        apply (div_eq_iff (mul_ne_zero (by norm_num) hs3)).2
        linear_combination -hs
  · rw [eval_seedQuad,sub_self,mul_zero,zero_mul]

theorem interp_eq_seedQuad (u g : V K) (s κ : K)
    (h01 : u 0 ≠ u 1) (h02 : u 0 ≠ u 2) (h12 : u 1 ≠ u 2)
    (h0 : ev (u 0) (seedQuad s κ)=g 0)
    (h1 : ev (u 1) (seedQuad s κ)=g 1)
    (h2 : ev (u 2) (seedQuad s κ)=g 2) :
    interp u g = seedQuad s κ := by
  obtain ⟨e0,e1,e2⟩ := interp_old u g h01 h02 h12
  exact quad_eq_of_three h01 h02 h12 (e0.trans h0.symm)
    (e1.trans h1.symm) (e2.trans h2.symm)

/-- Literal normalized row 3: three shifted cardinal taps and the self 1. -/
def lastNormRow (u : V K) (t : K) : V K →ₗ[K] K :=
  (shiftAt t).comp (interp u) + coordinate 3

theorem lastNormRow_literal (u v : V K) (t : K) :
    lastNormRow u t v =
      v 0 * shiftAt t (ell (u 0) (u 1) (u 2)) +
      v 1 * shiftAt t (ell (u 1) (u 0) (u 2)) +
      v 2 * shiftAt t (ell (u 2) (u 0) (u 1)) + v 3 := by
  change shiftAt t (interp u v)+v 3 = _
  simp only [interp_apply,map_add,map_smul,smul_eq_mul]

theorem lastNormRow_sample (u : V K) (t : K) (q : Quad K)
    (h01 : u 0 ≠ u 1) (h02 : u 0 ≠ u 2) (h12 : u 1 ≠ u 2)
    (ht : u 3=t) :
    lastNormRow u t (sample u q)=prim t q := by
  change shiftAt t (interp u (sample u q))+sample u q 3=_
  rw [interp_sample u h01 h02 h12,sample_apply,ht,shiftAt_apply]
  ring

theorem lastNormRow_defect [CharZero K] (u g : V K) (s κ t : K)
    (hp : interp u g = seedQuad s κ) (hg : g 3=0)
    (hq : t^2-(s+3)*t+s=0) :
    lastNormRow u t g=0 := by
  change shiftAt t (interp u g)+g 3=0
  rw [hp,hg,add_zero,shift_seedQuad,hq,mul_zero,zero_div]

theorem normalized_reverse_pivot [CharZero K] (u g : V K) (s κ t : K)
    (hp : interp u g = seedQuad s κ) (hg : g 3=0) (ht : u 3=t)
    (hκ : κ ≠ 0) (hs : t ≠ s) (hr : t ≠ s/3) :
    pivot u g ≠ 0 := by
  rw [pivot,hg,hp,ht,eval_seedQuad,zero_sub]
  intro hz
  exact (mul_ne_zero (mul_ne_zero hκ (sub_ne_zero.mpr hs)) (sub_ne_zero.mpr hr))
    (neg_eq_zero.mp hz)

/-- Four normalized anchor tests at the genuinely local fourth reverse row.
Row 2 uses the already supplied normalized_third_anchor. -/
theorem last_norm_anchor_on_four [CharZero K] (u g : V K) (s κ t : K)
    (h01 : u 0 ≠ u 1) (h02 : u 0 ≠ u 2) (h12 : u 1 ≠ u 2)
    (ht : u 3=t) (hp : interp u g=seedQuad s κ) (hg : g 3=0)
    (hq : t^2-(s+3)*t+s=0) :
    lastNormRow u t 1=t ∧ lastNormRow u t u=t^2/2 ∧
    lastNormRow u t (u^2)=t^3/3 ∧ lastNormRow u t g=0 := by
  have z0 : sample u ((1,0,0) : Quad K) = 1 := by
    funext i
    simp [sample_apply,ev_apply]
  have z1 : sample u ((0,1,0) : Quad K) = u := by
    funext i
    simp [sample_apply,ev_apply]
  have z2 : sample u ((0,0,1) : Quad K) = u^2 := by
    funext i
    simp [sample_apply,ev_apply,Pi.pow_apply]
  refine ⟨?_,?_,?_,lastNormRow_defect u g s κ t hp hg hq⟩
  · rw [←z0,lastNormRow_sample u t _ h01 h02 h12 ht]
    simp [prim]
  · rw [congrArg (lastNormRow u t) z1.symm, lastNormRow_sample u t _ h01 h02 h12 ht]
    simp [prim]
  · rw [←z2,lastNormRow_sample u t _ h01 h02 h12 ht]
    simp [prim]

/-- A true local-three row in physical clocks. -/
structure LocalThree (R : Matrix (Fin 4) (Fin 4) K) (c g : V K) (k : Fin 4) : Prop where
  defectZero : g k=0
  row0 : (mat R (1 : V K)) k=c k
  row1 : (mat R c) k=(c k)^2/2
  row2 : (mat R (c^2)) k=(c k)^3/3
  rowDefect : (mat R g) k=0

/-- Both evaluation and the primitive row agree on all old vectors. -/
theorem anchor_on_frame (R : Matrix (Fin 4) (Fin 4) K) (c g v : V K) (k : Fin 4)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (h : LocalThree R c g k) :
    ev (c k) (project c g v)=v k ∧ (mat R v) k=prim (c k) (project c g v) := by
  have eval : ev (c k) (project c g v) = v k := by
    symm
    simpa only [h.defectZero,mul_zero,add_zero] using reconstruct c g v h01 h02 h12 hp k
  refine ⟨eval,?_⟩
  let q := project c g v
  let a := defectCoef c g v
  have hv : v = q.1 • (1 : V K)+q.2.1 • c+q.2.2 • (c^2)+a • g := by
    funext i
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,Pi.pow_apply,
      smul_eq_mul,mul_one,ev_apply,q,a] using reconstruct c g v h01 h02 h12 hp i
  calc
    (mat R v) k = (mat R (q.1 • (1 : V K)+q.2.1 • c+q.2.2 • (c^2)+a • g)) k :=
      congrArg (fun w : V K => (mat R w) k) hv
    _ = _ := by
      simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        h.row0,h.row1,h.row2,h.rowDefect,mul_zero,add_zero,prim,q]

/-- Genuine one-step polynomial observations at an anchor, for arbitrary
old v. These are not assertions about only the four short words. -/
structure AnchorSteps (R : Matrix (Fin 4) (Fin 4) K) (ζ : V K)
    (proj : V K →ₗ[K] Polynomial K) (E : Polynomial K →ₗ[K] K)
    (I : Polynomial K →ₗ[K] Polynomial K) : Prop where
  transport : ∀ v, E (proj (mat R v))=E (I (proj v))
  clock : ∀ v, E (proj (ζ*v))=E ((1-Polynomial.X)*(proj v))

theorem anchor_at_polynomials (R : Matrix (Fin 4) (Fin 4) K) (c g : V K)
    (k : Fin 4) (γ : K) (E Iₚ : Polynomial K →ₗ[K] K)
    (I : Polynomial K →ₗ[K] Polynomial K)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2)
    (hp : pivot c g ≠ 0) (h : LocalThree R c g k)
    (he0 : E 1=1) (he1 : E Polynomial.X=c k)
    (he2 : E (Polynomial.X^2)=(c k)^2)
    (hi0 : Iₚ 1=c k) (hi1 : Iₚ Polynomial.X=(c k)^2/2)
    (hi2 : Iₚ (Polynomial.X^2)=(c k)^3/3)
    (hI : ∀ Q, Iₚ Q=E (I Q))
    (hClock : ∀ Q, E ((1-Polynomial.X)*Q)=(1-c k)*E Q) :
    AnchorSteps R (1-c) (polyProject c g) E I ∧
    (∀ v, E (polyProject c g v)=v k) ∧
    (∀ v, (mat R v) k-γ*v k=Iₚ (polyProject c g v)-γ*E (polyProject c g v)) := by
  have inv (v : V K) : E (polyProject c g v)=v k :=
    (evaluate_toPoly E (c k) he0 he1 he2 (project c g v)).trans
      (anchor_on_frame R c g v k h01 h02 h12 hp h).1
  have act (v : V K) : (mat R v) k=Iₚ (polyProject c g v) :=
    (anchor_on_frame R c g v k h01 h02 h12 hp h).2.trans
      (primitive_evaluate_toPoly Iₚ (c k) hi0 hi1 hi2 (project c g v)).symm
  refine ⟨⟨?_,?_⟩,inv,?_⟩
  · intro v
    rw [inv,act,hI]
  · intro v
    rw [inv,hClock,inv] <;> rfl
  · intro v
    rw [inv,act]

/-- All four length-two tails on the literal old reverse block, with
the head of the word on the outside. -/
theorem two_tail_table (R : Matrix (Fin 4) (Fin 4) K) (c g : V K)
    (h0 : mat R (1 : V K)=c) (h1 : mat R c=(2 : K)⁻¹ • (c^2)+g) :
    wordMap R (1-c) [.transport,.transport] 1=(2 : K)⁻¹ • (c^2)+g ∧
    wordMap R (1-c) [.transport,.clock] 1=c-(2 : K)⁻¹ • (c^2)-g ∧
    wordMap R (1-c) [.clock,.transport] 1=c-c^2 ∧
    wordMap R (1-c) [.clock,.clock] 1=1-(c+c)+c^2 := by
  refine ⟨?_,?_,?_,?_⟩
  · change mat R (mat R (1 : V K))=_
    rw [h0,h1]
  · change mat R ((1-c)*(1 : V K))=_
    rw [mul_one,map_sub,h0,h1]
    abel
  · change (1-c)*mat R (1 : V K)=_
    rw [h0,sub_mul,one_mul,pow_two]
  · change (1-c)*((1-c)*(1 : V K))=_
    rw [mul_one]
    funext i
    simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.one_apply,Pi.pow_apply]
    ring

theorem old_profile_eq_through_two (d : Chart K) (R : Matrix (Fin 4) (Fin 4) K)
    (c g : V K) (proj : V K →ₗ[K] Polynomial K)
    (h0 : mat R (1 : V K)=c) (h1 : mat R c=(2 : K)⁻¹ • (c^2)+g)
    (p0 : proj 1=1) (p1 : proj c=Polynomial.X)
    (p2 : proj (c^2)=Polynomial.X^2) (pg : proj g=0)
    (i0 : d.I 1=Polynomial.X) (i1 : d.I Polynomial.X=(2 : K)⁻¹ • (Polynomial.X^2)) :
    ∀ W : List Letter, W.length ≤ 2 → d.profile W=proj (wordMap R (1-c) W 1) := by
  obtain ⟨tt,tx,xt,xx⟩ := two_tail_table R c g h0 h1
  apply word_gate_le_two
  · change (1 : Polynomial K)=proj 1
    exact p0.symm
  · intro a
    cases a
    · change d.I 1=proj (mat R (1 : V K))
      rw [i0,h0,p1]
    · change (1-Polynomial.X)*1=proj ((1-c)*(1 : V K))
      simp only [mul_one,map_sub,p0,p1]
  · intro a b
    cases a <;> cases b
    · change d.I (d.I 1)=proj (wordMap R (1-c) [.transport,.transport] 1)
      simp only [i0,i1,tt,map_add,map_smul,p2,pg,add_zero]
    · change d.I ((1-Polynomial.X)*1)=proj (wordMap R (1-c) [.transport,.clock] 1)
      simp only [mul_one,tx,map_sub,map_smul,i0,i1,p1,p2,pg,sub_zero]
    · change (1-Polynomial.X)*d.I 1=proj (wordMap R (1-c) [.clock,.transport] 1)
      simp only [i0,xt,map_sub,p1,p2] <;> ring
    · change (1-Polynomial.X)*((1-Polynomial.X)*1)=proj (wordMap R (1-c) [.clock,.clock] 1)
      simp only [mul_one,xx,map_sub,map_add,p0,p1,p2] <;> ring

/-- Bind the checked chart's actual old projection to the old donor word.
For the literal chart, r enumerates physical old slots 7,6,5,4. -/
theorem reverse_defect_restrict (d : Chart K) (ξ : V8 K)
    (R : Matrix (Fin 4) (Fin 4) K) (c : V K)
    (proj : V K →ₗ[K] Polynomial K) (r : Fin 4 → Fin 8)
    (hact : ∀ v : V8 K, (d.L *ᵥ v) ∘ r = R *ᵥ (v ∘ r))
    (hclock : ξ ∘ r=1-c)
    (hProj : ∀ v : V8 K, d.projectOld v=proj (v ∘ r))
    (W : List Letter) :
    d.revDefect ξ W = d.profile W - proj (wordMap R (1-c) W 1) := by
  change d.profile W-d.projectOld (wordMap d.L ξ W 1) = _
  rw [hProj, wordMap_comp_of_mulVec_clock d.L R r ξ (1-c) hact hclock W 1] <;> rfl

theorem reverse_short_of_restrict (d : Chart K) (ξ : V8 K)
    (R : Matrix (Fin 4) (Fin 4) K) (c : V K) (proj : V K →ₗ[K] Polynomial K)
    (hOld : ∀ W : List Letter, d.revDefect ξ W=d.profile W-proj (wordMap R (1-c) W 1))
    (hShort : ∀ W : List Letter, W.length≤2 → d.profile W=proj (wordMap R (1-c) W 1)) :
    ∀ W : List Letter, W.length≤2 → d.revDefect ξ W=0 := by
  intro W hW
  rw [hOld W,hShort W hW,sub_self]

/-- A length-two exact tail plus either one-step anchor law suffices for the
actual length-three reverse defect. No eight-word replay is required. -/
theorem reverse_defect_at_anchor
    (d : Chart K) (ξ : V8 K)
    (R : Matrix (Fin 4) (Fin 4) K) (c : V K) (proj : V K →ₗ[K] Polynomial K)
    (E : Polynomial K →ₗ[K] K)
    (hOld : ∀ W : List Letter, d.revDefect ξ W=d.profile W-proj (wordMap R (1-c) W 1))
    (hShort : ∀ W : List Letter, W.length≤2 → d.profile W=proj (wordMap R (1-c) W 1))
    (hStep : AnchorSteps R (1-c) proj E d.I) :
    ∀ W : List Letter, W.length=3 → E (d.revDefect ξ W)=0 := by
  apply word_gate_three
  intro a U hU
  have e := hShort U hU.le
  rw [hOld,map_sub,sub_eq_zero]
  cases a
  · change E (d.I (d.profile U)) = E (proj (mat R (wordMap R (1-c) U 1)))
    rw [hStep.transport,e]
  · change E ((1-Polynomial.X)*d.profile U) = E (proj ((1-c)*(wordMap R (1-c) U 1)))
    rw [hStep.clock,e]

theorem reverse_defect_cubic (d : Chart K) (ξ : V8 K)
    (R : Matrix (Fin 4) (Fin 4) K) (c : V K) (proj : V K →ₗ[K] Polynomial K)
    (hOld : ∀ W : List Letter, d.revDefect ξ W=d.profile W-proj (wordMap R (1-c) W 1))
    (hP : ∀ W : List Letter, PolyBound W.length (d.profile W))
    (hProj : ∀ v, PolyBound 2 (proj v))
    (W : List Letter) (hW : W.length=3) :
    PolyBound 3 (d.revDefect ξ W) := by
  intro j hj
  have hb := hP W
  rw [hW] at hb
  rw [hOld W,Polynomial.coeff_sub,hb j hj,
    hProj (wordMap R (1-c) W 1) j (by omega),sub_self]

/-- Deliver exactly the reverse field of the checked TopBases structure
after the independent, four-root cardinal reconstruction of a cubic. -/
theorem reverse_top_of_anchors (d : Chart K) (ξ : V8 K)
    (R : Matrix (Fin 4) (Fin 4) K) (c : V K) (proj : V K →ₗ[K] Polynomial K)
    (E2 E3 : Polynomial K →ₗ[K] K) (K0 K4 : Polynomial K)
    (hOld : ∀ W : List Letter, d.revDefect ξ W=d.profile W-proj (wordMap R (1-c) W 1))
    (hShort : ∀ W : List Letter, W.length≤2 → d.profile W=proj (wordMap R (1-c) W 1))
    (hStep2 : AnchorSteps R (1-c) proj E2 d.I) (hStep3 : AnchorSteps R (1-c) proj E3 d.I)
    (hDegree : ∀ W : List Letter, PolyBound W.length (d.profile W))
    (hProj : ∀ v, PolyBound 2 (proj v))
    (hCard : ∀ J : Polynomial K, PolyBound 3 J → E2 J=0 → E3 J=0 →
      J=d.Ey J 0 • K0+d.Ey J 4 • K4) :
    ∀ W : List Letter, W.length=3 →
      d.revDefect ξ W=d.Ey (d.revDefect ξ W) 0 • K0+d.Ey (d.revDefect ξ W) 4 • K4 := by
  intro W hW
  exact hCard _ (reverse_defect_cubic d ξ R c proj hOld hDegree hProj W hW)
    (reverse_defect_at_anchor d ξ R c proj E2 hOld hShort hStep2 W hW)
    (reverse_defect_at_anchor d ξ R c proj E3 hOld hShort hStep3 W hW)

/-- Exact physical scaling of the literal old block, without any order or
rank premise. -/
theorem scale_matrix_action (R : Matrix (Fin 4) (Fin 4) K)
    (v : V K) (a b : K) : mat (a • R) (b • v) = (a*b) • (mat R v) := by
  funext i
  change (∑ j : Fin 4, (a*R i j)*(b*v j)) = (a*b)*(∑ j : Fin 4, R i j*v j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rescale_local_three (R : Matrix (Fin 4) (Fin 4) K)
    (u g : V K) (γ : K) (k : Fin 4) (h : LocalThree R u g k) :
    LocalThree (γ • R) (γ • u) ((γ^2) • g) k := by
  have sq : ((γ • u)^2 : V K)=(γ^2) • (u^2) := by
    funext i
    simp only [Pi.pow_apply,Pi.smul_apply,smul_eq_mul,mul_pow]
  have oneAct : mat (γ • R) (1 : V K)=γ • mat R 1 := by
    simpa only [one_smul,mul_one] using scale_matrix_action R (1 : V K) γ 1
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [Pi.smul_apply,smul_eq_mul,h.defectZero,mul_zero]
  · rw [oneAct]
    simp only [Pi.smul_apply,smul_eq_mul,h.row0]
  · rw [scale_matrix_action R u γ γ]
    simp only [Pi.smul_apply,smul_eq_mul,h.row1]
    ring
  · rw [sq,scale_matrix_action R (u^2) γ (γ^2)]
    simp only [Pi.smul_apply,smul_eq_mul,h.row2]
    ring
  · rw [scale_matrix_action R g γ (γ^2)]
    simp only [Pi.smul_apply,smul_eq_mul,h.rowDefect,mul_zero]

theorem rescale_global_moments (R : Matrix (Fin 4) (Fin 4) K)
    (u g : V K) (γ : K)
    (h0 : mat R (1 : V K)=u) (h1 : mat R u=(2 : K)⁻¹ • (u^2)+g) :
    mat (γ • R) (1 : V K)=γ • u ∧
    mat (γ • R) (γ • u)=(2 : K)⁻¹ • ((γ • u)^2)+(γ^2) • g := by
  constructor
  · simpa only [one_smul,mul_one,h0] using scale_matrix_action R (1 : V K) γ 1
  · rw [scale_matrix_action R u γ γ,h1]
    funext i
    simp only [Pi.smul_apply,Pi.add_apply,Pi.pow_apply,smul_eq_mul]
    ring

end RKResearch.Certified.PaidDefectBridge.ReverseChart
