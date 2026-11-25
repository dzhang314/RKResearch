module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstPencil
public import RKCert.ReviewedNative.OrderedPolynomialStripFactors
public import RKCert.ReviewedNative.FiniteGaussianScalarLift
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Reduce the literal reviewed weak-four port to uniform sign boxes

Only the rational reference receipts and the uniform covering receipts remain
as hypotheses. The latter express signs of actual pencil values at rational
strip endpoints and rejection of a product of normalized affine factors on a
box. In the exterior cells the exact coefficient identity (Vieta) is carried
into that leaf. No result about a fixed physical fibre or additional local or
global moment is invoked.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.CrossedGaussianScalarLift (integral_map)
open RKCert.ReviewedNative.FiniteRootSeparator (eval_on_base)
open RKCert.ReviewedNative.OrderedRootGapSaturation (OrderedExtension)
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open scoped BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def stoppedFactors {ι : Type*} (r : ι → K) (I : Finset ι) (a : K) : K[X] :=
  ∏ i ∈ I, (C a*X-C (r i))

def UnitPair (D : K[X]) : Prop :=
  integral 0 1 (X*D)=0 ∧ integral 0 1 (X^2*D)=0

/-- All hypotheses on a scalar leaf, apart from strip construction. The
selected indices are exhaustive, with no assumption about two roots being
earlier than the stop. When intervals reach zero, distinct strips give
strictly positive denominators for the rescaling by the sum of the clocks. -/
def InteriorRejects {n : ℕ} (m : ℕ) (lo hi : Fin n → K) : Prop :=
  ∀ (E : OrderedExtension K) (r : Fin n → E.carrier),
    (∀ i, E.embed (lo i) ≤ r i ∧ r i ≤ E.embed (hi i)) →
    ∀ (I : Finset (Fin n)), I.card=m → ∀ j, j ∉ I → 0<r j →
      ¬ UnitPair (stoppedFactors r I (r j))

/-- The exterior analogue. The arbitrary scalar at the extra index is
constrained only by its direction and the actual degree-seven coefficient
identity; the rational leaf will bound the projectivized ratio, not the
possibly unbounded exterior clock. An exterior fitting root and a high
exterior first stop are both included. -/
def ExteriorRejects (high : Bool) (P : K[X]) (lo hi : Fin 7 → K) : Prop :=
  ∀ (E : OrderedExtension K) (r : Fin 7 → E.carrier) (e : E.carrier),
    (∀ i, E.embed (lo i) ≤ r i ∧ r i ≤ E.embed (hi i)) →
    (if high then 1≤e else e≤0) →
    (P.map E.embed).coeff 7 = -(P.map E.embed).coeff 8*(e+∑ i : Fin 7,r i) →
    ∀ (I : Finset (Option (Fin 7))), I.card=4 → ∀ j, j ∉ I →
      0<withExtra r e j → ¬ UnitPair (stoppedFactors (withExtra r e) I (withExtra r e j))

/-- These are pointwise formulations of *uniform interval-cover* receipts.
A closed parameter tile with both signed endpoint checks obtains the
`SignStrips` field for every parameter in the tile by `PencilCell.at_param`.
The `*Rejects` fields must exclude every factor tuple in the same strips. -/
def InteriorCover (P T : K[X]) (n m : ℕ) : Prop :=
  ∀ v : K, 0≤v → v≤1 → ∃ lo hi : Fin n → K,
    SignStrips (pencil P T v) lo hi ∧
    (∀ i, 0≤lo i ∧ hi i≤1) ∧ InteriorRejects m lo hi

def ExteriorCover (P T : K[X]) (high : Bool) : Prop :=
  ∀ v : K, 0≤v → v≤1 → ∃ lo hi : Fin 7 → K,
    SignStrips (pencil P T v) lo hi ∧
    (∀ i, 0<lo i ∧ hi i<1) ∧ ExteriorRejects high (pencil P T v) lo hi

structure FirstBoxCover (J P₀ P₁ : K[X]) : Prop where
  cubic : InteriorCover J J 7 3
  unit : InteriorCover P₀ P₁ 8 4
  low : ExteriorCover J P₀ false
  high : ExteriorCover J (-P₁) true

private theorem integral_C_mul (l r c : K) (F : K[X]) :
    integral l r (C c*F) = c*integral l r F := by
  simpa only [Polynomial.smul_eq_C_mul,smul_eq_mul] using (integral l r).map_smul c F

private theorem affine_test_to_unit {a b : K} {Q D : K[X]} (k : ℕ)
    (ha : a≠0) (hb : b≠0) (form : Q.comp (C a*X) = C b*D)
    (paid : integral 0 a (X^k*Q)=0) :
    integral 0 1 (X^k*D)=0 := by
  have e := integral_affine (0:K) a (X^k*Q)
  simp only [sub_zero,map_zero,add_zero] at e
  have cf : (X^k*Q).comp (C a*X) = C (a^k*b)*(X^k*D) := by
    rw [mul_comp,pow_comp,X_comp,form,mul_pow,C_mul,C_pow]
    ring
  rw [paid,cf,integral_C_mul,←mul_assoc] at e
  exact (mul_eq_zero.mp e.symm).resolve_left
    (mul_ne_zero ha (mul_ne_zero (pow_ne_zero _ ha) hb))

private theorem unitPair_of_factor {ι : Type*} {r : ι → K} {I : Finset ι}
    {Q : K[X]} {a : K} (qa : a≠0) (qn : Q≠0)
    (form : Q = C Q.leadingCoeff*indexedHull r I)
    (h₁ : integral 0 a (X*Q)=0) (h₂ : integral 0 a (X^2*Q)=0) :
    UnitPair (stoppedFactors r I a) := by
  have c : Q.comp (C a*X) = C Q.leadingCoeff*stoppedFactors r I a := by
    calc
      Q.comp (C a*X) = (C Q.leadingCoeff*indexedHull r I).comp (C a*X) :=
        congrArg (fun f : K[X] => f.comp (C a*X)) form
      _ = _ := by simp only [C_mul_comp,indexedHull,stoppedFactors,prod_comp,sub_comp,X_comp,C_comp]
  have z := leadingCoeff_ne_zero.mpr qn
  refine ⟨?_, affine_test_to_unit 2 qa z c h₂⟩
  simpa only [pow_one] using
    (affine_test_to_unit 1 qa z c (by simpa only [pow_one] using h₁))

private theorem FirstStopPacket.mapped_stopped {Q Z : K[X]} {a : K}
    (H : FirstStopPacket Q Z a) (E : OrderedExtension K) :
    integral 0 (E.embed a) (X*(Q.map E.embed))=0 ∧
    integral 0 (E.embed a) (X^2*(Q.map E.embed))=0 := by
  constructor
  · have p := congrArg E.embed H.first
    rw [←integral_map E.embed 0 a (X*Q)] at p
    simpa only [map_zero,Polynomial.map_mul,map_X] using p
  · have p := congrArg E.embed H.second
    rw [←integral_map E.embed 0 a (X^2*Q)] at p
    simpa only [map_zero,Polynomial.map_mul,Polynomial.map_pow,map_X] using p

private theorem indexed_pair_from_layout {ι : Type*} [Fintype ι] {Q Z P : K[X]}
    {a c : K} (H : FirstStopPacket Q Z a) (scale : Q*Z=C c*P)
    (E : OrderedExtension K) (r : ι → E.carrier) (inj : Function.Injective r)
    (layout : P.map E.embed =
      C (P.map E.embed).leadingCoeff*indexedHull r Finset.univ) :
    ∃ (I : Finset ι) (j : ι), I.card=Q.natDegree ∧ j∉I ∧
      r j≠0 ∧ UnitPair (stoppedFactors r I (r j)) := by
  classical
  let U := Q.map E.embed
  let V := Z.map E.embed
  let S := P.map E.embed
  have eq : U*V=C (E.embed c)*S := by
    have p := congrArg (fun f : K[X] => f.map E.embed) scale
    simpa only [U,V,S,Polynomial.map_mul,map_C] using p
  have un : U≠0 := (Polynomial.map_ne_zero_iff E.embed.injective).2 H.fitNonzero
  have vn : V≠0 := (Polynomial.map_ne_zero_iff E.embed.injective).2 H.hullMonic.ne_zero
  have aV : V.IsRoot (E.embed a) := by
    change (Z.map E.embed).eval (E.embed a)=0
    rw [eval_on_base,show Z.eval a=0 from H.stopRoot,map_zero]
  obtain ⟨I,_,card,form,marks⟩ := factors_of_saturated_roots r Finset.univ inj un vn
    (scale_layout r Finset.univ (U*V) S (E.embed c) eq layout)
  obtain ⟨j,_,rj,notI⟩ := marks _ aV
  have an : E.embed a≠0 := by
    intro z
    apply H.stopNonzero
    apply E.embed.injective
    simpa only [map_zero] using z
  have stop := H.mapped_stopped E
  have pd : I.card=Q.natDegree := by rw [card,natDegree_map_eq_of_injective E.embed.injective]
  refine ⟨I,j,pd,notI,by simpa only [rj] using an,?_⟩
  rw [rj]
  exact unitPair_of_factor an un form stop.1 stop.2

private theorem pencil_degree_from_scale {Q Z P : K[X]} {a c : K} {n : ℕ}
    (H : FirstStopPacket Q Z a) (q : Q.natDegree=n) (cn : c≠0)
    (scale : Q*Z=C c*P) :
    P.natDegree=n+4 := by
  have d := congrArg Polynomial.natDegree scale
  rw [natDegree_mul H.fitNonzero H.hullMonic.ne_zero,q,H.hullDegree,natDegree_C_mul cn] at d
  exact d.symm

private theorem no_interior_box {Q Z P T : K[X]} {a c v : K} {n : ℕ}
    (H : FirstStopPacket Q Z a) (q : Q.natDegree=n) (cn : c≠0)
    (scale : Q*Z=C c*pencil P T v) (v0 : 0≤v) (v1 : v≤1)
    (cover : InteriorCover P T (n+4) n) : False := by
  obtain ⟨lo,hi,strips,positive,reject⟩ := cover v v0 v1
  obtain ⟨E,r,mono,window,roots⟩ := strips.exists_roots
  let p := (pencil P T v).map E.embed
  have d : p.natDegree=n+4 := by
    rw [natDegree_map_eq_of_injective E.embed.injective]
    exact pencil_degree_from_scale H q cn scale
  have form : p = C p.leadingCoeff*indexedHull r Finset.univ := by
    apply factor_eq_of_indexed_roots r Finset.univ mono.injective (fun i _ => roots i)
    change p.natDegree ≤ (Finset.univ : Finset (Fin (n+4))).card
    rw [d, Finset.card_univ, Fintype.card_fin]
  obtain ⟨I,j,ic,ji,jn,stopped⟩ := indexed_pair_from_layout H scale E r mono.injective form
  have jp : 0<r j := lt_of_le_of_ne
    ((show 0≤E.embed (lo j) by simpa only [map_zero] using E.mono.monotone (positive j).1).trans
      (window j).1) jn.symm
  exact reject E r window I (ic.trans q) j ji jp stopped

private theorem negative_stop_not_paid {r : Option (Fin 7) → K}
    {I : Finset (Option (Fin 7))} {a : K} (card : I.card=4) (a0 : a<0)
    (positive : ∀ i ∈ I, 0<r i) :
    ¬ UnitPair (stoppedFactors r I a) := by
  intro paid
  let D := X*stoppedFactors r I a
  have dF : (stoppedFactors r I a).natDegree ≤ I.card := by
    unfold stoppedFactors
    refine (natDegree_prod_le I (fun i => C a * X - C (r i))).trans ?_
    calc
      (∑ i ∈ I,(C a*X-C (r i)).natDegree) ≤ ∑ _i ∈ I,1 :=
        Finset.sum_le_sum (f := fun i : Option (Fin 7) => (C a * X - C (r i)).natDegree) fun i _ => by
          simpa only [sub_eq_add_neg,map_neg] using
          (natDegree_linear_le (a := a) (b := -(r i)))
      _ = I.card := by simp
  have d : D.natDegree ≤ 19 := by
    change (X*stoppedFactors r I a).natDegree≤19
    have b := natDegree_mul_le_of_le (m := 1) (by simp : (X:K[X]).natDegree≤1) dF
    rw [card] at b
    exact b.trans (by decide)
  have h := paid.1
  change integral 0 1 D = 0 at h
  rw [interval_exact 0 1 D d] at h
  have hpos (i : Fin 19) : 0 < D.eval (intervalPoint (0:K) 1 i) := by
    let x := intervalPoint (0:K) 1 i
    have xp := (intervalPoint_mem zero_lt_one i : x ∈ Set.Ioo (0:K) 1).1
    have factors : (∏ j ∈ I,(a*x-r j)) = ∏ j ∈ I,(r j-a*x) := by
      simp only [show ∀ j, a*x-r j = -(r j-a*x) from fun j => by ring,Finset.prod_neg,card]
      norm_num
    have prod : 0 < ∏ j ∈ I,(r j-a*x) := Finset.prod_pos fun j hj =>
      sub_pos.mpr ((mul_neg_of_neg_of_pos a0 xp).trans (positive j hj))
    simp only [D,stoppedFactors,eval_mul,eval_X,eval_prod,eval_sub,eval_C]
    change 0 < x*(∏ j ∈ I,(a*x-r j))
    rw [factors]
    exact mul_pos xp prod
  have z : 0 < ∑ i : Fin 19,intervalWeight (0:K) 1 i*D.eval (intervalPoint 0 1 i) := by
    apply Finset.sum_pos'
    · intro i _
      exact (mul_pos (intervalWeight_pos zero_lt_one i) (hpos i)).le
    · exact ⟨0,Finset.mem_univ _,mul_pos (intervalWeight_pos zero_lt_one 0) (hpos 0)⟩
  exact (ne_of_gt z) h

private theorem no_exterior_box {Q Z P T : K[X]} {a c v : K} {high : Bool}
    (H : FirstStopPacket Q Z a) (q : Q.natDegree=4) (cn : c≠0)
    (scale : Q*Z=C c*pencil P T v) (v0 : 0≤v) (v1 : v≤1)
    (cover : ExteriorCover P T high)
    (side : if high then
      (pencil P T v).coeff 8<0 ∧ 0≤(pencil P T v).eval 1
      else 0<(pencil P T v).coeff 8 ∧ (pencil P T v).eval 0≤0) : False := by
  obtain ⟨lo,hi,strips,positive,reject⟩ := cover v v0 v1
  obtain ⟨E,r,mono,window,roots⟩ := strips.exists_roots
  let p := (pencil P T v).map E.embed
  have d : p.natDegree=8 := by
    rw [natDegree_map_eq_of_injective E.embed.injective]
    exact pencil_degree_from_scale H q cn scale
  obtain ⟨e,factor⟩ := exists_one_extra_root (n := 7) d mono.injective roots
  have rp (i : Fin 7) : 0<r i :=
    lt_of_lt_of_le (by simpa only [map_zero] using E.mono (positive i).1) (window i).1
  have rt (i : Fin 7) : r i<1 :=
    lt_of_le_of_lt (window i).2 (by simpa only [map_one] using E.mono (positive i).2)
  have cl : p.leadingCoeff=E.embed ((pencil P T v).coeff 8) := by
    calc
      p.leadingCoeff = p.coeff 8 := by rw [←d,coeff_natDegree]
      _ = E.embed ((pencil P T v).coeff 8) := coeff_map E.embed 8
  have at₀ : p.eval 0 = E.embed ((pencil P T v).eval 0) := by
    simpa only [p,map_zero] using eval_on_base E.embed (pencil P T v) 0
  have at₁ : p.eval 1 = E.embed ((pencil P T v).eval 1) := by
    simpa only [p,map_one] using eval_on_base E.embed (pencil P T v) 1
  have outer : if high then 1≤e else e≤0 := by
    cases high
    · apply extra_le_zero_of_eval_zero factor rp
      · rw [cl]
        simpa only [map_zero] using E.mono side.1
      · rw [at₀]
        simpa only [map_zero] using E.mono.monotone side.2
    · apply one_le_extra_of_eval_one factor rt
      · rw [cl]
        simpa only [map_zero] using E.mono side.1
      · rw [at₁]
        simpa only [map_zero] using E.mono.monotone side.2
  have ne (i : Fin 7) : e≠r i := by
    cases high
    · exact ne_of_lt (lt_of_le_of_lt outer (rp i))
    · exact ne_of_gt (lt_of_lt_of_le (rt i) outer)
  have form : p = C p.leadingCoeff*indexedHull (withExtra r e) Finset.univ := by
    rw [indexedHull_withExtra]
    exact factor
  obtain ⟨I,j,ic,ji,jn,stopped⟩ := indexed_pair_from_layout H scale E
    (withExtra r e) (withExtra_injective mono.injective ne) form
  have count := ic.trans q
  have vi := vieta_one_extra d factor
  by_cases h : 0<withExtra r e j
  · exact reject E r e window outer vi I count j ji h stopped
  · have jNone : j=none := by
      cases j with
      | none => rfl
      | some i => exact (h (rp i)).elim
    subst j
    apply negative_stop_not_paid (r := withExtra r e) count (lt_of_le_of_ne (le_of_not_gt h) jn)
    · intro i hi'
      cases i with
      | none => exact (ji hi').elim
      | some i => exact rp i
    · exact stopped

private theorem C_mul_pencil (k : K) (P T : K[X]) (v : K) :
    C k*pencil P T v = C (k*(1-v))*P + C (k*v)*T := by
  simp only [pencil,mul_add,←mul_assoc,←C_mul]

/-- Structural ordered-field weak-four obstruction. All remaining premises
are the reusable finite polynomial references and continuous-box arithmetic.
The deductions do not rely on the input hull already splitting. -/
theorem no_firstStopPacket_of_boxes {Q Z J P₀ P₁ : K[X]} {a : K}
    (R : FirstPencilReferences J P₀ P₁) (B : FirstBoxCover J P₀ P₁)
    (H : FirstStopPacket Q Z a) : False := by
  have J8 : J.coeff 8=0 := coeff_eq_zero_of_natDegree_lt (by rw [R.jDegree]; decide)
  have P08 : P₀.coeff 8=P₀.leadingCoeff := by rw [←R.pDegree,coeff_natDegree]
  have P18 : P₁.coeff 8=P₀.leadingCoeff := by rw [R.identity,coeff_sub,J8,sub_zero,P08]
  have P11 : P₁.eval 1=0 := by rw [R.identity,eval_sub,R.pAtOne,sub_self]
  rcases H.represent R with ⟨q,c,cn,scale⟩ | ⟨q,c,b,cn,scale⟩
  · have e : pencil J J 0=J := by simp [pencil]
    rw [← e] at scale
    exact no_interior_box H q cn scale le_rfl zero_le_one B.cubic
  by_cases bl : 0≤b
  · let k := 1+b
    have kp : 0<k := add_pos_of_pos_of_nonneg zero_lt_one bl
    let v := 1/k
    have vp : 0<v := one_div_pos.mpr kp
    have v1 : v≤1 := by
      apply (div_le_iff₀ kp).2
      dsimp only [k]
      linarith only [bl]
    have kv : k*v=1 := by
      dsimp only [v]
      rw [div_eq_mul_inv,one_mul,mul_inv_cancel₀ kp.ne']
    have kb : k*(1-v)=b := by
      rw [mul_sub,mul_one,kv]
      simp [k]
    have pEq : C k*pencil J P₀ v=P₀+C b*J := by
      rw [C_mul_pencil,kb,kv,C_1,one_mul,add_comm]
    rw [← pEq,←mul_assoc,←C_mul] at scale
    apply no_exterior_box H q (mul_ne_zero cn kp.ne') scale vp.le v1 B.low
    constructor
    · rw [pencil_coeff,J8,mul_zero,zero_add,P08]
      exact mul_pos vp R.lead
    · rw [pencil_eval,R.pAtZero,mul_zero,add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr v1) R.jAtZero.le
  by_cases bh : b≤-1
  · let v := (-1)/b
    have bn : b<0 := bh.trans_lt (by norm_num)
    have vp : 0<v := div_pos_of_neg_of_neg (by norm_num) bn
    have v1 : v≤1 := (div_le_iff_of_neg bn).2 (by simpa only [one_mul] using bh)
    have bv : b*v= -1 := by
      rw [show b*v = v*b from mul_comm _ _,show v=(-1)/b from rfl,
        div_mul_cancel₀ _ bn.ne]
    have bb : b*(1-v)=b+1 := by rw [mul_sub,mul_one,bv,sub_neg_eq_add]
    have pEq : C b*pencil J (-P₁) v=P₀+C b*J := by
      rw [C_mul_pencil,bb,bv,R.identity,C_neg,C_add,C_1]
      ring
    rw [←pEq,←mul_assoc,←C_mul] at scale
    apply no_exterior_box H q (mul_ne_zero cn bn.ne) scale vp.le v1 B.high
    constructor
    · rw [pencil_coeff,J8,mul_zero,zero_add,coeff_neg,P18]
      exact mul_neg_of_pos_of_neg vp (neg_neg_of_pos R.lead)
    · rw [pencil_eval,eval_neg,P11,neg_zero,mul_zero,add_zero]
      exact mul_nonneg (sub_nonneg.mpr v1) R.jAtOne.le
  · let v := -b
    have v0 : 0≤v := neg_nonneg.mpr (le_of_not_ge bl)
    have v1 : v≤1 := by dsimp only [v]; linarith only [lt_of_not_ge bh]
    have pEq : pencil P₀ P₁ v = P₀+C b*J := by
      simp only [v,pencil,R.identity,C_sub,C_neg,C_1]
      ring
    rw [←pEq] at scale
    exact no_interior_box H q cn scale v0 v1 B.unit

/-- The exact weak-four input consumed by the existing native ordered ERK16
assembly, with its *actual* primitive payment, and no new analysis of rows. -/
theorem weakFourScalarExclusion_of_boxes {J P₀ P₁ : K[X]}
    (R : FirstPencilReferences J P₀ P₁) (B : FirstBoxCover J P₀ P₁)
    {Q Z : K[X]} {a c : K}
    (H : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) : False :=
  no_firstStopPacket_of_boxes R B (firstStopPacket_of_ports H)

end
end RKCert.ReviewedNative.WeakFourFirstOnly
