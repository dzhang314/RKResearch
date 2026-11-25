module

public import RKCert.ReviewedNative.FiniteRootSeparator
public import RKCert.ReviewedNative.FiniteOrderedSignWindows
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Base two-change crossed phase to a positive quadratic residual

Draft. The only ordered-extension input is the ability to select an
actual root of this polynomial in any paid base sign gap. The conclusion
is nonnegativity at the images of the base samples, not in the whole
extension interval.
-/
namespace RKCert.ReviewedNative.CrossedPositiveTailRoots

open Polynomial Set
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.FiniteRootSeparator

noncomputable section
variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- The actual open-unit base phase, in the monic sign orientation. -/
structure CrossedSignPhase (p : K[X]) (z h a u : K) : Prop where
  z0 : 0<z
  zh : z<h
  ha : h<a
  au : a<u
  u1 : u<1
  zpos : 0<p.eval z
  hneg : p.eval h<0
  aneg : p.eval a<0
  upos : 0<p.eval u
  noThree : ¬ HasAlternationsOn p (Ioo (0:K) 1) 3

private theorem opposite_left_ne {x y : K} (h : Opposite x y) : x ≠ 0 := by
  rcases h with ⟨hp,_⟩ | ⟨hn,_⟩
  · exact hp.ne'
  · exact hn.ne

private theorem opposite_right_ne {x y : K} (h : Opposite x y) : y ≠ 0 := by
  rcases h with ⟨_,hn⟩ | ⟨_,hp⟩
  · exact hn.ne
  · exact hp.ne'

private theorem signs_ne {x y : K} (h : Opposite x y) :
    SignType.sign x ≠ SignType.sign y := by
  rcases h with ⟨hp,hn⟩ | ⟨hn,hp⟩
  · rw [sign_pos hp,sign_neg hn]; decide
  · rw [sign_neg hn,sign_pos hp]; decide

theorem three_changes_of_alternating_four (p : K[X]) {a b c d : K}
    (aI : a ∈ Ioo (0:K) 1) (bI : b ∈ Ioo (0:K) 1)
    (cI : c ∈ Ioo (0:K) 1) (dI : d ∈ Ioo (0:K) 1)
    (ab : a<b) (bc : b<c) (cd : c<d)
    (sa : Opposite (p.eval a) (p.eval b))
    (sb : Opposite (p.eval b) (p.eval c))
    (sc : Opposite (p.eval c) (p.eval d)) :
    HasAlternationsOn p (Ioo (0:K) 1) 3 := by
  refine ⟨[a,b,c,d],?_,?_,?_⟩
  · simp [List.pairwise_cons,ab,bc,cd,ab.trans bc,ab.trans (bc.trans cd),bc.trans cd]
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact aI
    · exact bI
    · exact cI
    · exact dI
  · simp only [variation,List.map_cons,List.map_nil]
    rw [List.signVariations_cons_cons_of_ne_zero _ (opposite_left_ne sa) (opposite_right_ne sa),
      List.signVariations_cons_cons_of_ne_zero _ (opposite_left_ne sb) (opposite_right_ne sb),
      List.signVariations_cons_cons_of_ne_zero _ (opposite_left_ne sc) (opposite_right_ne sc)]
    simp [signs_ne sa,signs_ne sb,signs_ne sc]

private theorem zI {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u) :
    z ∈ Ioo (0:K) 1 := ⟨P.z0,P.zh.trans (P.ha.trans (P.au.trans P.u1))⟩

private theorem hI {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u) :
    h ∈ Ioo (0:K) 1 := ⟨P.z0.trans P.zh,P.ha.trans (P.au.trans P.u1)⟩

private theorem aI {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u) :
    a ∈ Ioo (0:K) 1 := ⟨(P.z0.trans P.zh).trans P.ha,P.au.trans P.u1⟩

private theorem uI {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u) :
    u ∈ Ioo (0:K) 1 := ⟨((P.z0.trans P.zh).trans P.ha).trans P.au,P.u1⟩

private theorem phase_end_nonneg {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u) :
    0≤p.eval 0 ∧ 0≤p.eval 1 := by
  constructor
  · by_contra bad
    obtain ⟨x,x0,xz,xneg⟩ := eval_neg_somewhere_right p P.z0 (lt_of_not_ge bad)
    exact P.noThree (three_changes_of_alternating_four p ⟨x0,xz.trans (zI P).2⟩
      (zI P) (hI P) (uI P) xz P.zh (P.ha.trans P.au)
      (Or.inr ⟨xneg,P.zpos⟩) (Or.inl ⟨P.zpos,P.hneg⟩) (Or.inr ⟨P.hneg,P.upos⟩))
  · by_contra bad
    obtain ⟨x,ux,x1,xneg⟩ := eval_neg_somewhere_left p P.u1 (lt_of_not_ge bad)
    exact P.noThree (three_changes_of_alternating_four p (zI P) (hI P) (uI P)
      ⟨(uI P).1.trans ux,x1⟩ P.zh (P.ha.trans P.au) ux
      (Or.inl ⟨P.zpos,P.hneg⟩) (Or.inr ⟨P.hneg,P.upos⟩) (Or.inl ⟨P.upos,xneg⟩))

private theorem left_pos_lt_neg {p : K[X]} {z h a u x y : K}
    (P : CrossedSignPhase p z h a u)
    (xI : x ∈ Ioo (0:K) 1) (yI : y ∈ Ioo (0:K) 1)
    (xh : x<h) (xp : 0<p.eval x) (yn : p.eval y<0) : x<y := by
  by_contra bad
  rcases (le_of_not_gt bad).lt_or_eq with yx | eq
  · exact P.noThree (three_changes_of_alternating_four p yI xI (hI P) (uI P)
      yx xh (P.ha.trans P.au)
      (Or.inr ⟨yn,xp⟩) (Or.inl ⟨xp,P.hneg⟩) (Or.inr ⟨P.hneg,P.upos⟩))
  · subst y
    exact (not_lt_of_ge xp.le) yn

private theorem neg_lt_right_pos {p : K[X]} {z h a u x y : K}
    (P : CrossedSignPhase p z h a u)
    (xI : x ∈ Ioo (0:K) 1) (yI : y ∈ Ioo (0:K) 1)
    (hy : h<y) (xn : p.eval x<0) (yp : 0<p.eval y) : x<y := by
  by_contra bad
  rcases (le_of_not_gt bad).lt_or_eq with yx | eq
  · exact P.noThree (three_changes_of_alternating_four p (zI P) (hI P) yI xI
      P.zh hy yx
      (Or.inl ⟨P.zpos,P.hneg⟩) (Or.inr ⟨P.hneg,yp⟩) (Or.inl ⟨yp,xn⟩))
  · subst y
    exact (not_lt_of_ge yp.le) xn

/-- The data provided by selecting the two sign-changing gap roots. -/
structure RootResidual (e : K →+* L) (p : K[X]) (z h a u : K)
    (r s : L) (B : L[X]) : Prop where
  zr : e z<r
  rh : r<e h
  as' : e a<s
  su : s<e u
  rRoot : (p.map e).IsRoot r
  sRoot : (p.map e).IsRoot s
  monic : B.Monic
  degree : B.natDegree=2
  factor : p.map e = B*((X-C r)*(X-C s))
  baseNonneg : ∀ x ∈ Icc (0:K) 1, 0≤B.eval (e x)

private theorem nonnegative_residual_on_base (e : K →+* L) (ord : StrictMono e)
    {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u)
    {r s : L} {B : L[X]} (zr : e z<r) (rh : r<e h) (as' : e a<s) (su : s<e u)
    (factor : p.map e = B*((X-C r)*(X-C s)))
    (left : ∀ x ∈ Ioo (0:K) 1, x<h → 0<p.eval x → e x<r)
    (right : ∀ x ∈ Ioo (0:K) 1, h<x → 0<p.eval x → s<e x)
    (negative : ∀ x ∈ Ioo (0:K) 1, p.eval x<0 → r<e x ∧ e x<s) :
    ∀ x ∈ Icc (0:K) 1, 0≤B.eval (e x) := by
  have hsH : e h<s := (ord P.ha).trans as'
  have rs : r<s := rh.trans hsH
  have fval (x : K) :
      e (p.eval x) = B.eval (e x)*((e x-r)*(e x-s)) := by
    simpa only [eval_on_base,eval_mul,eval_sub,eval_X,eval_C] using
      congrArg (Polynomial.eval (e x)) factor
  have endSign := phase_end_nonneg P
  intro x hx
  by_contra bad
  have bn : B.eval (e x)<0 := lt_of_not_ge bad
  by_cases x0 : x=0
  · subst x
    have a0 : e 0<r := (ord P.z0).trans zr
    have b0 : e 0<s := a0.trans rs
    have qp : 0≤e (p.eval 0) := by simpa only [map_zero] using ord.monotone endSign.1
    exact (not_lt_of_ge qp) ((fval 0).trans_lt (mul_neg_of_neg_of_pos bn
      (mul_pos_of_neg_of_neg (sub_neg.mpr a0) (sub_neg.mpr b0))))
  by_cases x1 : x=1
  · subst x
    have b1 : s<e 1 := su.trans (ord P.u1)
    have a1 : r<e 1 := rs.trans b1
    have qp : 0≤e (p.eval 1) := by simpa only [map_zero] using ord.monotone endSign.2
    exact (not_lt_of_ge qp) ((fval 1).trans_lt (mul_neg_of_neg_of_pos bn
      (mul_pos (sub_pos.mpr a1) (sub_pos.mpr b1))))
  have xi : x ∈ Ioo (0:K) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm x0),lt_of_le_of_ne hx.2 x1⟩
  rcases lt_trichotomy (p.eval x) 0 with xn | xz | xp
  · have sel := negative x xi xn
    have nx : e (p.eval x)<0 := by simpa only [map_zero] using ord xn
    exact (not_lt_of_ge nx.le) ((mul_pos_of_neg_of_neg bn
      (mul_neg_of_pos_of_neg (sub_pos.mpr sel.1) (sub_neg.mpr sel.2))).trans_eq (fval x).symm)
  · by_cases xr : e x=r
    · have xh : x<h := ord.lt_iff_lt.mp (by simpa only [xr] using rh)
      have fx : p.map e = (X-C (e x))*(B*(X-C s)) := by rw [factor,xr]; ring
      let A := p /ₘ (X-C x)
      have dx : (X-C x)*A=p :=
        mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mapped_factor e p x fx)
      have mp : A.map e = B*(X-C s) := map_base_quotient e p x _ fx
      have ev : e (A.eval x)= B.eval (e x)*(e x-s) := by
        simpa only [eval_on_base,eval_mul,eval_sub,eval_X,eval_C] using
          congrArg (Polynomial.eval (e x)) mp
      have av : 0<A.eval x := ord.lt_iff_lt.mp (by
        rw [map_zero,ev]
        exact mul_pos_of_neg_of_neg bn (sub_neg.mpr (by simpa only [xr] using rs)))
      obtain ⟨y,xy,yh,ya⟩ := eval_pos_somewhere_right A xh av
      have yp : 0<p.eval y := by
        rw [← dx,eval_mul,eval_sub,eval_X,eval_C]
        exact mul_pos (sub_pos.mpr xy) ya
      have badL := left y ⟨xi.1.trans xy,yh.trans (hI P).2⟩ yh yp
      rw [← xr] at badL
      exact (not_lt_of_ge (ord xy).le) badL
    · by_cases xs : e x=s
      · have hx' : h<x := ord.lt_iff_lt.mp (by simpa only [xs] using hsH)
        have fx : p.map e = (X-C (e x))*(B*(X-C r)) := by rw [factor,xs]; ring
        let A := p /ₘ (X-C x)
        have dx : (X-C x)*A=p :=
          mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mapped_factor e p x fx)
        have mp : A.map e = B*(X-C r) := map_base_quotient e p x _ fx
        have ev : e (A.eval x)= B.eval (e x)*(e x-r) := by
          simpa only [eval_on_base,eval_mul,eval_sub,eval_X,eval_C] using
            congrArg (Polynomial.eval (e x)) mp
        have av : A.eval x<0 := ord.lt_iff_lt.mp (by
          rw [map_zero,ev]
          exact mul_neg_of_neg_of_pos bn (sub_pos.mpr (by simpa only [xs] using rs)))
        obtain ⟨y,hy,yx,ya⟩ := eval_neg_somewhere_left A hx' av
        have yp : 0<p.eval y := by
          rw [← dx,eval_mul,eval_sub,eval_X,eval_C]
          exact mul_pos_of_neg_of_neg (sub_neg.mpr yx) ya
        have badR := right y ⟨(hI P).1.trans hy,yx.trans xi.2⟩ hy yp
        rw [← xs] at badR
        exact (not_lt_of_ge (ord yx).le) badR
      · have f := fval x
        rw [xz,map_zero] at f
        exact (mul_ne_zero bn.ne (mul_ne_zero (sub_ne_zero.mpr xr) (sub_ne_zero.mpr xs))) f.symm
  · have px : 0<e (p.eval x) := by simpa only [map_zero] using ord xp
    rcases lt_trichotomy x h with xh | hh | hx'
    · have xr := left x xi xh xp
      exact (not_lt_of_ge px.le) ((fval x).trans_lt (mul_neg_of_neg_of_pos bn
        (mul_pos_of_neg_of_neg (sub_neg.mpr xr) (sub_neg.mpr (xr.trans rs)))))
    · subst x
      exact (not_lt_of_ge xp.le) P.hneg
    · have sx := right x xi hx' xp
      exact (not_lt_of_ge px.le) ((fval x).trans_lt (mul_neg_of_neg_of_pos bn
        (mul_pos (sub_pos.mpr (rs.trans sx)) (sub_pos.mpr sx))))

/-- Root-source bridge: no ordered completeness or base density is used.
A supplied real closure is one way to instantiate the root source, but
all signs used by the theorem are on the original ordered base. -/
theorem root_residual_of_crossed_phase (e : K →+* L) (ord : StrictMono e)
    {p : K[X]} {z h a u : K} (P : CrossedSignPhase p z h a u)
    (monic : p.Monic) (degree : p.natDegree=4) (source : UnitRootSource e p) :
    ∃ (r s : L) (B : L[X]), RootResidual e p z h a u r s B := by
  classical
  let A : Set K := {x | x ∈ Ioo (0:K) 1 ∧ x<h ∧ 0<p.eval x}
  let N : Set K := {x | x ∈ Ioo (0:K) 1 ∧ p.eval x<0}
  let D : Set K := {x | x ∈ Ioo (0:K) 1 ∧ h<x ∧ 0<p.eval x}
  let F := (p.map e).roots.toFinset
  have froot {x : L} : x ∈ F ↔ (p.map e).IsRoot x := by
    simp only [F,Multiset.mem_toFinset,Polynomial.mem_roots (monic.map e).ne_zero]
  have zA : z ∈ A := ⟨zI P,P.zh,P.zpos⟩
  have hN : h ∈ N := ⟨hI P,P.hneg⟩
  have aN : a ∈ N := ⟨aI P,P.aneg⟩
  have uD : u ∈ D := ⟨uI P,P.ha.trans P.au,P.upos⟩
  have gapL : ∀ x ∈ A, ∀ y ∈ N, ∃ t ∈ F, e x<t ∧ t<e y := by
    intro x hx y hy
    have order := left_pos_lt_neg P hx.1 hy.1 hx.2.1 hx.2.2 hy.2
    obtain ⟨t,xt,ty,ht⟩ := source hx.1 hy.1 order (Or.inl ⟨hx.2.2,hy.2⟩)
    exact ⟨t,froot.mpr ht,xt,ty⟩
  have gapR : ∀ x ∈ N, ∀ y ∈ D, ∃ t ∈ F, e x<t ∧ t<e y := by
    intro x hx y hy
    have order := neg_lt_right_pos P hx.1 hy.1 hy.2.1 hx.2 hy.2.2
    obtain ⟨t,xt,ty,ht⟩ := source hx.1 hy.1 order (Or.inr ⟨hx.2,hy.2.2⟩)
    exact ⟨t,froot.mpr ht,xt,ty⟩
  obtain ⟨r,hr,rL,rN⟩ := finite_strict_separator F A N e e ⟨z,zA⟩ ⟨h,hN⟩ gapL
  obtain ⟨s,hs,sN,sR⟩ := finite_strict_separator F N D e e ⟨h,hN⟩ ⟨u,uD⟩ gapR
  have rs : r<s := (rN h hN).trans (sN h hN)
  have deg : (p.map e).natDegree=4 := by rw [natDegree_map_eq_of_injective e.injective,degree]
  obtain ⟨B,bm,bd,fact⟩ :=
    monic_quadratic_of_two_roots (p.map e) (monic.map e) deg rs (froot.mp hr) (froot.mp hs)
  refine ⟨r,s,B,rL z zA,rN h hN,sN a aN,sR u uD,froot.mp hr,froot.mp hs,bm,bd,fact,?_⟩
  exact nonnegative_residual_on_base e ord P (rL z zA) (rN h hN) (sN a aN) (sR u uD) fact
    (fun x xi xh xp => rL x ⟨xi,xh,xp⟩)
    (fun x xi hx xp => sR x ⟨xi,hx,xp⟩)
    (fun x xi xn => ⟨rN x ⟨xi,xn⟩,sN x ⟨xi,xn⟩⟩)

end
end RKCert.ReviewedNative.CrossedPositiveTailRoots
