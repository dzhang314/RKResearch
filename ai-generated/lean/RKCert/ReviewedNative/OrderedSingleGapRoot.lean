module

public import RKCert.ReviewedNative.OrderedRootGapSaturation
public import RKCert.ReviewedNative.OrderedIntervalSquareCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

@[expose] public section

/-! # One ordered gap root without a real-closure factory

Draft. The induction descends only in polynomial degree. A failed order
on an irreducible root's interval preorder would force a smaller gap
polynomial and thereby contradict its own positivity certificate.
-/
namespace RKCert.ReviewedNative.OrderedSingleGapRoot

open Polynomial
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.OrderedPreorderExtension
open RKCert.ReviewedNative.OrderedIntervalSquareCertificate

universe u

noncomputable section

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem change_iff_prod {x y : K} : Opposite x y ↔ x*y<0 := mul_neg_iff.symm

private theorem eval_ne_of_change {P : K[X]} {a b : K}
    (h : Opposite (P.eval a) (P.eval b)) : P.eval a ≠ 0 ∧ P.eval b ≠ 0 := by
  rcases h with ⟨ap,bn⟩ | ⟨an,bp⟩
  · exact ⟨ap.ne',bn.ne⟩
  · exact ⟨an.ne,bp.ne'⟩

private theorem not_unit_of_change {P : K[X]} {a b : K}
    (h : Opposite (P.eval a) (P.eval b)) : ¬ IsUnit P := by
  intro hu
  have c : P = C (P.coeff 0) :=
    eq_C_of_degree_le_zero (isUnit_iff_degree_eq_zero.mp hu).le
  have bad := change_iff_prod.mp h
  rw [c] at bad
  simp only [eval_C] at bad
  exact (not_lt_of_ge (mul_self_nonneg _)) bad

private theorem natDegree_pos_of_nonunit {P : K[X]} (ne : P≠0) (nu : ¬IsUnit P) :
    0<P.natDegree := by
  by_contra h
  have z : P.natDegree=0 := Nat.eq_zero_of_not_pos h
  have dz : P.degree=0 := by rw [degree_eq_natDegree ne,z,Nat.cast_zero]
  exact nu (isUnit_iff_degree_eq_zero.mpr dz)

private theorem gap_of_proper {g : K[X]} [Fact (Irreducible g)] {a b : K} (ab : a<b)
    (an : g.eval a≠0) (bn : g.eval b≠0)
    (proper : (-1 : AdjoinRoot g) ∉
      gapPreorder (AdjoinRoot.of g) a b ab (AdjoinRoot.root g)) :
    ∃ E : OrderedExtension K, rootInGap E g a b := by
  let e := AdjoinRoot.of g
  let r := AdjoinRoot.root g
  let C := gapPreorder e a b ab r
  obtain ⟨ord,sor,nn⟩ := ordered_of_preorder C
    ⟨gapPreorder_square e a b ab r,proper⟩
  letI : LinearOrder (AdjoinRoot g) := ord
  letI : IsStrictOrderedRing (AdjoinRoot g) := sor
  have mono : StrictMono e := by
    intro x y xy
    have h : 0≤e y-e x := by
      rw [← map_sub]
      exact nn _ (gapPreorder_base e a b ab r _ (sub_nonneg.mpr xy.le))
    exact lt_of_le_of_ne (sub_nonneg.mp h) (fun eq => xy.ne (e.injective eq))
  let E : OrderedExtension K := {
    carrier := AdjoinRoot g
    field := inferInstance
    order := ord
    strict := sor
    embed := e
    mono := mono }
  have isr : (g.map e).IsRoot r := AdjoinRoot.isRoot_root g
  have nza : e a≠r := by
    intro eq
    apply an
    apply e.injective
    rw [map_zero,← eval_on_base,eq]
    exact isr
  have nzb : r≠e b := by
    intro eq
    apply bn
    apply e.injective
    rw [map_zero,← eval_on_base,← eq]
    exact isr
  have left : e a ≤ r := sub_nonneg.mp (nn _ (gapPreorder_left e a b ab r))
  have right : r ≤ e b := sub_nonneg.mp (nn _ (gapPreorder_right e a b ab r))
  exact ⟨E,r,lt_of_le_of_ne left nza,lt_of_le_of_ne right nzb,isr⟩

/-- A degree-bounded strong induction proves the abstract one-gap
factory in the same universe as the input ordered field. -/
private theorem root_in_ordered_extension_aux (n : ℕ) :
    ∀ (P : K[X]), P.natDegree ≤ n → ∀ (a b : K), a<b →
      Opposite (P.eval a) (P.eval b) →
      ∃ E : OrderedExtension K, rootInGap E P a b := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro P pn a b ab opp
    have ep := eval_ne_of_change opp
    have p0 : P≠0 := fun eq => ep.1 (by simp [eq])
    have nu := not_unit_of_change opp
    have dpos := natDegree_pos_of_nonunit p0 nu
    rcases irreducible_or_factor nu with irr | ⟨F,G,fu,gu,factor⟩
    · let t := P.leadingCoeff⁻¹
      have t0 : t≠0 := inv_ne_zero (leadingCoeff_ne_zero.mpr p0)
      let g := P*C t
      have gm : g.Monic := monic_mul_leadingCoeff_inv p0
      have gi : Irreducible g := (irreducible_mul_isUnit (isUnit_C.mpr t0.isUnit)).mpr irr
      letI : Fact (Irreducible g) := ⟨gi⟩
      have gd : g.natDegree=P.natDegree := natDegree_mul_C t0
      have gp : 0<g.natDegree := by simpa only [gd] using dpos
      have gprod : g.eval a*g.eval b<0 := by
        have pos : 0<t^2 := sq_pos_of_ne_zero t0
        calc
          g.eval a*g.eval b = (P.eval a*P.eval b)*t^2 := by simp only [g,eval_mul,eval_C]; ring
          _ < 0 := mul_neg_of_neg_of_pos (change_iff_prod.mp opp) pos
      have good : (-1 : AdjoinRoot g) ∉
          gapPreorder (AdjoinRoot.of g) a b ab (AdjoinRoot.root g) := by
        intro bad
        obtain ⟨W,gW,Wd,pos⟩ := improper_gap_certificate gm gp ab bad
        obtain ⟨Q,WQ⟩ := gW
        have Wa : 0<W.eval a := by
          simpa only [Polynomial.map_id,RingHom.id_apply] using
            pos K (RingHom.id K) strictMono_id a le_rfl ab.le
        have Wb : 0<W.eval b := by
          simpa only [Polynomial.map_id,RingHom.id_apply] using
            pos K (RingHom.id K) strictMono_id b ab.le le_rfl
        have Q0 : Q≠0 := by
          intro eq
          simp only [WQ,eq,mul_zero,eval_zero,lt_irrefl] at Wa
        have dQ : Q.natDegree<g.natDegree := by
          rw [WQ,natDegree_mul gm.ne_zero Q0] at Wd
          omega
        have Wprod : W.eval a*W.eval b =
            (g.eval a*g.eval b)*(Q.eval a*Q.eval b) := by
          simp only [WQ,eval_mul]
          ring
        have Qprod : Q.eval a*Q.eval b<0 := by
          by_contra nh
          have badW := mul_nonpos_of_nonpos_of_nonneg gprod.le (le_of_not_gt nh)
          rw [← Wprod] at badW
          exact (not_lt_of_ge badW) (mul_pos Wa Wb)
        have Qn : Q.natDegree<n := dQ.trans_le (gd.trans_le pn)
        obtain ⟨E,x,ax,xb,xq⟩ := ih Q.natDegree Qn Q le_rfl a b ab
          (change_iff_prod.mpr Qprod)
        have val := pos E.carrier E.embed E.mono x ax.le xb.le
        have zero : (W.map E.embed).eval x=0 := by
          rw [WQ,Polynomial.map_mul,eval_mul,show (Q.map E.embed).eval x=0 from xq,mul_zero]
        exact (ne_of_gt val) zero
      have endNe := eval_ne_of_change (change_iff_prod.mpr gprod)
      obtain ⟨E,x,ax,xb,xg⟩ := gap_of_proper ab endNe.1 endNe.2 good
      refine ⟨E,x,ax,xb,?_⟩
      change (g.map E.embed).eval x=0 at xg
      simp only [g,Polynomial.map_mul,map_C,eval_mul,eval_C] at xg
      exact (mul_eq_zero.mp xg).resolve_right (fun eq => t0 (E.embed.injective (by
        simpa only [map_zero] using eq)))
    · have f0 : F≠0 := by
        intro eq
        exact p0 (by rw [factor,eq,zero_mul])
      have g0 : G≠0 := by
        intro eq
        exact p0 (by rw [factor,eq,mul_zero])
      have fd := natDegree_pos_of_nonunit f0 fu
      have gd := natDegree_pos_of_nonunit g0 gu
      have sum : P.natDegree=F.natDegree+G.natDegree := by
        rw [factor,natDegree_mul f0 g0]
      have both : (F.eval a*F.eval b)*(G.eval a*G.eval b)<0 := by
        have val : P.eval a*P.eval b = (F.eval a*F.eval b)*(G.eval a*G.eval b) := by
          simp only [factor,eval_mul]
          ring
        rw [← val]
        exact change_iff_prod.mp opp
      by_cases first : F.eval a*F.eval b<0
      · have low : F.natDegree<n := by omega
        obtain ⟨E,x,ax,xb,xf⟩ := ih F.natDegree low F le_rfl a b ab (change_iff_prod.mpr first)
        refine ⟨E,x,ax,xb,?_⟩
        change (P.map E.embed).eval x=0
        rw [factor,Polynomial.map_mul,eval_mul,show (F.map E.embed).eval x=0 from xf,zero_mul]
      · have second : G.eval a*G.eval b<0 := by
          by_contra hn
          exact (not_lt_of_ge (mul_nonneg (le_of_not_gt first) (le_of_not_gt hn))) both
        have low : G.natDegree<n := by omega
        obtain ⟨E,x,ax,xb,xg⟩ := ih G.natDegree low G le_rfl a b ab (change_iff_prod.mpr second)
        refine ⟨E,x,ax,xb,?_⟩
        change (P.map E.embed).eval x=0
        rw [factor,Polynomial.map_mul,eval_mul,show (G.map E.embed).eval x=0 from xg,mul_zero]

theorem singleGapFactory : SingleGapFactory.{u} := by
  intro K _ _ _ P a b ab opp
  exact root_in_ordered_extension_aux P.natDegree P le_rfl a b ab opp

theorem exists_unitRootSource (p : K[X]) :
    ∃ E : OrderedExtension K, UnitRootSource E.embed p :=
  unitRootSource_of_singleGapFactory singleGapFactory p

end
end RKCert.ReviewedNative.OrderedSingleGapRoot
