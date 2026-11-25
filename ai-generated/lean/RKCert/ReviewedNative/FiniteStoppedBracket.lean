module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows
public import RKCert.ReviewedNative.OrderedRightPoleInterpolation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A degree-paid stopped quadrature bracket

The two finite meshes are integration nodes only; a separately supplied
sign separator may use additional samples.  The interpolants never
integrate a rational function.  No ordering of undisplayed roots is
needed, and the nodal law can have signed weights. -/

namespace RKCert.ReviewedNative.FiniteStoppedBracket

open Polynomial
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.RightPoleInterpolation

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The polynomial whose reciprocal has the indicated right poles. -/
def poleProduct (ds : List K) : K[X] := (ds.map (fun a => C a-X)).prod

private theorem poleProduct_nil : poleProduct ([] : List K) = 1 := rfl

private theorem poleProduct_cons (a : K) (ds : List K) :
    poleProduct (a::ds) = (C a-X)*poleProduct ds := rfl

private theorem cutProduct_append (xs ys : List K) :
    cutProduct (xs++ys) = cutProduct xs*cutProduct ys := by
  simp only [cutProduct, List.map_append, List.prod_append]

private theorem poleProduct_append (xs ys : List K) :
    poleProduct (xs++ys) = poleProduct xs*poleProduct ys := by
  simp only [poleProduct, List.map_append, List.prod_append]

private theorem poleProduct_degree (ds : List K) : (poleProduct ds).natDegree ≤ ds.length := by
  induction ds with
  | nil => simp [poleProduct_nil]
  | cons a ds ih =>
      have one : (C a-X : K[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp)
      rw [poleProduct_cons, List.length_cons]
      exact (natDegree_mul_le_of_le one ih).trans_eq (Nat.add_comm _ _)

private theorem cutProduct_ne_zero (xs : List K) : cutProduct xs ≠ 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [cutProduct_cons]
      exact mul_ne_zero (X_sub_C_ne_zero a) ih

private theorem cut_at_knot {xs : List K} {x : K} (hx : x ∈ xs) :
    (cutProduct xs).eval x = 0 := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with e | m
      · subst a
        simp [cutProduct_cons, eval_mul, eval_sub]
      · simp [cutProduct_cons, eval_mul, ih m]

private theorem pole_at_knot {xs : List K} {x : K} (hx : x ∈ xs) :
    (poleProduct xs).eval x = 0 := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with e | m
      · subst a
        simp [poleProduct_cons, eval_mul, eval_sub]
      · simp [poleProduct_cons, eval_mul, ih m]

theorem poleProduct_pos (xs : List K) (x : K) (below : ∀ a∈xs, x<a) :
    0 < (poleProduct xs).eval x := by
  induction xs with
  | nil => simp [poleProduct_nil]
  | cons a xs ih =>
      simp only [poleProduct_cons, eval_mul, eval_sub, eval_C, eval_X]
      exact mul_pos (sub_pos.mpr (below a (by simp)))
        (ih (fun y hy => below y (List.mem_cons_of_mem _ hy)))

theorem poleProduct_orientation (xs : List K) (x : K) :
    (poleProduct xs).eval x = (-1:K)^xs.length*(cutProduct xs).eval x := by
  induction xs with
  | nil => simp [poleProduct_nil]
  | cons a xs ih =>
      simp only [poleProduct_cons, cutProduct_cons, eval_mul, eval_sub, eval_X, eval_C,
        ih, List.length_cons, pow_succ]
      ring

private theorem reciprocal_product (ds : List K) (x : K) (below : ∀ a∈ds, x<a) :
    (poleProduct ds).eval x * (ds.map (fun a => (a-x)⁻¹)).prod = 1 := by
  induction ds with
  | nil => simp [poleProduct_nil]
  | cons a ds ih =>
      have ax : a-x ≠ 0 := (sub_pos.mpr (below a (by simp))).ne'
      have tail := ih (fun y hy => below y (List.mem_cons_of_mem _ hy))
      simp only [poleProduct_cons, eval_mul, eval_sub, eval_C, eval_X, List.map_cons,
        List.prod_cons]
      calc
        _ = ((a-x)*(a-x)⁻¹) *
            ((poleProduct ds).eval x*(ds.map (fun y => (y-x)⁻¹)).prod) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ ax, tail, one_mul]

private theorem rightPoleFun_of_list {v : K} (ds : List K) (ne : ds ≠ [])
    (right : ∀ d∈ds, v≤d) :
    RightPoleFun v (fun x => (ds.map (fun d => (d-x)⁻¹)).prod) := by
  cases ds with
  | nil => exact False.elim (ne rfl)
  | cons d ds =>
      have base := RightPoleFun.pole d (right d (by simp))
      have prod := base.mul_pole_list ds (fun a ha => right a (List.mem_cons_of_mem _ ha))
      simpa only [List.map_cons, List.prod_cons] using prod

private theorem exists_between_right_list {t : K} (xs : List K) (rt : ∀ x∈xs, t<x) :
    ∃ v, t<v ∧ ∀ x∈xs, v<x := by
  induction xs with
  | nil => exact ⟨t+1, lt_add_of_pos_right _ zero_lt_one, by simp⟩
  | cons a xs ih =>
      obtain ⟨z,tz,tail⟩ := ih (fun y hy => rt y (List.mem_cons_of_mem _ hy))
      have ta := rt a (by simp)
      refine ⟨min z ((t+a)/2), lt_min tz (left_lt_add_div_two.mpr ta), ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | mem
      · exact (min_le_right _ _).trans_lt (add_div_two_lt_right.mpr ta)
      · exact (min_le_left _ _).trans_lt (tail y mem)

/-- The marked locations may already be grouped; no tableau is imported. -/
def atomSum (xs : List K) (μ f : K → K) : K := (xs.map (fun x => μ x*f x)).sum

private theorem atomSum_congr {xs : List K} {μ f g : K → K}
    (h : ∀ x∈xs, f x = g x) : atomSum xs μ f = atomSum xs μ g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change μ a*f a+atomSum xs μ f = μ a*g a+atomSum xs μ g
      rw [h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem atomSum_zero_of {xs : List K} {μ f : K → K}
    (h : ∀ x∈xs, f x = 0) : atomSum xs μ f = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change μ a*f a+atomSum xs μ f = 0
      rw [h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), mul_zero, add_zero]

/-- One degree per sign separator and two per off-stop label. -/
def bracketDegree (L R left right : List K) : ℕ :=
  L.length+R.length+2*(left.length+right.length)

/-- A common finite sign fit, normalized at the stop.  The right factor
parity converts the ordinary nodal product into right-pole orientation. -/
structure StopSeparator (P : K[X]) (l t r τ : K) (L R : List K) : Prop where
  cutLeft : ∀ x∈L, x<t
  cutRight : ∀ x∈R, t<x
  fitLeft : ∀ i : Fin 19, P.eval (intervalPoint l t i) ≠ 0 →
    0 < τ*P.eval (intervalPoint l t i)*(cutProduct L).eval (intervalPoint l t i)
  fitRight : ∀ i : Fin 19, P.eval (intervalPoint t r i) ≠ 0 →
    0 < (τ*(-1:K)^R.length)*P.eval (intervalPoint t r i)*(cutProduct R).eval (intervalPoint t r i)

set_option maxRecDepth 3800
set_option maxHeartbeats 1200000

/-- Two degree-paid exact tests squeeze a true zero at a marked stop.
The local weight is A; the global signed law uses A times H, where
H is the positive product of the nonempty right pole factors.  Values
of H are inverted only at displayed labels, never under an integral. -/
theorem strict_bracket_of_pole_grid {l t r τ : K} (lt : l<t) (tr : t<r)
    {A P : K[X]} {μ : K → K} {b : ℕ}
    (D L R left right : List K) (nonempty : D ≠ [])
    (polesRight : ∀ d∈D, r≤d) (sep : StopSeparator P l t r τ L R)
    (atomsLeft : ∀ x∈left, x<t) (atomsRight : ∀ x∈right, t<x)
    (positiveLeft : ∀ i : Fin 19, 0 < A.eval (intervalPoint l t i))
    (nonnegativeRight : ∀ i : Fin 19, 0 ≤ A.eval (intervalPoint t r i))
    (pn : P ≠ 0) (survive : P.natDegree+left.length<19)
    (localDegree : (A*P).natDegree≤19)
    (paid : bracketDegree L R left right≤b)
    (grid : A.natDegree+(poleProduct D).natDegree+P.natDegree+
      bracketDegree L R left right≤19)
    (law : ∀ B : K[X], B.natDegree≤b →
      integral l r (A*poleProduct D*P*B) =
        atomSum left μ B.eval + μ t*B.eval t + atomSum right μ B.eval)
    (localZero : integral l t (A*P)=0) :
    let S := atomSum left μ (fun x => ((poleProduct D).eval x)⁻¹)
    let J := μ t*((poleProduct D).eval t)⁻¹
    τ*S < 0 ∧ 0 < τ*(S+J) := by
  let H := poleProduct D
  let S := atomSum left μ (fun x => (H.eval x)⁻¹)
  let J₀ := μ t*(H.eval t)⁻¹
  change τ*S < 0 ∧ 0 < τ*(S+J₀)
  let landmarks := r :: (R ++ (right ++ List.ofFn (intervalPoint t r)))
  have landmark (x : K) (hx : x∈landmarks) : t<x := by
    simp only [landmarks, List.mem_cons, List.mem_append] at hx
    rcases hx with e | hR | hA | hg
    · subst x
      exact tr
    · exact sep.cutRight x hR
    · exact atomsRight x hA
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
      exact (intervalPoint_mem tr i).1
  obtain ⟨v₀,tv₀,gap⟩ := exists_between_right_list landmarks landmark
  have v₀r : v₀<r := gap r (by simp [landmarks])
  have both (keep : Bool) :
      0 < (if keep then (1:K) else -1)*τ*(S+(if keep then J₀ else 0)) := by
    let v := if keep then v₀ else t
    let extra := if keep then [] else [t]
    let anchor := if keep then [t] else []
    let ps := R ++ (right ++ (right ++ extra))
    let ks := L ++ (left ++ (left ++ anchor))
    let F (x : K) := (D.map (fun a => (a-x)⁻¹)).prod *
      (ps.map (fun a => (a-x)⁻¹)).prod
    have tv : t≤v := by cases keep <;> simp [v,tv₀.le]
    have vr : v≤r := by cases keep <;> simp [v,v₀r.le,tr.le]
    have dp (d : K) (hd : d∈D) : v≤d := vr.trans (polesRight d hd)
    have pr (a : K) (ha : a∈R) : v≤a := by
      cases keep
      · exact (sep.cutRight a ha).le
      · exact (gap a (by simp [landmarks,ha])).le
    have pa (a : K) (ha : a∈right) : v≤a := by
      cases keep
      · exact (atomsRight a ha).le
      · exact (gap a (by simp [landmarks,ha])).le
    have pg (i : Fin 19) : v < intervalPoint t r i := by
      cases keep
      · exact (intervalPoint_mem tr i).1
      · have mem : intervalPoint t r i ∈ List.ofFn (intervalPoint t r) :=
          List.mem_ofFn.mpr ⟨i,rfl⟩
        exact gap (intervalPoint t r i) (List.mem_cons_of_mem r
          (List.mem_append_right R (List.mem_append_right right mem)))
    have pp (d : K) (hd : d∈ps) : v≤d := by
      simp only [ps,List.mem_append] at hd
      rcases hd with ha | ha | ha | ha
      · exact pr d ha
      · exact pa d ha
      · exact pa d ha
      · cases keep
        · have eq : d=t := by simpa [extra] using ha
          subst d
          exact le_rfl
        · simp [extra] at ha
    have kk (d : K) (hd : d∈ks) : d<v := by
      simp only [ks,List.mem_append] at hd
      rcases hd with ha | ha | ha | ha
      · exact (sep.cutLeft d ha).trans_le tv
      · exact (atomsLeft d ha).trans_le tv
      · exact (atomsLeft d ha).trans_le tv
      · cases keep
        · simp [anchor] at ha
        · have eq : d=t := by simpa [anchor] using ha
          subst d
          exact tv₀
    have f : RightPoleFun v F := (rightPoleFun_of_list D nonempty dp).mul_pole_list ps pp
    obtain ⟨B,g,E⟩ := f.interpolant ks kk
    let N := poleProduct ps
    let T := N*B
    have td : T.natDegree ≤ bracketDegree L R left right := by
      by_cases empty : ks=[]
      · simp [T,E.empty empty]
      have live := List.length_pos_iff.mpr empty
      apply (natDegree_mul_le_of_le (poleProduct_degree ps) E.degree).trans
      cases keep <;> simp [ps,ks,extra,anchor,bracketDegree] at live ⊢ <;> omega
    have recip (x : K) (xv : x<v) : H.eval x*N.eval x*F x=1 := by
      dsimp only [H,N,F]
      calc
        _ = ((poleProduct D).eval x*(D.map (fun a => (a-x)⁻¹)).prod) *
            ((poleProduct ps).eval x*(ps.map (fun a => (a-x)⁻¹)).prod) := by ring
        _ = 1 := by
          rw [reciprocal_product D x (fun a ha => xv.trans_le (dp a ha)),
            reciprocal_product ps x (fun a ha => xv.trans_le (pp a ha)), one_mul]
    have knotValue (x : K) (mem : x∈ks) : T.eval x = (H.eval x)⁻¹ := by
      have xv := kk x mem
      have hB : F x = B.eval x := sub_eq_zero.mp (by
        rw [E.error x xv, cut_at_knot mem, zero_mul])
      have hn : H.eval x ≠ 0 := (poleProduct_pos D x
        (fun a ha => xv.trans_le (dp a ha))).ne'
      have target : H.eval x*T.eval x=1 := by
        simp only [T, eval_mul, ← hB]
        rw [← mul_assoc, recip x xv]
      rw [← one_div, eq_div_iff hn, mul_comm]
      exact target
    have leftValue (x : K) (hx : x∈left) : T.eval x = (H.eval x)⁻¹ :=
      knotValue x (by simp [ks,hx])
    have rightValue (x : K) (hx : x∈right) : T.eval x = 0 := by
      have hx' : x∈ps := by simp [ps,hx]
      simp only [T,N,eval_mul,pole_at_knot hx',zero_mul]
    have stopValue : T.eval t = if keep then (H.eval t)⁻¹ else 0 := by
      cases keep
      · have ht' : t∈ps := by simp [ps,extra]
        simp [T,N,pole_at_knot ht']
      · simpa using knotValue t (by simp [ks,anchor])
    have leftShape (x : K) : (cutProduct ks).eval x =
        (cutProduct L).eval x*((cutProduct left).eval x)^2*(if keep then x-t else 1) := by
      cases keep <;>
        simp [ks,anchor,cutProduct_append,eval_mul,eval_sub,pow_two] <;> ring
    have rightShape (x : K) : N.eval x =
        (-1:K)^R.length*(cutProduct R).eval x*((poleProduct right).eval x)^2*
          (if keep then 1 else t-x) := by
      cases keep <;>
        simp [N,ps,extra,poleProduct_append,poleProduct_nil,poleProduct_cons,eval_mul,eval_sub,
          poleProduct_orientation R x,pow_two] <;> ring
    let k : K := if keep then 1 else -1
    let G := A*H*P*T
    let Gₗ := C (k*τ)*(G-A*P)
    let Gᵣ := C (k*τ)*G
    let stopL (x : K) : K := if keep then t-x else 1
    let stopR (x : K) : K := if keep then 1 else x-t
    have Gd : G.natDegree≤19 :=
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le
        (natDegree_mul_le (p:=A) (q:=H)) (le_refl P.natDegree)) td).trans grid
    have gdL : Gₗ.natDegree≤19 :=
      (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le Gd localDegree))
    have gdR : Gᵣ.natDegree≤19 := (natDegree_C_mul_le _ _).trans Gd
    have evalL (x : K) (xt : x<t) : Gₗ.eval x =
        (A.eval x*(τ*P.eval x*(cutProduct L).eval x))*
          ((H.eval x*N.eval x)*(((cutProduct left).eval x)^2*(stopL x*g x))) := by
      have xv := xt.trans_le tv
      have delta : H.eval x*N.eval x*B.eval x-1 =
          -(H.eval x*N.eval x)*((cutProduct ks).eval x*g x) := by
        calc
          _ = H.eval x*N.eval x*(B.eval x-F x) := by rw [mul_sub,recip x xv]
          _ = _ := by rw [show B.eval x-F x = -(F x-B.eval x) by ring, E.error x xv]; ring
      calc
        _ = (k*τ)*(A.eval x*P.eval x)*(H.eval x*N.eval x*B.eval x-1) := by
          simp only [Gₗ,G,T,eval_mul,eval_sub,eval_C]
          ring
        _ = _ := by rw [delta,leftShape]; cases keep <;> simp [k,stopL] <;> ring
    have evalR (x : K) : Gᵣ.eval x =
        (A.eval x*H.eval x)*
          (((τ*(-1:K)^R.length)*P.eval x*(cutProduct R).eval x)*
            (((poleProduct right).eval x)^2*(stopR x*B.eval x))) := by
      simp only [Gᵣ,G,T,eval_mul,eval_C]
      rw [rightShape]
      cases keep <;> simp [k,stopR] <;> ring
    have Lpos (i : Fin 19) (pi : P.eval (intervalPoint l t i)≠0)
        (ci : (cutProduct left).eval (intervalPoint l t i)≠0) :
        0 < Gₗ.eval (intervalPoint l t i) := by
      let x := intervalPoint l t i
      have xt : x<t := (intervalPoint_mem lt i).2
      have xv := xt.trans_le tv
      have st : 0<stopL x := by cases keep <;> simp [stopL,xt]
      change 0 < Gₗ.eval x
      rw [evalL x xt]
      exact mul_pos (mul_pos (positiveLeft i) (sep.fitLeft i pi))
        (mul_pos (mul_pos
          (poleProduct_pos D x (fun a ha=>xv.trans_le (dp a ha)))
          (poleProduct_pos ps x (fun a ha=>xv.trans_le (pp a ha))))
          (mul_pos (sq_pos_of_ne_zero ci) (mul_pos st (E.rest.positive x xv))))
    have Lnonneg (i : Fin 19) : 0 ≤ Gₗ.eval (intervalPoint l t i) := by
      let x := intervalPoint l t i
      have xt : x<t := (intervalPoint_mem lt i).2
      change 0 ≤ Gₗ.eval x
      by_cases pn' : P.eval x=0
      · rw [evalL x xt]
        simp [pn']
      by_cases cn' : (cutProduct left).eval x=0
      · rw [evalL x xt]
        simp [cn']
      exact (Lpos i pn' cn').le
    have survivor : (P*cutProduct left).natDegree<19 :=
      (natDegree_mul_le_of_le (le_refl _) (cutProduct_degree left)).trans_lt survive
    obtain ⟨i,live⟩ := exists_nonzero_grid_sample lt
      (mul_ne_zero pn (cutProduct_ne_zero left)) survivor
    have Lint : 0 < integral l t Gₗ := integral_pos_of_grid_samples lt gdL Lnonneg
      ⟨i,Lpos i (fun h=>live (by simp [eval_mul,h])) (fun h=>live (by simp [eval_mul,h]))⟩
    have Rint : 0 ≤ integral t r Gᵣ := by
      rw [interval_exact t r Gᵣ gdR]
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (intervalWeight_pos tr j).le
      let x := intervalPoint t r j
      have xi : x ∈ Set.Ioo t r := intervalPoint_mem tr j
      have st : 0<stopR x := by cases keep <;> simp [stopR,xi.1]
      have fit : 0 ≤ (τ*(-1:K)^R.length)*P.eval x*(cutProduct R).eval x := by
        by_cases h : P.eval x=0
        · simp [h]
        · exact (sep.fitRight j h).le
      change 0 ≤ Gᵣ.eval x
      rw [evalR x]
      exact mul_nonneg (mul_nonneg (nonnegativeRight j)
          (poleProduct_pos D x (fun a ha => xi.2.trans_le (polesRight a ha))).le)
        (mul_nonneg fit (mul_nonneg (sq_nonneg _) (mul_nonneg st.le (E.nonneg x (pg j)))))
    have spl : integral l t G+integral t r G=integral l r G := by
      simp only [integral_apply]
      ring
    have join : integral l t Gₗ+integral t r Gᵣ = (k*τ)*integral l r G := by
      simp only [Gₗ,Gᵣ,← smul_eq_C_mul,map_smul,map_sub,localZero,sub_zero,smul_eq_mul]
      rw [← mul_add,spl]
    have signIntegral : 0<(k*τ)*integral l r G :=
      join ▸ add_pos_of_pos_of_nonneg Lint Rint
    have value : integral l r G = S + (if keep then J₀ else 0) := by
      change integral l r (A*poleProduct D*P*T)=_
      rw [law T (td.trans paid), atomSum_congr leftValue, atomSum_zero_of rightValue,
        add_zero,stopValue]
      cases keep <;> simp [S,J₀]
    simpa only [value,k] using signIntegral
  have lower : 0 < -(τ*S) := by simpa [neg_mul] using both false
  exact ⟨neg_pos.mp lower, by simpa using both true⟩

end
end RKCert.ReviewedNative.FiniteStoppedBracket
