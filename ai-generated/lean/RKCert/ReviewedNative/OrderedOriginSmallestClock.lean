module

public import RKCert.ReviewedNative.OrderedOriginMirroredChronology
public import RKCert.ReviewedNative.OrderedSampleCutProducts

@[expose] public section

/-! # No smallest first clock, using two finite ordered grids

A split sign-cut product replaces factoring P into ordered roots. A
positive right-pole interpolant produces the degree-six global tester.
The receiving cut uses no ordered-field extension and only the first
local moment of the three-clock packet. -/
namespace RKCert.ReviewedNative.OriginSignedSquares

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.RightPoleInterpolation
open RKCert.ReviewedNative.OrderedSampleCuts
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem cutProduct_above (xs : List K) (x : K) (above : ∀a∈xs,a<x) :
    0<(cutProduct xs).eval x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
      exact mul_pos (sub_pos.mpr (above a (by simp)))
        (ih (fun a ha=>above a (List.mem_cons_of_mem _ ha)))

private theorem cutProduct_below (xs : List K) (x : K) (below : ∀a∈xs,x<a) :
    0<(-1:K)^xs.length*(cutProduct xs).eval x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have rest := ih (fun z hz=>below z (List.mem_cons_of_mem _ hz))
      have eq : (-1:K)^(a::xs).length*(cutProduct (a::xs)).eval x =
          (a-x)*((-1:K)^xs.length*(cutProduct xs).eval x) := by
        simp only [List.length_cons,pow_succ,cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
        ring
      rw [eq]
      exact mul_pos (sub_pos.mpr (below a (by simp))) rest

private theorem inverse_product (xs : List K) (x : K) (below : ∀a∈xs,x<a) :
    (xs.map (fun a=>(a-x)⁻¹)).prod*((-1:K)^xs.length*(cutProduct xs).eval x)=1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have arc : a-x≠0 := (sub_pos.mpr (below a (by simp))).ne'
      have rest := ih (fun z hz=>below z (List.mem_cons_of_mem _ hz))
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,cutProduct_cons,
        eval_mul,eval_sub,eval_X,eval_C]
      calc
        _ = ((a-x)⁻¹*(a-x))*
            ((xs.map (fun d=>(d-x)⁻¹)).prod*((-1:K)^xs.length*(cutProduct xs).eval x)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ arc,rest,mul_one]

set_option maxRecDepth 4500
set_option maxHeartbeats 1700000

theorem noSmallestClock_of_pole_sign_cuts : NoSmallestClock K := by
  intro P u v w B u0 u1 uv uw
  let SL := gridSamples (0:K) u
  let SR := gridSamples u 1
  have li (x : K) (hx : x∈SL) : x∈Set.Ioo (0:K) u := gridSamples_inside u0 x hx
  have ri (x : K) (hx : x∈SR) : x∈Set.Ioo u 1 := gridSamples_inside u1 x hx
  have inc : (SL++SR).Pairwise (· < ·) := List.pairwise_append.mpr
    ⟨gridSamples_increasing u0,gridSamples_increasing u1,
      fun x hx y hy => (li x hx).2.trans (ri y hy).1⟩
  have inAll (x : K) (hx : x∈SL++SR) : 0<x ∧ x<1 := by
    rcases List.mem_append.mp hx with l|r
    · exact ⟨(li x l).1,(li x l).2.trans u1⟩
    · exact ⟨u0.trans (ri x r).1,(ri x r).2⟩
  obtain ⟨L,R,e,D⟩ := exists_split_cuts P u (SL++SR) inc inAll
  have counts : L.length+R.length≤5 :=
    D.cost.trans ((variation_le_natDegree P _ inc).trans B.degree)
  let PL := cutProduct L
  let PR := cutProduct R
  let M : K[X] := (X-C v)*(X-C w)
  let σ : K := (-1)^R.length
  let γ : K := e*σ
  have ss : σ*σ=1 := by dsimp only [σ]; rw [←mul_pow]; norm_num
  let base (x : K) := (u-x)⁻¹*(1-x)⁻¹*((v-x)⁻¹)^2*((w-x)⁻¹)^2
  have fu : RightPoleFun u (fun x=>(u-x)⁻¹) := RightPoleFun.pole u le_rfl
  have f1 : RightPoleFun u (fun x=>(1-x)⁻¹) := RightPoleFun.pole 1 u1.le
  have fv : RightPoleFun u (fun x=>(v-x)⁻¹) := RightPoleFun.pole v uv.le
  have fw : RightPoleFun u (fun x=>(w-x)⁻¹) := RightPoleFun.pole w uw.le
  have fbase : RightPoleFun u base := by
    simpa only [base,pow_two] using
      (RightPoleFun.times _ _ (RightPoleFun.times _ _
        (RightPoleFun.times _ _ fu f1) (RightPoleFun.times _ _ fv fv))
        (RightPoleFun.times _ _ fw fw))
  let g (x : K) := base x*(R.map (fun a=>(a-x)⁻¹)).prod
  have gP : RightPoleFun u g := fbase.mul_pole_list R (fun a ha=>(D.upper a ha).1.le)
  obtain ⟨J,h,W⟩ := gP.interpolant L (fun a ha=>(D.lower a ha).2)
  let S : K[X] := (C u-X)*(1-X)*M^2*(C σ*PR)
  have gS (x : K) (xu : x<u) : g x*S.eval x=1 := by
    have ru := inverse_product R x (fun a ha=>xu.trans (D.upper a ha).1)
    have inv : base x*((u-x)*(1-x)*(M.eval x)^2)=1 := by
      simp only [base,M,eval_mul,eval_sub,eval_X,eval_C]
      field_simp [(sub_pos.mpr xu).ne',(sub_pos.mpr (xu.trans u1)).ne',
        (sub_pos.mpr (xu.trans uv)).ne',(sub_pos.mpr (xu.trans uw)).ne']
      <;> ring
    calc
      _ = (base x*((u-x)*(1-x)*(M.eval x)^2))*
            ((R.map (fun a=>(a-x)⁻¹)).prod*(σ*PR.eval x)) := by
        simp only [g,S,eval_mul,eval_sub,eval_X,eval_C,eval_one,eval_pow]
        ring
      _ = 1 := by rw [inv,ru,one_mul]
  have sp (x : K) (xu : x<u) : 0<S.eval x := by
    apply (mul_pos_iff_of_pos_left (gP.positive x xu)).mp
    rw [gS x xu]
    exact zero_lt_one
  let Z : K[X] := C σ*(PR*M*J)
  have md : M.natDegree≤2 := natDegree_mul_le_of_le
    (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le
  have zd : Z.natDegree≤6 := by
    by_cases empty : L=[]
    · simp [Z,W.empty empty]
    have ll := List.length_pos_iff.mpr empty
    have t := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (cutProduct_degree R) md) W.degree
    apply (natDegree_C_mul_le _ _).trans
    change (cutProduct R*M*J).natDegree≤6
    omega
  let T := X*(1-X)*P*threeHull u v w*Z
  have mesh : integral 0 1 T=0 := B.mesh Z zd
  have Tleft : T=-(X*P*S*J) := by
    dsimp only [T,Z,threeHull,S,M]
    ring
  have Tright : T=C σ*(X*(1-X)*(X-C u)*P*PR*M^2*J) := by
    dsimp only [T,Z,threeHull,M]
    ring
  have td : T.natDegree≤16 := by
    have d1 : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
    have nd : (threeHull u v w).natDegree≤3 := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le)
      (natDegree_X_sub_C _).le
    exact natDegree_mul_le_of_le (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le d1) B.degree) nd) zd
  let TL := C γ*(T+X*P)
  let TR := C γ*T
  have dl : TL.natDegree≤19 := by
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_add_le _ _).trans
    exact max_le (td.trans (by decide))
      ((natDegree_mul_le_of_le natDegree_X.le B.degree).trans (by decide))
  have dr : TR.natDegree≤19 := (natDegree_C_mul_le _ _).trans (td.trans (by decide))
  have fitL (x : K) (inside : x∈SL) (live : P.eval x≠0) :
      0<γ*P.eval x*PL.eval x := by
    have px := (li x inside).2
    have rpos : 0<σ*PR.eval x := cutProduct_below R x
      (fun a ha=>px.trans (D.upper a ha).1)
    apply (mul_pos_iff_of_pos_right rpos).mp
    have eq : (γ*P.eval x*PL.eval x)*(σ*PR.eval x) =
        (σ*σ)*(P.eval x*cutValue e L R x) := by dsimp only [γ,cutValue,PL,PR]; ring
    rw [eq,ss,one_mul]
    exact D.fit x (List.mem_append_left _ inside) live
  have fitR (x : K) (inside : x∈SR) (live : P.eval x≠0) :
      0<e*P.eval x*PR.eval x := by
    have lp : 0<PL.eval x := cutProduct_above L x
      (fun a ha=>(D.lower a ha).2.trans (ri x inside).1)
    apply (mul_pos_iff_of_pos_right lp).mp
    have eq : (e*P.eval x*PR.eval x)*PL.eval x = P.eval x*cutValue e L R x := by
      dsimp only [cutValue,PL,PR]; ring
    rw [eq]
    exact D.fit x (List.mem_append_right _ inside) live
  have leftEval (x : K) (xu : x<u) :
      TL.eval x = (x*S.eval x)*(γ*P.eval x*PL.eval x)*h x := by
    have key : S.eval x*g x=1 := by rw [mul_comm,gS x xu]
    calc
      _ = γ*x*P.eval x*(1-S.eval x*J.eval x) := by
        rw [show TL=C γ*(T+X*P) from rfl,Tleft]
        simp only [eval_mul,eval_add,eval_neg,eval_X,eval_C]
        ring
      _ = γ*x*P.eval x*(S.eval x*(g x-J.eval x)) := by
        simp only [mul_sub,key]
      _ = _ := by rw [W.error x xu]; dsimp only [PL]; ring
  have rightEval (x : K) :
      TR.eval x=x*(1-x)*(x-u)*(M.eval x)^2*J.eval x*(e*P.eval x*PR.eval x) := by
    have eq : γ*σ=e := by dsimp only [γ]; rw [mul_assoc,ss,mul_one]
    rw [show TR=C γ*T from rfl,Tright]
    simp only [eval_mul,eval_sub,eval_X,eval_C,eval_one,eval_pow]
    rw [←mul_assoc,eq]
    ring
  have lMem (i : Fin 19) : intervalPoint 0 u i∈SL :=
    List.mem_ofFn.mpr ⟨i,rfl⟩
  have rMem (i : Fin 19) : intervalPoint u 1 i∈SR :=
    List.mem_ofFn.mpr ⟨i,rfl⟩
  have lPos (x : K) (inL : x∈SL) (live : P.eval x≠0) : 0<TL.eval x := by
    have hx := li x inL
    rw [leftEval x hx.2]
    exact mul_pos (mul_pos (mul_pos hx.1 (sp x hx.2)) (fitL x inL live))
      (W.rest.positive x hx.2)
  obtain ⟨i,live⟩ := exists_nonzero_grid_sample u0 B.live
    (B.degree.trans_lt (by decide))
  have left : 0 < integral 0 u TL := by
    refine integral_pos_of_grid_samples u0 dl ?_ ⟨i,lPos _ (lMem i) live⟩
    intro j
    let x := intervalPoint 0 u j
    by_cases z : P.eval x=0
    · change 0≤TL.eval x
      simp [leftEval x (li x (lMem j)).2,z]
    · exact (lPos x (lMem j) z).le
  have right : 0 ≤ integral u 1 TR := by
    rw [interval_exact u 1 TR dr]
    apply Finset.sum_nonneg
    intro i _
    let x := intervalPoint u 1 i
    have inR : x∈SR := rMem i
    have hx := ri x inR
    have fit : 0≤e*P.eval x*PR.eval x := by
      by_cases z : P.eval x=0
      · simp [z]
      · exact (fitR x inR z).le
    have value : 0≤TR.eval x := by
      rw [rightEval]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (u0.trans hx.1).le (sub_nonneg.mpr hx.2.le))
        (sub_nonneg.mpr hx.1.le)) (sq_nonneg _)) (W.nonneg x hx.1)) fit
    exact mul_nonneg (intervalWeight_pos u1 i).le value
  have addUp : integral 0 u T+integral u 1 T=integral 0 1 T := by
    simp only [integral_apply]
    ring
  have sum : integral 0 u TL+integral u 1 TR=0 := by
    simp only [TL,TR,←smul_eq_C_mul,map_smul,map_add,B.first,add_zero,smul_eq_mul]
    rw [←mul_add,addUp,mesh,mul_zero]
  exact (add_pos_of_pos_of_nonneg left right).ne' sum

end
end RKCert.ReviewedNative.OriginSignedSquares
