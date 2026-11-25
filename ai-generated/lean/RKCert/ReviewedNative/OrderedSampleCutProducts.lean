module

public import RKCert.ReviewedNative.OrderedRightPoleInterpolation
public import RKCert.ReviewedNative.OrderedAlternationDegree

@[expose] public section

/-! # A split sign-cut product on one ordered sample list

A single signed product fits both sides of the pivot. Each cut is
chosen inside its actual adjacent-sample gap and off the pivot; no
root existence for the sampled polynomial is required. -/
namespace RKCert.ReviewedNative.OrderedSampleCuts

open Polynomial RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.RightPoleInterpolation SignType
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def cutValue (e : K) (L R : List K) (x : K) : K :=
  e*(cutProduct L).eval x*(cutProduct R).eval x

structure SplitCuts (P : K[X]) (u : K) (xs : List K) (L R : List K) (e : K) : Prop where
  lower : ∀ x∈L, 0<x ∧ x<u
  upper : ∀ x∈R, u<x ∧ x<1
  cost : L.length+R.length≤variation P xs
  fit : ∀ x∈xs, P.eval x≠0 → 0 < P.eval x*cutValue e L R x

private theorem point_between_away (x y u : K) (xy : x<y) :
    ∃ z, x<z ∧ z<y ∧ z≠u := by
  let a := (x+y)/2
  have xa : x<a := left_lt_add_div_two.mpr xy
  have ay : a<y := add_div_two_lt_right.mpr xy
  by_cases e : a=u
  · let b := (x+a)/2
    have xb : x<b := left_lt_add_div_two.mpr xa
    have ba : b<a := add_div_two_lt_right.mpr xa
    exact ⟨b,xb,ba.trans ay,ne_of_lt (e ▸ ba)⟩
  · exact ⟨a,xa,ay,e⟩

private theorem same_sign_keep {a b z : K} (same : sign a=sign b) (pos : 0<b*z) :
    0<a*z := by
  rcases mul_pos_iff.mp pos with ⟨bp,zp⟩ | ⟨bn,zn⟩
  · exact mul_pos (sign_eq_one_iff.mp (same.trans (sign_pos bp))) zp
  · exact mul_pos_of_neg_of_neg (sign_eq_neg_one_iff.mp (same.trans (sign_neg bn))) zn

private theorem opposite_sign_flip {a b z : K} (an : a≠0)
    (di : sign a≠sign b) (pos : 0<b*z) : a*z<0 := by
  rcases mul_pos_iff.mp pos with ⟨bp,zp⟩ | ⟨bn,zn⟩ <;>
    rcases lt_or_gt_of_ne an with ap | ap
  · exact mul_neg_of_neg_of_pos ap zp
  · exact (di ((sign_pos ap).trans (sign_pos bp).symm)).elim
  · exact (di ((sign_neg ap).trans (sign_neg bn).symm)).elim
  · exact mul_neg_of_pos_of_neg ap zn

private theorem cuts_nonzero (P : K[X]) (u x : K) (xs : List K)
    (inc : (x::xs).Pairwise (· < ·))
    (inside : ∀ z∈x::xs, 0<z ∧ z<1)
    (live : ∀ z∈x::xs, P.eval z≠0) :
    ∃ L R e, SplitCuts P u (x::xs) L R e ∧
      ∀ z≤x, 0<P.eval x*cutValue e L R z := by
  induction xs generalizing x with
  | nil =>
      have xn := live x (by simp)
      have pos (z : K) : 0<P.eval x*cutValue (P.eval x) [] [] z := by
        simpa only [cutValue,cutProduct_nil,eval_one,mul_one,pow_two] using sq_pos_of_ne_zero xn
      refine ⟨[],[],P.eval x,⟨by simp,by simp,by simp,?_⟩,fun z _=>pos z⟩
      intro z h _
      have eq : z=x := by simpa using h
      rw [eq]
      exact pos x
  | cons y ys ih =>
      have xy : x<y := (List.pairwise_cons.mp inc).1 y (by simp)
      obtain ⟨L,R,e,D,before⟩ := ih y (List.pairwise_cons.mp inc).2
        (fun z hz=>inside z (List.mem_cons_of_mem _ hz))
        (fun z hz=>live z (List.mem_cons_of_mem _ hz))
      have xn := live x (by simp)
      have yn := live y (by simp)
      have cost : variation P (x::y::ys)=variation P (y::ys)+
          (if sign (P.eval x)=sign (P.eval y) then 0 else 1) := by
        simpa only [variation,List.map_cons] using
          (List.signVariations_cons_cons_of_ne_zero (ys.map P.eval) xn yn)
      classical
      by_cases same : sign (P.eval x)=sign (P.eval y)
      · have b (z : K) (zx : z≤x) : 0<P.eval x*cutValue e L R z :=
          same_sign_keep same (before z (zx.trans xy.le))
        refine ⟨L,R,e,⟨D.lower,D.upper,?_,?_⟩,b⟩
        · rw [cost,if_pos same,add_zero]
          exact D.cost
        · intro z hz nz
          rcases List.mem_cons.mp hz with rfl|inTail
          · exact b z le_rfl
          · exact D.fit z inTail nz
      obtain ⟨a,xa,ay,au⟩ := point_between_away x y u xy
      let L' := if a<u then a::L else L
      let R' := if a<u then R else a::R
      have value (z : K) : cutValue e L' R' z=cutValue e L R z*(z-a) := by
        by_cases h : a<u
        · simp only [L',R',h,if_true,cutValue,cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
          ring
        · simp only [L',R',h,if_false,cutValue,cutProduct_cons,eval_mul,eval_sub,eval_X,eval_C]
          ring
      have b (z : K) (zx : z≤x) : 0<P.eval x*cutValue e L' R' z := by
        rw [value,←mul_assoc]
        exact mul_pos_of_neg_of_neg (opposite_sign_flip xn same (before z (zx.trans xy.le)))
          (sub_neg.mpr (zx.trans_lt xa))
      refine ⟨L',R',e,⟨?_,?_,?_,?_⟩,b⟩
      · intro z hz
        by_cases h : a<u
        · have j : z∈a::L := by simpa only [L',h,if_true] using hz
          rcases List.mem_cons.mp j with rfl|mem
          · exact ⟨(inside x (by simp)).1.trans xa,h⟩
          · exact D.lower z mem
        · exact D.lower z (by simpa only [L',h,if_false] using hz)
      · intro z hz
        by_cases h : a<u
        · exact D.upper z (by simpa only [R',h,if_true] using hz)
        · have j : z∈a::R := by simpa only [R',h,if_false] using hz
          rcases List.mem_cons.mp j with rfl|mem
          · exact ⟨lt_of_le_of_ne (le_of_not_gt h) au.symm,ay.trans (inside y (by simp)).2⟩
          · exact D.upper z mem
      · rw [cost,if_neg same]
        have d := D.cost
        by_cases h : a<u <;> simp only [L',R',h,if_true,if_false,List.length_cons] <;> omega
      · intro z hz nz
        rcases List.mem_cons.mp hz with rfl | inTail
        · exact b z le_rfl
        · have yz : y≤z := by
            rcases List.mem_cons.mp inTail with rfl|mem
            · exact le_rfl
            · exact ((List.pairwise_cons.mp (List.pairwise_cons.mp inc).2).1 _ mem).le
          rw [value,←mul_assoc]
          exact mul_pos (D.fit z inTail nz) (sub_pos.mpr (ay.trans_le yz))

/-- Construct one sign-fit product on all nonzero samples, even if some
of the original grid values are zero. -/
theorem exists_split_cuts (P : K[X]) (u : K) (xs : List K)
    (inc : xs.Pairwise (· < ·)) (inside : ∀ z∈xs, 0<z ∧ z<1) :
    ∃ L R e, SplitCuts P u xs L R e := by
  classical
  let nz := xs.filter (fun z=>!decide (P.eval z=0))
  have nzInc : nz.Pairwise (· < ·) := inc.filter _
  have live (z : K) (hz : z∈nz) : P.eval z≠0 := by
    simpa using (List.mem_filter.mp hz).2
  have nzIn (z : K) (hz : z∈nz) : 0<z ∧ z<1 := inside z (List.mem_filter.mp hz).1
  have on (z : K) (hz : z∈xs) (hn : P.eval z≠0) : z∈nz :=
    List.mem_filter.mpr ⟨hz,by simp [hn]⟩
  have cost : variation P nz=variation P xs := by
    change (nz.map P.eval).signVariations=(xs.map P.eval).signVariations
    have e : nz.map P.eval=(xs.map P.eval).filter (fun z=>!decide (z=0)) := by
      simp only [nz,List.filter_map,Function.comp_def]
    rw [e,List.signVariations_filter_ne_zero]
  cases eq : nz with
  | nil =>
      refine ⟨[],[],1,⟨by simp,by simp,by simp,?_⟩⟩
      intro z hz zn
      have q := on z hz zn
      rw [eq] at q
      exact (List.not_mem_nil q).elim
  | cons x more =>
      obtain ⟨L,R,e,D,_⟩ := cuts_nonzero P u x more
        (by simpa only [eq] using nzInc)
        (fun z hz=>nzIn z (eq.symm ▸ hz))
        (fun z hz=>live z (eq.symm ▸ hz))
      refine ⟨L,R,e,D.lower,D.upper,?_,?_⟩
      · exact D.cost.trans_eq ((congrArg (variation P) eq).symm.trans cost)
      · intro z hz zn
        exact D.fit z (eq ▸ on z hz zn) zn

end
end RKCert.ReviewedNative.OrderedSampleCuts
