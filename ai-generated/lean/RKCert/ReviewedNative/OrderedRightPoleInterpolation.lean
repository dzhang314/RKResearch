module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Ordered right-pole interpolation without a real closure

For a positive expression made from reciprocals of right-hand poles,
the next divided difference is again such an expression. Successive
interpolation then gives a positive Newton remainder and positive
extrapolation to the right of every interpolation node. -/
namespace RKCert.ReviewedNative.RightPoleInterpolation

open Polynomial
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

inductive RightPoleFun (u : K) : (K → K) → Prop
  | pole (r : K) (hr : u≤r) : RightPoleFun u (fun x => (r-x)⁻¹)
  | scale (c : K) (hc : 0<c) (f : K → K) (hf : RightPoleFun u f) :
      RightPoleFun u (fun x => c*f x)
  | plus (f g : K → K) (hf : RightPoleFun u f) (hg : RightPoleFun u g) :
      RightPoleFun u (fun x => f x+g x)
  | times (f g : K → K) (hf : RightPoleFun u f) (hg : RightPoleFun u g) :
      RightPoleFun u (fun x => f x*g x)

theorem RightPoleFun.positive {u : K} {f : K → K} (F : RightPoleFun u f) :
    ∀ x<u, 0<f x := by
  induction F with
  | pole r hr => exact fun x hx => inv_pos.mpr (sub_pos.mpr (hx.trans_le hr))
  | scale c hc f hf ih => exact fun x hx => mul_pos hc (ih x hx)
  | plus f g hf hg ifp igp => exact fun x hx => add_pos (ifp x hx) (igp x hx)
  | times f g hf hg ifp igp => exact fun x hx => mul_pos (ifp x hx) (igp x hx)

theorem RightPoleFun.divided_step {u a : K} {f : K → K} (F : RightPoleFun u f) (au : a<u) :
    ∃ g, RightPoleFun u g ∧ ∀ x<u, f x=f a+(x-a)*g x := by
  induction F with
  | pole r hr =>
      have ar : 0<r-a := sub_pos.mpr (au.trans_le hr)
      let p : K → K := fun x => (r-x)⁻¹
      refine ⟨fun x => (r-a)⁻¹*p x,
        RightPoleFun.scale _ (inv_pos.mpr ar) p (RightPoleFun.pole r hr),?_⟩
      intro x xu
      have xr : 0<r-x := sub_pos.mpr (xu.trans_le hr)
      dsimp only [p]
      field_simp [ar.ne',xr.ne']
      <;> ring
  | scale c hc f hf ih =>
      obtain ⟨g,hg,eq⟩ := ih
      refine ⟨fun x => c*g x,RightPoleFun.scale c hc g hg,?_⟩
      intro x xu
      change c*f x = c*f a+(x-a)*(c*g x)
      rw [eq x xu]
      ring
  | plus f g hf hg ifp igp =>
      obtain ⟨v,hv,ev⟩ := ifp
      obtain ⟨w,hw,ew⟩ := igp
      refine ⟨fun x => v x+w x,RightPoleFun.plus v w hv hw,?_⟩
      intro x xu
      change f x+g x=f a+g a+(x-a)*(v x+w x)
      rw [ev x xu,ew x xu]
      ring
  | times f g hf hg ifp igp =>
      obtain ⟨v,hv,ev⟩ := ifp
      obtain ⟨w,hw,ew⟩ := igp
      refine ⟨fun x => v x*g x+f a*w x,
        RightPoleFun.plus _ _ (RightPoleFun.times v g hv hg)
          (RightPoleFun.scale _ (hf.positive a au) w hw),?_⟩
      intro x xu
      change f x*g x=f a*g a+(x-a)*(v x*g x+f a*w x)
      rw [ev x xu,ew x xu]
      ring

def cutProduct (xs : List K) : K[X] :=
  (xs.map (fun x => X-C x)).prod

@[simp] theorem cutProduct_nil : cutProduct ([] : List K)=1 := rfl

@[simp] theorem cutProduct_cons (a : K) (xs : List K) :
    cutProduct (a::xs)=(X-C a)*cutProduct xs := rfl

theorem cutProduct_degree (xs : List K) : (cutProduct xs).natDegree≤xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [cutProduct_cons]
      have d := natDegree_mul_le_of_le (natDegree_X_sub_C a).le ih
      change _ ≤ xs.length+1
      exact d.trans_eq (Nat.add_comm 1 xs.length)

/-- This construction does not need distinct nodes. Distinct nodes
coming from a sign separator are useful for the receiving application. -/
structure InterpolatesRightPole (u : K) (f : K → K) (xs : List K)
    (H : K[X]) (g : K → K) : Prop where
  rest : RightPoleFun u g
  degree : H.natDegree≤xs.length-1
  empty : xs=[] → H=0
  nonneg : ∀ x,u<x → 0≤H.eval x
  positive : xs≠[] → ∀ x,u<x → 0<H.eval x
  error : ∀ x<u, f x-H.eval x=(cutProduct xs).eval x*g x

theorem RightPoleFun.interpolant {u : K} {f : K → K}
    (F : RightPoleFun u f) (xs : List K) (paid : ∀ x∈xs,x<u) :
    ∃ H g, InterpolatesRightPole u f xs H g := by
  induction xs generalizing f with
  | nil =>
      refine ⟨0,f,F,by simp,fun _=>rfl,by simp,fun n=>False.elim (n rfl),?_⟩
      intro x _
      simp
  | cons a xs ih =>
      have au := paid a (by simp)
      obtain ⟨h,hh,delta⟩ := F.divided_step au
      obtain ⟨J,g,E⟩ := ih hh (fun x hx=>paid x (List.mem_cons_of_mem _ hx))
      let H := C (f a)+(X-C a)*J
      have cap : H.natDegree≤(a::xs).length-1 := by
        by_cases zero : xs=[]
        · simp [H,zero,E.empty zero]
        have lo : 0<xs.length := List.length_pos_iff.mpr zero
        dsimp only [H]
        apply (natDegree_add_le _ _).trans
        rw [natDegree_C,zero_max]
        have h := natDegree_mul_le_of_le (natDegree_X_sub_C a).le E.degree
        simp only [List.length_cons]
        omega
      have pos (x : K) (ux : u<x) : 0<H.eval x := by
        simp only [H,eval_add,eval_C,eval_mul,eval_sub,eval_X]
        exact add_pos_of_pos_of_nonneg (F.positive a au)
          (mul_nonneg (sub_pos.mpr (au.trans ux)).le (E.nonneg x ux))
      refine ⟨H,g,E.rest,cap,by simp,fun x xu=>(pos x xu).le,fun _=>pos,?_⟩
      intro x xu
      simp only [H,eval_add,eval_C,eval_mul,eval_sub,eval_X,cutProduct_cons]
      rw [delta x xu]
      linear_combination (x-a)*(E.error x xu)

/-- Adding any finite list of eligible poles preserves the same
positive-function class, including when the list is empty. -/
theorem RightPoleFun.mul_pole_list {u : K} {f : K → K} (F : RightPoleFun u f)
    (ds : List K) (right : ∀ d∈ds,u≤d) :
    RightPoleFun u (fun x => f x*(ds.map (fun d => (d-x)⁻¹)).prod) := by
  induction ds with
  | nil => simpa only [List.map_nil,List.prod_nil,mul_one] using F
  | cons d ds ih =>
      have h := ih (fun z hz=>right z (List.mem_cons_of_mem _ hz))
      have p : RightPoleFun u (fun x => (d-x)⁻¹) := RightPoleFun.pole d (right d (by simp))
      have q := RightPoleFun.times _ _ p h
      change RightPoleFun u (fun x=>f x*((d-x)⁻¹*(ds.map (fun z=>(z-x)⁻¹)).prod))
      simpa only [mul_left_comm] using q

end
end RKCert.ReviewedNative.RightPoleInterpolation
