module
public import RKCert.DirkClockRetractionOps
@[expose] public section
namespace RKCert.Paired.PivotProjection
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] {s:ℕ}

theorem interpolate_fiber (c z:Vec K s) (ag:∀i j,c i=c j→z i=z j) :
    ∃Q:K[X],∀i,Q.eval (c i)=z i:=by
  let f (x:K):K:=if h:∃i,c i=x then z (Classical.choose h) else 0
  refine ⟨Lagrange.interpolate (Clock.sites c) id f,fun i=>?_⟩
  have ev:=Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (Clock.site_mem c i)
  simp only [id_eq] at ev
  rw [ev]
  have hx:∃j,c j=c i:=⟨i,rfl⟩
  change f (c i)=z i
  dsimp only [f]
  rw [dite_eq_left hx]
  exact ag _ _ (Classical.choose_spec hx)

/-- A single chronological retraction can respect two simultaneous diagonal
signals. The proof separates the finite joint fibers using a generic linear
combination, and uses the existing one-clock construction and Mathlib's
Lagrange interpolation rather than a second elimination algorithm. -/
theorem exists_joint_retraction [Infinite K] (c v:Vec K s) (U:Submodule K (Vec K s))
    (ic:U.map (diag c)≤U) (iv:U.map (diag v)≤U) :
    ∃P:ClockRetraction c U,∀x,P.projection (diag v x)=diag v (P.projection x):=by
  let bad:Finset K:=(Finset.univ:Finset (Fin s×Fin s)).image (fun p=>
    (c p.2-c p.1)/(v p.1-v p.2))
  obtain ⟨a,ha⟩:=bad.exists_notMem
  let d:Vec K s:=fun i=>c i+a*v i
  have same(i j:Fin s)(h:d i=d j): c i=c j ∧ v i=v j:=by
    have vv:v i=v j:=by
      by_contra vn
      have dn:v i-v j≠0:=sub_ne_zero.mpr vn
      have e:a=(c j-c i)/(v i-v j):=(eq_div_iff dn).mpr (by
        change c i+a*v i=c j+a*v j at h
        linear_combination h)
      exact ha (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,e.symm⟩)
    exact ⟨by simpa only [d,vv,add_left_inj] using h,vv⟩
  have dd:U.map (diag d)≤U:=by
    rintro _ ⟨x,hx,rfl⟩
    have e:diag d x=diag c x+a • diag v x:=by
      ext i
      simp only [diag_apply,d,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [e]
    exact U.add_mem (ic ⟨_,hx,rfl⟩) (U.smul_mem a (iv ⟨_,hx,rfl⟩))
  obtain ⟨P⟩:=exists_clock_retraction d U dd
  obtain ⟨H,hH⟩:=interpolate_fiber d c (fun i j e=>(same i j e).1)
  obtain ⟨J,hJ⟩:=interpolate_fiber d v (fun i j e=>(same i j e).2)
  have comm (z:Vec K s) (Q:K[X]) (fit:∀i,Q.eval (d i)=z i) (x:Vec K s) :
      P.projection (diag z x)=diag z (P.projection x):=by
    have e(y:Vec K s):diag z y=weightedEval d y Q:=by ext i;simp only [diag_apply,weightedEval_apply,fit]
    rw [e,P.weighted,←e]
  refine ⟨⟨P.projection,P.diagonal,P.causal,P.kills,P.defect,comm c H hH,?_⟩,comm v J hJ⟩
  intro x Q
  have e(y:Vec K s):weightedEval c y Q=weightedEval d y (Q.comp H):=by
    ext i;simp only [weightedEval_apply,eval_comp,hH]
  rw [e,P.weighted,←e]

namespace ClockRetraction
variable {c:Vec K s} {U:Submodule K (Vec K s)} (P:ClockRetraction c U)

theorem fiber (a:K) (x:Vec K s):
    P.projection (Clock.fiber c a x)=Clock.fiber c a (P.projection x):=by
  let y:Vec K s:=fun i=>if c i=a then 1 else 0
  obtain ⟨H,h⟩:=interpolate_fiber c y (fun i j eq=>by simp only [y,eq])
  have e(u:Vec K s):Clock.fiber c a u=weightedEval c u H:=by
    ext i
    simp only [Clock.fiber,weightedEval_apply,h,y]
    split <;> simp
  rw [e,P.weighted,←e]

theorem clock_pow (k:ℕ) (x:Vec K s):
    P.projection ((diag c^k) x)=(diag c^k) (P.projection x):=by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,P.clock,ih]

theorem head_sites (w:Vec K s)
    (normal:∀a,Clock.fiber c a w∈U→Clock.fiber c a w=0) :
    Clock.headSites c w⊆Clock.headSites c (P.projection w):=by
  intro a ha
  obtain ⟨i,hi,eq⟩:=Finset.mem_image.mp ha
  have inz:w i≠0:=(Finset.mem_filter.mp hi).2
  by_contra hn
  have hz:Clock.fiber c a (P.projection w)=0:=by
    ext j
    by_cases same:c j=a
    · rw [Clock.fiber,ite_eq_left same]
      exact not_not.mp (fun nz=>hn (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nz⟩,same⟩))
    · simp [Clock.fiber,same]
  have he:=P.defect (Clock.fiber c a w)
  rw [P.fiber,hz,sub_zero] at he
  have q:=congrFun (normal a he) i
  exact inz (by simpa [Clock.fiber,eq] using q)
end ClockRetraction
end
end RKCert.Paired.PivotProjection
