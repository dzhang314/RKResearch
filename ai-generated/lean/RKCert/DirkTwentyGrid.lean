module
public import RKCert.DirkTwentyOrigin
public import RKCert.DirkQuinticPhysical
public import RKCert.DirkQuinticFixed10
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.Endpoint RKCert.FixedFactor RKCert.DirkQuintic
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section
set_option maxHeartbeats 2500000

def endpointDensity:K[X]:=(intHorner der10).map (Int.castRingHom K)

omit [CharZero K] in
theorem endpointDensity_degree:(endpointDensity (K:=K)).natDegree≤9:=
  natDegree_map_le.trans (degree_horner_le der10 9 (by decide))

/-- Exact endpoint-difference functional on monomials of degree at most
ten for the fixed derivative, including the zero constant moment. -/
theorem endpointDensity_moments (j:Fin 11):
    (formalPrimitive (X^j.val*endpointDensity (K:=K))).eval 1=(1:K)^j.val-(0:K)^j.val:=by
  rw [primitive_eval_power_mul _ _ _ endpointDensity_degree]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,endpointDensity,der10,coeff_map,coeff_horner,readCoeff]

/-- Original endpoint difference minus the genuine weighted derivative
annihilates E10, so it is a true one-mark grade-nine column. -/
theorem twenty_endpoint_difference (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28):
    Pi.single (Fin.last s) (1:K)-Pi.single (0:Fin (s+1)) (1:K)-weightedEval (nodes A) b endpointDensity
      ∈marked A 20 9:=by
  obtain ⟨h,org,clean⟩:=twenty_origin ha ho size
  obtain ⟨_,ct,_⟩:=twenty_final_row ha ho size h
  have c0:nodes A 0=0:=by simp [nodes,org]
  let δ:Vec K (s+1):=Pi.single (Fin.last s) (1:K)-Pi.single (0:Fin (s+1)) (1:K)
  let B:=weightedEval (nodes A) b endpointDensity
  have action(v:Vec K (s+1)):row (δ-B) v=v (Fin.last s)-v 0-row B v:=by
    rw [row_sub_col,show δ=Pi.single (Fin.last s) (1:K)-Pi.single (0:Fin (s+1)) (1:K) from rfl,row_sub_col,row_single_left,row_single_left]
  have pure(f:Vec K (s+1))(hf:f∈zeroSpace A 10):row (δ-B) f=0:=by
    rw [action,clean f hf,show f 0=0 from zeroSpace_first_of_row org 10 hf,sub_self,zero_sub,neg_eq_zero]
    have paid:=weights_mul_zeroSpace ho (j:=10) (by decide) hf
    have P:evalNodes A endpointDensity∈treeSpace A 9:=evalNodes_mem_treeSpace _ _ endpointDensity_degree
    have zero:row (b*f) (evalNodes A endpointDensity)=0:=mem_annih.mp paid _ P
    rw [row_apply] at zero ⊢
    convert zero using 1;apply Finset.sum_congr rfl; intro i _
    simp only [B,weightedEval_apply,Pi.mul_apply,evalNodes_apply];ring
  have bush(j:Fin 11):row (δ-B) (normTree A (Tree.bush j.val))=0:=by
    have eval:row B (normTree A (Tree.bush j.val))=probe A b j.val (evalNodes A endpointDensity):=by
      simp only [row_apply,B,weightedEval_apply,normTree_bush,probe,evalNodes_apply]
      apply Finset.sum_congr rfl;intro i _;ring
    have p0:=(OrdinaryTrace.scalar A endpointDensity_degree).probe ho j.val (by have:=j.isLt;omega)
    rw [action,eval,p0,endpointDensity_moments j,normTree_bush]
    change (nodes A (Fin.last s))^j.val-(nodes A 0)^j.val-_ =0
    rw [ct,c0,sub_self]
  change δ-B∈annih (treeSpace A 10)
  rw [mem_annih]
  intro u hu
  rw [h.full] at hu
  obtain ⟨_,⟨a,rfl⟩,v,hv,rfl⟩:=Submodule.mem_sup.mp hu
  rw [map_add,pure v hv,add_zero,polyEval_apply,map_sum]
  apply Finset.sum_eq_zero
  intro k _;rw [map_smul,bush k,smul_zero]

theorem twenty_clean_grid (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (i:Fin (s+1)) (bi:b i≠0) (ti:tau A b i=0):((X-1)*lobatto (K:=K) 10).eval (mirror A i)=0:=by
  obtain ⟨h,org,_⟩:=twenty_origin ha ho size
  have D:=twenty_paid_reverse ha ho size h
  have clean:=twenty_endpoint_difference ha ho size
  rw [h.words 9 (by decide) (by decide)] at clean
  obtain ⟨Q,_,eqn⟩:=D.word_polynomial ha ho (D.nonlocal_cubic ha ho) (r:=7) (by decide) (by decide) clean
  obtain ⟨_,ct,_⟩:=twenty_final_row ha ho size h
  apply lobatto_grid_reflect_zero
  by_cases endp:i=Fin.last s
  · simp [endp,ct]
  by_cases origin:i=0
  · have c0:nodes A 0=0:=by simp [nodes,org]
    simp [origin,c0,lobatto]
  have e:=eqn i
  simp only [Pi.sub_apply,Pi.single_eq_of_ne endp,Pi.single_eq_of_ne origin,sub_self,zero_sub,weightedEval_apply,ti,mul_zero,neg_eq_zero] at e
  have nil:(endpointDensity (K:=K)).eval (nodes A i)=0:=(mul_eq_zero.mp e).resolve_right bi
  change ((intHorner der10).map (Int.castRingHom K)).eval (nodes A i)=0 at nil
  simp [lobatto,native_der10,nil]
end
end RKCert.Paired.Terminal

