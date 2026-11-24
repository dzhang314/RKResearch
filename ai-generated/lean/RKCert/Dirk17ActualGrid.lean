module
public import RKCert.Dirk17Unanchored
public import RKCert.Dirk17RadauQuadrature
public import RKCert.DirkTwentyCleanBudget
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Polynomial RKCert.Endpoint RKCert.Paired.Terminal RKCert.RadauEight
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 4000
/-- The native original terminal cardinal and its endpoint reproducer
differ by an actual full grade-eight mark. -/
theorem unanchored_endpoint (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Unanchored A b):
    Pi.single (Fin.last 22) (1:K)-weightedEval (nodes A) b (density K)∈marked A 17 8:=by
  let B:=weightedEval (nodes A) b (density K)
  let e:Vec K 23:=Pi.single (Fin.last 22) (1:K)
  have action(v:Vec K 23):row (e-B) v=v (Fin.last 22)-row B v:=by rw [row_sub_col,row_single_left]
  have pure(f:Vec K 23)(hf:f∈zeroSpace A 8):row (e-B) f=0:=by
    rw [action,h.clean f hf,zero_sub,neg_eq_zero]
    have paid:=weights_mul_zeroSpace ho (j:=8) (by decide) hf
    have P:evalNodes A (density K)∈treeSpace A 8:=evalNodes_mem_treeSpace _ _ density_degree
    have zero:row (b*f) (evalNodes A (density K))=0:=mem_annih.mp paid _ P
    rw [row_apply] at zero ⊢
    convert zero using 1;apply Finset.sum_congr rfl;intro i _
    simp only [B,weightedEval_apply,Pi.mul_apply,evalNodes_apply];ring
  have bush(j:Fin 9):row (e-B) (normTree A (Tree.bush j.val))=0:=by
    have eqn:row B (normTree A (Tree.bush j.val))=probe A b j.val (evalNodes A (density K)):=by
      simp only [row_apply,B,weightedEval_apply,normTree_bush,probe,evalNodes_apply]
      apply Finset.sum_congr rfl;intro i _;ring
    have val:=(OrdinaryTrace.scalar A density_degree).probe ho j.val (by have:=j.isLt;omega)
    rw [action,eqn,val,density_moments j,normTree_bush]
    change (nodes A (Fin.last 22))^j.val-1=0
    rw [show nodes A (Fin.last 22)=1 from h.D.terminal,one_pow,sub_self]
  change e-B∈annih (treeSpace A 8)
  rw [mem_annih]
  intro u hu;rw [(ranks ha ho).e8_full] at hu
  obtain ⟨_,⟨a,rfl⟩,f,hf,rfl⟩:=Submodule.mem_sup.mp hu
  rw [map_add,pure f hf,add_zero,polyEval_apply,map_sum]
  apply Finset.sum_eq_zero;intro i _;rw [map_smul,bush i,smul_zero]

theorem unanchored_grid (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Unanchored A b)
    (i:Fin 23) (bi:b i≠0) (ti:tau A b i=0):(grid K).eval (mirror A i)=0:=by
  have marked:=unanchored_endpoint ha ho h
  rw [h.words 8 (by decide) (by decide)] at marked
  obtain ⟨Q,_,eqn⟩:=h.D.word_polynomial ha ho (h.D.nonlocal_cubic ha ho) (r:=6) (by decide) (by decide) marked
  rw [grid_native]
  by_cases t:i=Fin.last 22
  · subst i
    have ct:nodes A (Fin.last 22)=1:=h.D.terminal
    change (1-nodes A (Fin.last 22))*_=0
    rw [ct,sub_self,zero_mul]
  have e:=eqn i
  simp only [Pi.sub_apply,Pi.single_eq_of_ne t,zero_sub,weightedEval_apply,ti,mul_zero,neg_eq_zero] at e
  have nil:(density K).eval (nodes A i)=0:=(mul_eq_zero.mp e).resolve_right bi
  rw [density_reversed] at nil
  apply mul_eq_zero.mpr;right
  exact (mul_eq_zero.mp nil).resolve_left (by norm_num)
end
end RKCert.Paired.Seventeen
