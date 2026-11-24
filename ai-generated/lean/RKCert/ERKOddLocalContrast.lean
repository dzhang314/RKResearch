module
public import RKCert.ERKOddLocalHidden
public import RKCert.ERKOddReversePrefixDetector
public import RKCert.ERKOddBroadLow

@[expose] public section
/-! # Two actual numerical masks in the localized odd contrast
Only the forward hidden kernel is a coordinate algebra, never the reverse
base subspace. The corrected contrast retains exact scalar moments. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
variable {K:Type*} [Field K]
noncomputable section

theorem joint_selector_mem {s:ℕ}{U:Submodule K (Vec K s)}{x y u:Vec K s}
    (hx:U.map (diag x)≤U)(hy:U.map (diag y)≤U)(uU:u∈U)(a:K→K→K):
    (fun i=>a (x i) (y i)*u i)∈U:=by
  classical
  have my:MaskInvariant y U:=by
    intro p v vU
    have h:=fiber_mem hy p vU
    have same:blockMask y p v=fiber y p v:=by ext i;by_cases e:y i=p <;> simp [blockMask,fiber,e]
    rwa [same]
  have eq:(fun i=>a (x i) (y i)*u i)=
      ∑ p ∈ Clock.sites x,(fun i=>a p (y i)*fiber x p u i):=by
    ext i
    rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (x i) (site_mem x i)]
    · simp [fiber]
    · intro p _ ne
      simp [fiber,Ne.symm ne]
  rw [eq]
  exact U.sum_mem (fun p _=>mulByBlock_mem y my (a p) (fiber_mem hx p uU))

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ f:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}

def localContrast (A:Fin 26→Fin 26→K)(b f:Vec K 26)(Q:K[X]):Vec K 26:=by
  classical
  exact fun i=>if f i=0 then Q.eval (mirror A i)*b i else 0

omit [IsStrictOrderedRing K] in
theorem localContrast_apply (Q:K[X])(i:Fin 26):
    localContrast A b f Q i=(if f i=0 then Q.eval (mirror A i)*b i else 0):=by
  classical
  rfl

theorem LocalLinearBand.local_contrast_clean (B:LocalLinearBand A b r U τ)
    (Q P:K[X]) {u:Vec K 26}(uU:u∈U)
    (preserve:∀v∈U,f*v∈U)
    (fit:weightedEval (mirror A) τ Q=τ*f)
    (rep:b*f=u+weightedEval (mirror A) τ P):
    ∃v∈U,localContrast A b f Q=
      weightedEval (mirror A) b Q-weightedEval (mirror A) τ P-v:=by
  classical
  let y:=mirror A
  let w(a z:K):K:=if z≠0 ∧ z≠Q.eval a then Q.eval a/z-1 else 0
  have invf:U.map (diag f)≤U:=by
    rintro _ ⟨v,hv,rfl⟩
    have e:diag f v=f*v:=by ext i;simp [diag_apply]
    rw [e];exact preserve v hv
  let ζ:Vec K 26:=fun i=>w (y i) (f i)*u i
  have zu:ζ∈U:=joint_selector_mem B.clock invf uU w
  refine ⟨u+ζ,U.add_mem uU zu,?_⟩
  ext i
  have fh:=congrFun fit i
  have g:=congrFun rep i
  simp only [weightedEval_apply,Pi.mul_apply,Pi.add_apply] at fh g
  change Q.eval (y i)*τ i=τ i*f i at fh
  change b i*f i=u i+P.eval (y i)*τ i at g
  rw [localContrast_apply]
  simp only [Pi.sub_apply,Pi.add_apply,weightedEval_apply]
  change (if f i=0 then Q.eval (y i)*b i else 0)=
    Q.eval (y i)*b i-P.eval (y i)*τ i-(u i+w (y i) (f i)*u i)
  by_cases z:f i=0
  · have wz:w (y i) (f i)=0:=by simp [w,z]
    rw [z,mul_zero] at g
    rw [ite_eq_left z,wz,zero_mul,add_zero]
    linear_combination -g
  rw [ite_eq_right z]
  by_cases same:f i=Q.eval (y i)
  · have wz:w (y i) (f i)=0:=by simp [w,same]
    rw [wz,zero_mul,add_zero]
    rw [same] at g
    linear_combination -g
  have e:τ i=0:=by
    have h:τ i*(f i-Q.eval (y i))=0:=by linear_combination -fh
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr same)
  rw [e,mul_zero,add_zero] at g
  rw [e,mul_zero,sub_zero,show w (y i) (f i)=Q.eval (y i)/f i-1 from ite_eq_left ⟨z,same⟩,←g]
  field_simp [z]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mirror_eval_in_tree {s j:ℕ}{A:Fin s→Fin s→K}(P:K[X])(dP:P.natDegree≤j):
    (fun i=>P.eval (mirror A i))∈treeSpace A j:=by
  have eq:(fun i=>P.eval (mirror A i))=evalNodes A (reflectPolynomial P):=by
    ext i;simp [reflectPolynomial,eval_comp,mirror]
  rw [eq]
  exact evalNodes_mem_treeSpace A _ ((reflectPolynomial_degree _).trans dP)

theorem LocalLinearBand.local_contrast_moments (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17) (Q P R:K[X]) {u W:Vec K 26}
    (uU:u∈U)(eq:W=weightedEval (mirror A) b Q-weightedEval (mirror A) τ P-u)
    (qb:R.natDegree+Q.natDegree+1≤17)(pb:R.natDegree+P.natDegree≤15-r)
    (ub:R.natDegree≤16-r):
    (∑i,weightedEval (mirror A) W R i)=(Paired.primitive (R*Q)).eval 1:=by
  let y:=mirror A
  have e:weightedEval y W R=
      weightedEval y b (R*Q)-weightedEval y τ (R*P)-weightedEval y u R:=by
    ext i
    rw [eq]
    simp only [weightedEval_apply,Pi.sub_apply,eval_mul,y]
    ring
  have hQ:(R*Q).natDegree+1≤17:=by have e:=natDegree_mul_le (p:=R) (q:=Q);omega
  have hP:(R*P).natDegree≤15-r:=natDegree_mul_le.trans pb
  have zt:=mem_annih.mp B.paid _ (mirror_eval_in_tree (A:=A) _ hP)
  have zu:=mem_annih.mp (B.base_annih ho uU) _ (mirror_eval_in_tree (A:=A) R ub)
  have zT:(∑ i,weightedEval y τ (R*P) i)=0:=by
    simpa only [weightedEval_apply,row_apply,mul_comm] using zt
  have zU:(∑ i,weightedEval y u R i)=0:=by
    simpa only [weightedEval_apply,row_apply,mul_comm] using zu
  rw [e]
  simp only [Pi.sub_apply,Finset.sum_sub_distrib]
  rw [zT,zU,sub_zero,sub_zero,reflected_scalar_budget ho (R*Q) hQ,formalPrimitive_eq_treePrimitive]
end
end RKCert.Paired.ReverseHull

