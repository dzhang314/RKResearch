module
public import RKCert.Dirk17SevenSites
public import RKCert.DirkSynchronousFifth
public import RKCert.RadauMissingRoot
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b θ:Vec K (s+1)}
noncomputable section
set_option maxRecDepth 3500
set_option maxHeartbeats 1500000
/-- The finite seven-clean support count yields *six* exact global
moments, testing the actual grade-five trace before its clock cost can
be charged again. The polynomial T is the nodal product over the actual
remaining clean clocks, not the free coefficient of any assumed tableau. -/
theorem seven_clean_global (ho:HasTreeOrderAtLeast A b 17)(Q:K[X]) (u v:K)
    (many:(cleanSites A b).card≤7) (zero:0∈cleanSites A b) (uS:u∈cleanSites A b)(vS:v∈cleanSites A b)
    (un:u≠0)(vn:v≠0)(diff:v≠u)
    (tr:ReverseTrace A b 17 5 (diag (mirror A) θ) (X*Q))
    (active:∀i,θ i≠0→b i≠0 ∧ tau A b i=0):
    ∃T:K[X], T.natDegree≤4 ∧ T≠0 ∧
      ∀k:Fin 6,integral (X^(k.val+1)*((X-C u)*(X-C v)*Q)*T)=0:=by
  classical
  let S:=cleanSites A b
  let R:=((S.erase 0).erase u).erase v
  let T:K[X]:=Lagrange.nodal R id
  have hu:u∈S.erase 0:=Finset.mem_erase.mpr ⟨un,uS⟩
  have hv:v∈(S.erase 0).erase u:=Finset.mem_erase.mpr ⟨diff,Finset.mem_erase.mpr ⟨vn,vS⟩⟩
  have deg:T.natDegree≤4:=by
    rw [show T.natDegree=R.card from Lagrange.natDegree_nodal]
    change (((S.erase 0).erase u).erase v).card≤4
    rw [Finset.card_erase_of_mem hv,Finset.card_erase_of_mem hu,Finset.card_erase_of_mem zero]
    omega
  refine ⟨T,deg,Lagrange.nodal_ne_zero,?_⟩
  intro k
  let L:K[X]:=X^k.val*(X-C u)*(X-C v)*T
  have dL:L.natDegree≤11:=by
    have a:=natDegree_mul_le (p:=(X:K[X])^k.val) (q:=(X-C u:K[X]))
    have b:=natDegree_mul_le (p:=(X:K[X])^k.val*(X-C u)) (q:=X-C v)
    have d:=natDegree_mul_le (p:=(X:K[X])^k.val*(X-C u)*(X-C v)) (q:=T)
    rw [natDegree_X_pow,natDegree_X_sub_C] at a
    rw [natDegree_X_sub_C] at b
    change (X^k.val*(X-C u)*(X-C v)*T).natDegree≤11
    have:=k.isLt;omega
  let y:=mirror A
  have point(i:Fin (s+1)) : (y i*θ i)*L.eval (y i)=0:=by
    by_cases z:θ i=0
    · simp [z]
    obtain ⟨bi,ti⟩:=active i z
    by_cases yz:y i=0
    · simp [yz]
    by_cases yu:y i=u
    · simp [L,yu]
    by_cases yv:y i=v
    · simp [L,yv]
    have yi:y i∈R:=Finset.mem_erase.mpr ⟨yv,Finset.mem_erase.mpr ⟨yu,Finset.mem_erase.mpr ⟨yz,mem_cleanSites i bi ti⟩⟩⟩
    have tv:T.eval (y i)=0:=Lagrange.eval_nodal_at_node (v:=id) yi
    simp [L,tv]
  have paid:=tr.pair_polynomial_radau ho L (by omega)
  have kill:row (diag y θ) (weightedEval y (1:Vec K (s+1)) L)=0:=by
    rw [row_apply];apply Finset.sum_eq_zero;intro i _
    simpa [diag_apply,weightedEval_apply,mul_comm] using point i
  change row (diag y θ) (weightedEval y (1:Vec K (s+1)) L)=unitIntegral (L*(X*Q)) at paid
  rw [kill,unitIntegral_apply] at paid
  rw [integral_eq,←formalPrimitive_eq_treePrimitive]
  have swap:X^(k.val+1)*((X-C u)*(X-C v)*Q)*T=L*(X*Q):=by rw [pow_succ];dsimp [L];ring
  rw [swap];exact paid.symm
end
end RKCert.Paired.Terminal
