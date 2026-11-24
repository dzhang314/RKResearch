module
public import RKCert.DirkTwentyGrid
public import RKCert.DirkTwentyCleanBudget
public import Mathlib.FieldTheory.IsAlgClosed.Basic
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.Endpoint RKCert.DirkQuintic
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b θ:Vec K (s+1)} {j:ℕ} {Q:K[X]}
noncomputable section
/-- Purely finite choice of as many omitted roots as the physical clean
site count permits. The only splitting assumption is on the fixed grid. -/
theorem omitted_ten_grid (S:Finset K) {n:ℕ} (room:n+S.card≤11)
    (sp:((X-1)*lobatto (K:=K) 10).Splits):
    ∃v:Fin n→K, Function.Injective v ∧ (∀k,((X-1)*lobatto 10).eval (v k)=0) ∧ ∀k,v k∉S:=by
  classical
  let D:K[X]:=(X-1)*lobatto 10
  let Λ:=D.roots.toFinset
  let E:=Λ \ S
  have deg:D.natDegree=11:=degree_grid10
  have dn:D≠0:=fun h=>by rw [h,natDegree_zero] at deg;omega
  have big:Λ.card=11:=by
    change D.roots.toFinset.card=_
    rw [Multiset.toFinset_card_of_nodup (nodup_roots sep_grid10),←sp.natDegree_eq_card_roots,deg]
  have card:n≤E.card:=by
    have cc:=Finset.le_card_sdiff S Λ
    change Λ.card-S.card≤E.card at cc;omega
  let pick:Fin n→E:=fun k=>(Fintype.equivFin E).symm ⟨k.val,by rw [Fintype.card_coe];have:=k.isLt;omega⟩
  let v:Fin n→K:=fun k=>(pick k).val
  have hit(k:Fin n):v k∈E:=(pick k).property
  refine ⟨v,?_,fun k=>((mem_roots dn).mp (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp (hit k)).1)).eq_zero,
    fun k=>(Finset.mem_sdiff.mp (hit k)).2⟩
  intro a b eqn
  exact Fin.ext (congrArg (fun x:Fin (Fintype.card E)=>x.val) ((Fintype.equivFin E).symm.injective (show pick a=pick b from Subtype.ext eqn)))

/-- Every missing physical clean knot is an actual root of the trace
numerator. Use the individual degree-ten grid cardinal and all its
original marked-to-ordinary pairings; do not invent a quadrature row. -/
theorem twenty_omitted_root (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (h:ReverseTrace A b 20 j θ Q) (budget:j+11≤20) (dQ:Q.natDegree<10)
    (support:∀i,θ i≠0→b i≠0 ∧ tau A b i=0) {z:K}
    (root:((X-1)*lobatto 10).eval z=0) (off:z∉cleanSites A b):Q.eval z=0:=by
  classical
  let D:K[X]:=(X-1)*lobatto 10
  obtain ⟨L,rep⟩:=(dvd_iff_isRoot.mpr (show D.IsRoot z from root))
  have deg:D.natDegree=11:=degree_grid10
  have nz:D≠0:=fun e=>by rw [e,natDegree_zero] at deg;omega
  have ln:L≠0:=fun e=>nz (by rw [rep,e,mul_zero])
  have ld:=congrArg Polynomial.natDegree rep
  rw [natDegree_mul (X_sub_C_ne_zero _) ln,natDegree_X_sub_C,deg] at ld
  have null:weightedEval (mirror A) θ L=0:=by
    ext i
    by_cases zero:θ i=0
    · simp [zero]
    obtain ⟨bi,ti⟩:=support i zero
    have yn:mirror A i≠z:=fun eqn=>off (eqn ▸ mem_cleanSites i bi ti)
    have val:D.eval (mirror A i)=0:=twenty_clean_grid ha ho size i bi ti
    rw [rep,eval_mul,eval_sub,eval_X,eval_C] at val
    have lz: L.eval (mirror A i)=0:=(mul_eq_zero.mp val).resolve_left (sub_ne_zero.mpr yn)
    simp [lz]
  have paid:=h.pair_polynomial ho L (by omega)
  rw [null] at paid
  have van:integral (L*Q)=0:=by rw [integral_eq,←formalPrimitive_eq_treePrimitive,←paid];simp
  rw [grid_cardinal_eval (m:=10) (Or.inr (Or.inr (Or.inr rfl))) rep.symm Q dQ] at van
  exact (mul_eq_zero.mp van).resolve_right (grid_cardinal_nz (m:=10) (Or.inr (Or.inr (Or.inr rfl))) rep.symm (by omega) ln)
end
end RKCert.Paired.Terminal
