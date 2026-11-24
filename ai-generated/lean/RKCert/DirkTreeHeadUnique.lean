module
public import RKCert.DirkTreeClockTail
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m n q : ℕ}
noncomputable section

/-- Coefficients for the fixed scalar block, the actual invariant vector,
and the growing head block map to physical stage values. -/
def treeHeadMap (A : Fin s→Fin s→K) (U : Submodule K (Vec K s)) (w : Vec K s) (m n : ℕ) :
    ((Fin (m+1)→K) × U × (Fin (n+1)→K)) →ₗ[K] Vec K s where
  toFun v := polyEval A m v.1 + v.2.1.val + diag w (polyEval A n v.2.2)
  map_add' a b := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,map_add];abel
  map_smul' a b := by
    change polyEval A m (a • b.1) + a • b.2.1.val + diag w (polyEval A n (a • b.2.2))=a • _
    rw [map_smul,map_smul,map_smul,smul_add,smul_add]

omit [CharZero K] in
/-- The low-degree scalar block and normalized orbit jointly span no more
than the range of the explicit coefficient map, including core coordinates. -/
theorem poly_chain_le_head_range {A : Fin s→Fin s→K} {U : Submodule K (Vec K s)} {w : Vec K s} :
    LinearMap.range (polyEval A m) ⊔ chain (diag (nodes A)) U w (n+1) ≤
        LinearMap.range (treeHeadMap A U w m n) := by
  classical
  intro x hx
  obtain ⟨_,⟨a,rfl⟩,v,hv,rfl⟩:=Submodule.mem_sup.mp hx
  obtain ⟨u,hu,Q,dQ,vq⟩:=Clock.exists_head_poly hv
  have dn : Q.natDegree≤n := by
    by_cases z:Q=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr dQ)
  refine ⟨(a,⟨u,hu⟩,fun i=>Q.coeff i.val),?_⟩
  change polyEval A m a + u + diag w (polyEval A n (fun i=>Q.coeff i.val))=polyEval A m a + v
  rw [←evalNodes_eq_polyEval A Q dn]
  ext i
  simp only [Pi.add_apply,diag_apply,evalNodes_apply,vq i]
  ring

namespace MidpointHead
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {r : ℕ}

/-- The coefficient map is injective and its range is exactly E_q. This
is full directness, not merely a claimed representation with no uniqueness. -/
theorem exact_tree_parameters (h : MidpointHead A m U w r) (fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+3≤2*m) (dn : n+1=r+(q-5)) :
    Function.Injective (treeHeadMap A U w m n) ∧ LinearMap.range (treeHeadMap A U w m n)=treeSpace A q := by
  have hm : 7≤m := by rcases fixed with rfl|rfl|rfl|rfl <;>decide
  let T:=treeHeadMap A U w m n
  have sub : treeSpace A q≤LinearMap.range T := by
    rw [h.tree_band fixed ha ho he low high,←dn]
    exact poly_chain_le_head_range
  have rk:=(even_dual_band hm ha ho he (q:=q) (r:=2*m-q-3) low (by omega)).1
  have st:=Submodule.finrank_mono sub
  have rt:=T.finrank_range_add_finrank_ker
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun] at rt
  have count:=h.count
  have k0 : finrank K (LinearMap.ker T)=0 := by omega
  refine ⟨LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp k0),?_⟩
  exact (Submodule.eq_of_le_of_finrank_le sub (by omega)).symm

omit [CharZero K] in
private theorem poly_zero_of_low_coeff (P : K[X]) (dP : P.natDegree≤n)
    (eqn : (fun i : Fin (n+1)=>P.coeff i.val)=0) : P=0 := by
  ext k
  by_cases hk:k<n+1
  · exact (congrFun eqn ⟨k,hk⟩).trans (coeff_zero k).symm
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).trans (coeff_zero k).symm

/-- Polynomial formulation of the actual three-block direct sum. -/
theorem physical_relation_trivial (h : MidpointHead A m U w r)
    (fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+3≤2*m)
    {H Q : K[X]} (dH : H.natDegree≤m) (dQ : Q.natDegree<r+(q-5))
    {u : Vec K (s+1)} (hu : u∈U)
    (eqn : ∀ i, H.eval (nodes A i)+u i+Q.eval (nodes A i)*w i=0) :
    H=0 ∧ u=0 ∧ Q=0 := by
  let n:=r+(q-5)-1
  have en : n+1=r+(q-5) := by dsimp [n];have:=h.positive;omega
  have dq : Q.natDegree≤n := by omega
  let t : (Fin (m+1)→K) × U × (Fin (n+1)→K) :=
    (fun i=>H.coeff i.val,⟨u,hu⟩,fun i=>Q.coeff i.val)
  have z : treeHeadMap A U w m n t=0 := by
    change polyEval A m _ + u + diag w (polyEval A n _)=0
    rw [←evalNodes_eq_polyEval A H dH,←evalNodes_eq_polyEval A Q dq]
    ext i;simpa [mul_comm] using eqn i
  have i0:=((h.exact_tree_parameters fixed ha ho he low high en).1 (z.trans (map_zero _).symm))
  exact ⟨poly_zero_of_low_coeff H dH (congrArg Prod.fst i0),
    congrArg (fun a => (a.2.1 : Vec K (s+1))) i0,
    poly_zero_of_low_coeff Q dq (congrArg (fun a=>a.2.2) i0)⟩

/-- All paid head powers cost different effective numerical sites at every
tail grade, even when the tableau has physically repeated abscissae. -/
theorem physical_head_site_bound (h : MidpointHead A m U w r)
    (fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+3≤2*m) :
    r+(q-5)≤(Clock.headSites (nodes A) w).card := by
  classical
  by_contra! small
  let Z:=Clock.headSites (nodes A) w
  let Q:=Lagrange.nodal Z id
  have dn:Q.natDegree=Z.card:=Lagrange.natDegree_nodal
  have hz:=h.physical_relation_trivial fixed ha ho he low high (H:=0) (Q:=Q)
    (by simp) (by rw [dn];exact small) (u:=0) U.zero_mem (fun i=>by
      by_cases z:w i=0
      · simp [z]
      have mem:=Clock.headSites_mem (c:=nodes A) i z
      have v:Q.eval (nodes A i)=0:=Lagrange.eval_nodal_at_node (v:=id) mem
      simp [v])
  exact Lagrange.nodal_ne_zero hz.2.2

end MidpointHead
end
end RKCert.Paired.Terminal
