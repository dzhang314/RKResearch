module
public import RKCert.DirkTreeHeadUnique
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m q : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
noncomputable section
namespace MidpointHead
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {r : ℕ}

/-- Both directions of the full physical scalar/core/head parameterization.
Together with physical_relation_trivial this gives uniqueness, not merely
an unspecified decomposition into overlapping spaces. -/
theorem tree_polynomial_iff (h : MidpointHead A m U w r)
    (fixed : m=7 ∨ m=8 ∨ m=9 ∨ m=10) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (low : m≤q) (high : q+3≤2*m) (v : Vec K (s+1)) :
    v∈treeSpace A q ↔ ∃ H : K[X], ∃ u∈U, ∃ Q : K[X], H.natDegree≤m ∧ Q.natDegree<r+(q-5) ∧
      ∀ i, v i=H.eval (nodes A i)+u i+Q.eval (nodes A i)*w i := by
  classical
  let n:=r+(q-5)-1
  have en : n+1=r+(q-5) := by dsimp [n];have:=h.positive;omega
  rw [←(h.exact_tree_parameters fixed ha ho he low high en).2]
  constructor
  · rintro ⟨⟨a,u,t⟩,rfl⟩
    refine ⟨ofFn (m+1) a,u,u.property,ofFn (n+1) t,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a),?_,?_⟩
    · rw [←en];exact ofFn_natDegree_lt (by omega) t
    · intro i
      change (polyEval A m a + (u:Vec K (s+1)) + diag w (polyEval A n t)) i=_
      rw [←evalNodes_ofFn A m a,←evalNodes_ofFn A n t]
      simp [mul_comm]
  · rintro ⟨H,u,hu,Q,dh,dq,res⟩
    have dn:Q.natDegree≤n:=by omega
    refine ⟨(fun i=>H.coeff i.val,⟨u,hu⟩,fun i=>Q.coeff i.val),?_⟩
    change polyEval A m _ + u + diag w (polyEval A n _)=v
    rw [←evalNodes_eq_polyEval A H dh,←evalNodes_eq_polyEval A Q dn]
    ext i
    simpa [mul_comm] using (res i).symm

end MidpointHead

/-- The actual p14/p16 surviving equality charts, simultaneously. The
mode count at the final grade is r+2m−8; the head can have only one or
two base powers at grade five. No local quartic premise remains. -/
theorem fixed_forward_tree_head (hm : m=7 ∨ m=8) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m) :
    ∃ U w r, MidpointHead A m U w r ∧ (r=1 ∨ r=2) ∧
    r+2*m-8≤(Clock.headSites (nodes A) w).card ∧
    ∀ q, m≤q → q+3≤2*m →
      (treeSpace A q=LinearMap.range (polyEval A m) ⊔ chain (diag (nodes A)) U w (r+(q-5))) := by
  obtain ⟨U,w,r,h⟩:=midpoint_head_fixed hm ha ho he
  have fix : m=7 ∨ m=8 ∨ m=9 ∨ m=10 := hm.imp_right Or.inl
  have seven:7≤m:=by rcases hm with rfl|rfl <;>decide
  have cnt:=h.physical_head_site_bound fix ha ho he (q:=2*m-3) (by omega) (by omega)
  refine ⟨U,w,r,h,by have:=h.count;have:=h.lower;have:=h.upper;omega,by omega,?_⟩
  intro q lo hi
  exact h.tree_band fix ha ho he lo hi

end
end RKCert.Paired.Terminal
