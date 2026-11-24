module
public import RKCert.FiveDebutPhysical
@[expose] public section
namespace RKCert.FiveDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape RKCert.FourDebut Module Polynomial
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K}
variable {U : Submodule K (Vec K s)} {w : Vec K s}

noncomputable section
private def atRows {d : ℕ} (c : Vec K s) (ix : Fin d→Fin s) : K[X] →ₗ[K] (Fin d→K) :=
  LinearMap.pi (fun j=>leval (c (ix j)))

/-- All earlier rows pay a zero primitive response; the frontier also pays
when (and only when invoked with) its already refunded zero diagonal.
The same output polynomial handles all physical repeats and origins. -/
theorem response_at_paid {j n : ℕ} {i : Fin s} {v : Vec K s} {P : K[X]}
    (ha : LowerArray A) (flag : zeroSpace A (j+1)≤chain (diag (nodes A)) U w n)
    (tr : OrdinaryTrace A j v P) (pre : PrefixZero v i) :
    ∃ Q : K[X], Q.degree<(n:WithBot ℕ) ∧ Q∈compatible (nodes A) w U i ∧
      ∀ l, (l < i ∨ l=i ∧ A i i=0) → ¬Live U l → (primitive P).eval (nodes A l)=w l*Q.eval (nodes A l) := by
  have pp : evalNodes A (primitive P)-mat A v∈zeroSpace A (j+1) := by
    simpa only [RKCert.Endpoint.formalPrimitive_eq_treePrimitive,neg_sub] using (zeroSpace A (j+1)).neg_mem tr.primitive.pure
  obtain ⟨u,hu,Q,dQ,eqn⟩:=exists_head_poly (flag pp)
  have val (l : Fin s) (hl : l < i ∨ l=i ∧ A i i=0) :
      (primitive P).eval (nodes A l)=u l+Q.eval (nodes A l)*w l := by
    have z : mat A v l=0 := by
      rcases hl with before|⟨rfl,diag0⟩
      · exact mat_zero_before ha pre l before
      · simpa only [diag0,zero_mul] using causalDiag_mat ha l v pre
    simpa only [Pi.sub_apply,evalNodes_apply,z,sub_zero] using eqn l
  have comp : Q∈compatible (nodes A) w U i := by
    refine ⟨fun z=>(primitive P).eval z,?_, -u,U.neg_mem hu,?_⟩
    · change (primitive P).eval 0=0
      rw [←Polynomial.coeff_zero_eq_eval_zero,primitive_coeff_zero]
    · intro l hl
      change w l*Q.eval (nodes A l)= -u l+(primitive P).eval (nodes A l)
      rw [val l (.inl hl)];ring
  refine ⟨Q,dQ,comp,fun l hl ho=>?_⟩
  have uz : u l=0 := by by_contra hn;exact ho ⟨u,hu,hn⟩
  rw [val l hl,uz,zero_add,mul_comm]

/-- Independent input/output site counts in the genuine paired-cut rank
lemma. Only d nonzero diagnostic heads are needed; the remaining old
representatives (notably the fourth before fifth refund) can still vanish. -/
theorem paid_paired_cut {j d t o : ℕ} {i : Fin s} (ix : Fin t→Fin s) (iy : Fin o→Fin s)
    (ha : LowerArray A) (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U)
    (inc : U≤zeroSpace A j) (chain_in : chain (diag (nodes A)) U w d≤zeroSpace A j)
    (flag : zeroSpace A (j+1)≤chain (diag (nodes A)) U w (d+1))
    (prior : ∀ k, ix k < i) (outside : ∀ k, ¬Live U (ix k))
    (cover : ∀ l < i, ¬Live U l → nodes A l≠0 → ∃ k, nodes A l=nodes A (ix k))
    (iy_pay : ∀ k, iy k < i ∨ iy k=i ∧ A i i=0) (iy_out : ∀ k, ¬Live U (iy k))
    (used : Fin d→Fin t) (active : ∀ k, w (ix (used k))≠0)
    (distinct : Function.Injective (fun k=>nodes A (ix (used k)))) (big : t+2≤j) :
    ∃ P Q : K[X], P≠0 ∧ P.natDegree≤j ∧ P.eval 0=0 ∧ Q.degree<(d:WithBot ℕ) ∧
      (∀ k, P.eval (nodes A (ix k))=w (ix k)*Q.eval (nodes A (ix k))) ∧
      ∀ k, (primitive P).eval (nodes A (iy k))=0 := by
  classical
  let H:=compatible (nodes A) w U i
  let V:=degreeLT K j
  let W:=H ⊓ degreeLT K d
  let D:=H ⊓ degreeLT K (d+1)
  let (n : ℕ) : FiniteDimensional K (degreeLT K n) := Module.Finite.equiv (degreeLTEquiv K n).symm
  let : FiniteDimensional K W := FiniteDimensional.of_injective (Submodule.inclusion (show W≤degreeLT K d from inf_le_right)) (Submodule.inclusion_injective _)
  let : FiniteDimensional K D := FiniteDimensional.of_injective (Submodule.inclusion (show D≤degreeLT K (d+1) from inf_le_right)) (Submodule.inclusion_injective _)
  let Vx : V→ₗ[K]K[X] := (LinearMap.mulLeft K X).comp V.subtype
  let obs:=atRows (nodes A) ix
  let L:=(obs.comp Vx).coprod (-(((diag (w ∘ ix)).comp obs).comp W.subtype))
  let G:=(atRows (nodes A) iy).comp (primitive.comp Vx)
  let B:=((diag (w ∘ iy)).comp (atRows (nodes A) iy)).comp D.subtype
  have ineq (f:V) (q:W) (zero:L (f,q)=0) (k:Fin t) :
      (Vx f).eval (nodes A (ix k))=w (ix k)*q.val.eval (nodes A (ix k)) := by
    have e:=congrFun zero k
    change (Vx f).eval (nodes A (ix k)) + -(w (ix k)*q.val.eval (nodes A (ix k)))=0 at e
    exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])
  have fd (f:V) : (Vx f).natDegree≤j := by
    change (X*f.val).natDegree≤j
    by_cases z:f.val=0
    · simp [z]
    · rw [natDegree_X_mul z]
      have g:=(natDegree_lt_iff_degree_lt z).mpr (mem_degreeLT.mp f.property)
      omega
  have f0 (f:V) : (Vx f).eval 0=0 := by change (X*f.val).eval 0=0;simp
  have resp (f:V) (q:W) (hz:L (f,q)=0) : G f∈LinearMap.range B := by
    obtain ⟨u,hu,fit⟩:=fit_prefix ix prior outside cover inv alg (f0 f) q.property.1 (ineq f q hz)
    let wq:Vec K s:=fun l=>w l*q.val.eval (nodes A l)
    let v:=evalNodes A (Vx f)-wq-u
    have wp:wq∈zeroSpace A j:=chain_in (polynomial_head_mem (mem_degreeLT.mp q.property.2))
    have tr:OrdinaryTrace A j v (Vx f):=by
      refine ⟨fd f,?_⟩
      rw [show v-evalNodes A (Vx f)= -(wq+u) by dsimp [v];abel]
      exact (zeroSpace A j).neg_mem ((zeroSpace A j).add_mem wp (inc hu))
    have pre:PrefixZero v i:=fun l hl=>by change ((Vx f).eval (nodes A l)-w l*q.val.eval (nodes A l))-u l=0;rw [fit l hl,sub_self]
    obtain ⟨R,dR,cR,vals⟩:=response_at_paid ha flag tr pre
    refine ⟨⟨R,cR,mem_degreeLT.mpr dR⟩,?_⟩
    ext k
    exact (vals _ (iy_pay k) (iy_out k)).symm
  have unique (q:W) (z:L (0,q)=0) : q=0 := by
    have van (k:Fin d) : q.val.eval (nodes A (ix (used k)))=0 := by
      have e:=ineq 0 q z (used k)
      rw [map_zero,eval_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_left (active k)
    exact Subtype.ext (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ distinct.injOn
      (by rw [Finset.card_univ,Fintype.card_fin];exact mem_degreeLT.mp q.property.2) (fun k _=>van k))
  have rank:t+2≤finrank K V:=by rw [(degreeLTEquiv K j).finrank_eq,Module.finrank_fin_fun];exact big
  obtain ⟨f,q,fnz,matchq,gz⟩:=paired_kernel L G B rank (degree_charge H d) resp unique
  have nn : f.val≠0:=fun z=>fnz (Subtype.ext z)
  exact ⟨Vx f,q.val,mul_ne_zero X_ne_zero nn,fd f,f0 f,mem_degreeLT.mp q.property.2,ineq f q matchq,fun k=>congrFun gz k⟩

end
end RKCert.FiveDebut
