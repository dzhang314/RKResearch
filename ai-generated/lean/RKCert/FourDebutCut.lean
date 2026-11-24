module
public import RKCert.FourDebutStages
@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape Module Polynomial
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {c w : Vec K s}

theorem polynomial_head_mem {Q : Polynomial K} {n : ℕ} (deg : Q.degree<(n:WithBot ℕ)) :
    (fun i=>w i*Q.eval (c i))∈chain (diag c) U w n := by
  classical
  by_cases z : Q=0
  · subst Q
    simpa only [Polynomial.eval_zero,mul_zero,Pi.zero_def] using (chain (diag c) U w n).zero_mem
  have hd := (Polynomial.natDegree_lt_iff_degree_lt z).mpr deg
  have hh := ((chain_le_iff (T:=diag c) (U:=U) (w:=w) n).mp le_rfl).2
  have eqn : (fun i=>w i*Q.eval (c i)) = ∑ j∈Finset.range n, Q.coeff j • (diag c^j) w := by
    ext i
    rw [Finset.sum_apply,Polynomial.eval_eq_sum_range' hd,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Pi.smul_apply,smul_eq_mul,pow_diag_apply]; ring
  rw [eqn]
  exact (chain (diag c) U w n).sum_mem (fun j hj=>
    (chain (diag c) U w n).smul_mem _ (hh j (Finset.mem_range.mp hj)))

private noncomputable def atRows {d : ℕ} (c : Vec K s) (ix : Fin d→Fin s) :
    Polynomial K →ₗ[K] Vec K d := LinearMap.pi fun i => Polynomial.leval (c (ix i))

set_option maxHeartbeats 1200000 in
/-- A nonzero input profile in the actual chronological cut, simultaneously
zero under the primitive on every retained witness including the new debut.
Compatibility is measured over the full physical prefix. -/
theorem native_paired_cut [CharZero K] {k : ℕ} {i : Fin s} (ix : Fin (k+1)→Fin s)
    (ha : SDIRK.lower A) (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U)
    (hin : U≤zeroSpace A (k+3)) (chain_in : chain (diag (nodes A)) U w k ≤ zeroSpace A (k+3))
    (flag : zeroSpace A (k+4) ≤ chain (diag (nodes A)) U w (k+1))
    (prior : ∀ l, ix l < i) (outs : ∀l,¬Live U (ix l)) (outi : ¬Live U i)
    (cover : ∀ l < i, ¬Live U l → nodes A l≠0 → ∃a,nodes A l=nodes A (ix a))
    (wi : ∀ l,w (ix l) ≠ 0)
    (distinct : Function.Injective (fun l => nodes A (ix l))) (ai : A i i=0) :
    ∃ P Q : Polynomial K, P≠0 ∧ P.natDegree≤k+3 ∧ P.eval 0=0 ∧
      Q.degree<(k:WithBot ℕ) ∧ (∀ l,P.eval (nodes A (ix l))=w (ix l)*Q.eval (nodes A (ix l))) ∧
      (primitive P).eval (nodes A i)=0 ∧ (∀ l,(primitive P).eval (nodes A (ix l))=0) := by
  classical
  let H := compatible (nodes A) w U i
  let V := degreeLT K (k+3)
  let W := H ⊓ degreeLT K k
  let D := H ⊓ degreeLT K (k+1)
  let (n : ℕ) : FiniteDimensional K (degreeLT K n) := Module.Finite.equiv (degreeLTEquiv K n).symm
  let : FiniteDimensional K W := FiniteDimensional.of_injective
    (Submodule.inclusion (show W≤degreeLT K k from inf_le_right)) (Submodule.inclusion_injective _)
  let : FiniteDimensional K D := FiniteDimensional.of_injective
    (Submodule.inclusion (show D≤degreeLT K (k+1) from inf_le_right)) (Submodule.inclusion_injective _)
  let Vx : V→ₗ[K]Polynomial K := (LinearMap.mulLeft K Polynomial.X).comp V.subtype
  let obs := atRows (nodes A) ix
  let oldw := (diag (w ∘ ix)).comp obs
  let L := (obs.comp Vx).coprod (-(oldw.comp W.subtype))
  let iy : Fin ((k+1)+1)→Fin s := Fin.cons i ix
  let G := (atRows (nodes A) iy).comp (primitive.comp Vx)
  let B := ((diag (w ∘ iy)).comp (atRows (nodes A) iy)).comp D.subtype
  have eqL (f : V) (q : W) (hl : L (f,q)=0) (l : Fin (k+1)) :
      (Vx f).eval (nodes A (ix l))=w (ix l)*q.val.eval (nodes A (ix l)) := by
    have e := congrFun hl l
    change (Vx f).eval (nodes A (ix l)) + -(w (ix l)*q.val.eval (nodes A (ix l)))=0 at e
    exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])
  have hd (f : V) : (Vx f).natDegree≤k+3 := by
    change (X*f.val).natDegree≤k+3
    by_cases z : f.val=0
    · simp [z]
    · rw [Polynomial.natDegree_X_mul z]
      have h := (Polynomial.natDegree_lt_iff_degree_lt z).mpr (Polynomial.mem_degreeLT.mp f.property)
      omega
  have hzero (f : V) : (Vx f).eval 0=0 := by change (X*f.val).eval 0=0; simp
  have resp (f : V) (q : W) (hl : L (f,q)=0) : G f∈LinearMap.range B := by
    have fit := fit_prefix ix prior outs cover hT hU (hzero f) q.property.1 (eqL f q hl)
    obtain ⟨u,hu,fit⟩ := fit
    let wq : Vec K s := fun l => w l*q.val.eval (nodes A l)
    let v := evalNodes A (Vx f)-wq-u
    have wp : wq∈zeroSpace A (k+3) := chain_in (polynomial_head_mem (Polynomial.mem_degreeLT.mp q.property.2))
    have mv : v-evalNodes A (Vx f)∈zeroSpace A (k+3) := by
      have ee : v-evalNodes A (Vx f)=-(wq+u) := by dsimp [v]; abel
      rw [ee]; exact (zeroSpace A (k+3)).neg_mem ((zeroSpace A (k+3)).add_mem wp (hin hu))
    have pre : PrefixZero v i := by
      intro l h
      change ((Vx f).eval (nodes A l)-w l*q.val.eval (nodes A l))-u l=0
      rw [fit l h,sub_self]
    obtain ⟨R,degree,ok,he⟩ := primitive_output ha flag (hd f) mv pre ai
    refine ⟨⟨R,ok,Polynomial.mem_degreeLT.mpr degree⟩,?_⟩
    ext t
    change w (iy t)*R.eval (nodes A (iy t)) = (primitive (Vx f)).eval (nodes A (iy t))
    exact Fin.cases (he i le_rfl outi).symm (fun t=>(he _ (prior t).le (outs t)).symm) t
  have uniq (q : W) (hl : L (0,q)=0) : q=0 := by
    have z (t : Fin (k+1)) : q.val.eval (nodes A (ix t))=0 := by
      have h := eqL 0 q hl t
      rw [map_zero,Polynomial.eval_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (wi t)
    have hd : q.val.degree < (k:WithBot ℕ) := Polynomial.mem_degreeLT.mp q.property.2
    exact Subtype.ext (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ distinct.injOn
      (by rw [Finset.card_univ,Fintype.card_fin]; exact hd.trans (by exact_mod_cast Nat.lt_succ_self k)) (fun j _=>z j))
  have big : k+1+2 ≤ finrank K V := by
    rw [(degreeLTEquiv K (k+3)).finrank_eq,Module.finrank_fin_fun]
  have step : finrank K D ≤ finrank K W+1 := degree_charge H k
  obtain ⟨f,q,fnz,l0,g0⟩ := paired_kernel L G B big step resp uniq
  have fp : f.val≠0 := fun h => fnz (Subtype.ext h)
  have ge (j : Fin ((k+1)+1)) : (primitive (Vx f)).eval (nodes A (iy j))=0 := congrFun g0 j
  exact ⟨Vx f,q.val,mul_ne_zero X_ne_zero fp,hd f,hzero f,Polynomial.mem_degreeLT.mp q.property.2,
    eqL f q l0,ge 0,fun l=>ge l.succ⟩
end RKCert.FourDebut
