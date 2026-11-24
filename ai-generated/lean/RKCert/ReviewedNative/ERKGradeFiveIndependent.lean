module

public import RKCert.ReviewedNative.ERKGradeFiveProfiles
public import RKCert.ReviewedNative.ERKProfileCompression
public import RKCert.ReviewedNative.PrimitiveHeadFactor
public import RKCert.ReviewedNative.OneOffReceiverPrefix

@[expose] public section

/-! # The independent quadratic branch of the native grade-five surplus
The first clean nonzero receiver proves an actual order-five prefix.
Its physical input labels, not raw stages, are counted, avoiding a
distinct-row hypothesis on the original tableau. -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree Module OneOff RKCert.OneEscape Polynomial
open scoped Matrix Classical FiniteRootedTree

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

private theorem minimal_independent_chain (ha : ∀ i j,i ≤ j → A i j=0)
    (sep : PolySeparated A 5) (cap : finrank K (zeroSpace A 5)≤4)
    (ind : diag (nodes A) (g A)∉Submodule.span K {g A}) :
    zeroSpace A 4=chain (diag (nodes A)) ⊥ (g A) 3 ∧
    zeroSpace A 5=chain (diag (nodes A)) ⊥ (g A) 4 := by
  obtain ⟨r2,r3,_,_⟩ := minimal_grade_five_ranks ha sep cap
  have cm : diag (nodes A) (g A)∈zeroSpace A 3 := diag_zeroSpace A 2 (mDef_mem A 1)
  have e : zeroSpace A 3=zeroSpace A 2 ⊔ Submodule.span K {diag (nodes A) (g A)} := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact sup_le (zeroSpace_mono A (by decide)) ((Submodule.span_singleton_le_iff_mem ..).mpr cm)
    · rw [Submodule.finrank_sup_span_singleton (by rwa [grade_two_span]),r2,r3]
  let C := diag (nodes A)
  let U : Submodule K (Fin s→K) := ⊥
  have stable : U.map C≤U := by simp [U]
  have c3 : zeroSpace A 3=chain C U (g A) 2 := by
    rw [e,grade_two_span]
    change _=(U ⊔ Submodule.span K {(C^0) (g A)}) ⊔ Submodule.span K {(C^1) (g A)}
    simp [U,C]
  have c4 : zeroSpace A 4=chain C U (g A) 3 :=
    (minimum_five_clock_step ha sep cap (j:=3) (by decide) (by decide)).trans
      (by rw [c3,clock_chain_next stable (by decide)])
  have c5 : zeroSpace A 5=chain C U (g A) 4 :=
    (minimum_five_clock_step ha sep cap (j:=4) (by decide) (by decide)).trans
      (by rw [c4,clock_chain_next stable (by decide)])
  exact ⟨c4,c5⟩

omit [CharZero K] in
private theorem pure_clock_rep {n j : ℕ} (pos : 0<n)
    (ev : zeroSpace A j=chain (diag (nodes A)) ⊥ (g A) n)
    {v : Fin s→K} (hv : v∈zeroSpace A j) :
    ∃ P : K[X], P.natDegree<n ∧ ∀ i,v i=P.eval (nodes A i)*g A i := by
  obtain ⟨u,hu,P,hP,rfl⟩ := HeadFiber.exists_poly (ev ▸ hv)
  have uz : u=0 := (Submodule.mem_bot K).mp hu
  refine ⟨P,?_,?_⟩
  · by_cases z : P=0
    · simpa [z] using pos
    · exact (natDegree_lt_iff_degree_lt z).mpr hP
  · simp [uz]

private theorem same_pure_profile {n : ℕ}
    (e4 : zeroSpace A 4=chain (diag (nodes A)) ⊥ (g A) n) (hn : 0<n)
    {j k : Fin s} (ck : nodes A j=nodes A k) (gk : g A j=g A k)
    (t : FiniteRootedTree) (ht : (t.order:ℕ)≤5) :
    Φ t A j=Φ t A k := by
  let m := (t.order:ℕ)-1
  have et : t.order = (clockTree m).order := by
    apply PNat.eq
    rw [order_clockTree]
    have := t.order.pos
    dsimp [m]
    omega
  have v := normDiff_mem (j:=4) A t _ et ht
  obtain ⟨P,_,e⟩ := pure_clock_rep hn e4 v
  have h₁ := e j
  have h₂ := e k
  simp only [Pi.sub_apply,normTree_clockTree] at h₁ h₂
  rw [ck,gk] at h₁
  have equal : normTree A t j=normTree A t k := by linear_combination h₁-h₂
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr t.forestFactorial.ne_zero)
  simpa only [normTree,Pi.smul_apply,smul_eq_mul] using equal

/-- Separated native grade five cannot be minimal if the first two
quadratic clock directions are independent. -/
theorem grade_five_surplus_of_independent_quadratic
    (ha : ∀ i j,i ≤ j → A i j=0) (sep : PolySeparated A 5)
    (ind : diag (nodes A) (g A)∉Submodule.span K {g A}) :
    5≤finrank K (zeroSpace A 5) := by
  by_contra! bad
  have cap : finrank K (zeroSpace A 5)≤4 := by omega
  obtain ⟨e4,e5⟩ := minimal_independent_chain ha sep cap ind
  have gn : g A≠0 := by
    intro z
    apply ind
    rw [z,map_zero]
    exact (Submodule.span K {(0:Fin s→K)}).zero_mem
  have gmem : g A∈zeroSpace A 2 := mDef_mem A 1
  obtain ⟨G,dG,Ge⟩ := pure_clock_rep (by decide) e4 (zeroSpace_mul (m:=2) (n:=2) gmem gmem)
  have Gev (l : Fin s) (hl : g A l≠0) : G.eval (nodes A l)=g A l := by
    have h := Ge l
    change g A l*g A l=G.eval (nodes A l)*g A l at h
    exact (mul_right_cancel₀ hl h).symm
  have Gn : G≠0 := by
    intro z
    apply gn
    ext l
    change g A l=0
    by_contra nz
    exact nz (by simpa only [z,eval_zero] using (Gev l nz).symm)
  let P : K[X] := X*G
  have pd : P.natDegree≤3 := Polynomial.natDegree_mul_le_of_le
    (show (X:K[X]).natDegree≤1 by simp) (show G.natDegree≤2 by omega)
  let Z := evalNodes A P - diag (nodes A) (g A)
  have zp (l : Fin s) : Z l=nodes A l*(G.eval (nodes A l)-g A l) := by
    simp [Z,P,mul_sub]
  have Cz : diag (nodes A) (g A)∈zeroSpace A 3 := diag_zeroSpace A 2 gmem
  have nz : Z≠0 := by
    intro z
    have eq : evalNodes A P=diag (nodes A) (g A) := sub_eq_zero.mp z
    exact (mul_ne_zero X_ne_zero Gn)
      (sep P (by omega) (eq ▸ zeroSpace_mono A (by decide : 3≤5) Cz))
  let U : Set (Fin s) := {l | nodes A l≠0 ∧ g A l=0}
  have ne : U.Nonempty := by
    obtain ⟨l,z⟩ := Function.ne_iff.mp nz
    rw [zp,Pi.zero_apply] at z
    refine ⟨l,left_ne_zero_of_mul z,?_⟩
    by_contra gz
    exact z (by rw [Gev l gz,sub_self,mul_zero])
  obtain ⟨i,⟨ci,gi⟩,imin⟩ := wellFounded_lt.has_min U ne
  have pre (l : Fin s) (li : l < i) (gz : g A l=0) : nodes A l=0 := by
    by_contra cn
    exact imin l ⟨cn,gz⟩ li
  have zpre (l : Fin s) (li : l < i) : Z l=0 := by
    rw [zp]
    by_cases gz : g A l=0
    · rw [pre l li gz,zero_mul]
    · rw [Gev l gz,sub_self,mul_zero]
  have mat0 (l : Fin s) (li : l ≤ i) : mat A Z l=0 :=
    causal_mat ha l Z (fun k kl=>zpre k (kl.trans_le li))
  have all0 : ∀ v∈zeroSpace A 5,v i=0 := by
    intro v hv
    obtain ⟨p,_,q⟩ := pure_clock_rep (by decide) e5 hv
    rw [q,gi,mul_zero]
  let e : Fin i.val→Fin s := Fin.castLE i.isLt.le
  let f : Fin i.val→Option K := fun l => if g A (e l)=0 then none else some (nodes A (e l))
  have earlier (l : Fin i.val) : e l < i := l.isLt
  have match_label (j k : Fin i.val) (eq : f j=f k) :
      nodes A (e j)=nodes A (e k) ∧ g A (e j)=g A (e k) := by
    by_cases j0 : g A (e j)=0 <;> by_cases k0 : g A (e k)=0
    · exact ⟨(pre _ (earlier j) j0).trans (pre _ (earlier k) k0).symm,j0.trans k0.symm⟩
    · simp [f,j0,k0] at eq
    · simp [f,j0,k0] at eq
    · have x : nodes A (e j)=nodes A (e k) := by simpa only [f,j0,k0,ite_false,Option.some.injEq] using eq
      exact ⟨x,(Gev _ j0).symm.trans ((congrArg G.eval x).trans (Gev _ k0))⟩
  have num := clean_five_receiver_profile_floor ha i ci all0 f (fun j k eq =>
    same_pure_profile e4 (by decide) (match_label j k eq).1 (match_label j k eq).2)
  let S : Finset K := (Finset.univ.filter (fun l : Fin i.val=>g A (e l)≠0)).image (fun l=>nodes A (e l))
  have cnt : 5≤S.card := by
    have sub : Finset.univ.image f ⊆ insert none (S.image some) := by
      intro j hj
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hj
      by_cases k : g A (e l)=0
      · simp [f,k]
      · rw [show f l=some (nodes A (e l)) by simp [f,k]]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k⟩,rfl⟩,rfl⟩)
    have cards := (Finset.card_le_card sub).trans
      ((Finset.card_insert_le ..).trans (Nat.succ_le_succ Finset.card_image_le))
    omega
  have AZ : mat A Z - evalNodes A (primitive P)∈zeroSpace A 4 := by
    have e : mat A Z - evalNodes A (primitive P)=
        (mat A (evalNodes A P)-evalNodes A (primitive P))-mat A (diag (nodes A) (g A)) := by
      dsimp only [Z]
      rw [map_sub,sub_right_comm]
    rw [e]
    exact (zeroSpace A 4).sub_mem (primitive_defect A P pd) (mat_zeroSpace_charZero A 3 Cz)
  obtain ⟨H,dH,Hfit⟩ := pure_clock_rep (by decide) e4 AZ
  let R := primitive P + G*H
  have Rd : R.natDegree≤4 := natDegree_add_le_of_degree_le
    (primitive_natDegree_le pd) (natDegree_mul_le_of_le
      (show G.natDegree≤2 by omega) (show H.natDegree≤2 by omega))
  have root (x : K) (hx : x∈S) : R.eval x=0 := by
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
    have gl : g A (e l)≠0 := (Finset.mem_filter.mp hl).2
    have val := Hfit (e l)
    rw [Pi.sub_apply,evalNodes_apply,mat0 _ (earlier l).le,←Gev _ gl] at val
    simp only [R,eval_add,eval_mul]
    linear_combination -val
  have R0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S root (by omega)
  have prod : primitive (X*G)=G*(-H) := by
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left R0
  have hn := primitive_X_mul_no_nonzero_root Gn (by simpa using Nat.le_of_lt_succ dH) prod ci
  have value := Hfit i
  rw [Pi.sub_apply,evalNodes_apply,mat0 i le_rfl,gi,mul_zero,zero_sub,neg_eq_zero] at value
  exact hn value

end RKResearch.Certified.Graded
