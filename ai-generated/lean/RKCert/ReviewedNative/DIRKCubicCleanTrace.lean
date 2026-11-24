module

public import RKCert.ReviewedNative.ClockHeadPaidFlow
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import RKCert.ReviewedNative.DIRKOrderSix

@[expose] public section

/-! # Paid native primitive tests on clean physical rows of a cubic head -/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b w y : Fin s → K}

omit [CharZero K] in
private theorem primitive_eval_power (P : K[X]) (x : K) (k d : ℕ) (hd : P.natDegree≤d) :
    (primitive (X^k*P)).eval x=
      ∑ j : Fin (d+1), P.coeff j.val * x^(k+j.val+1) / ((k+j.val+1:ℕ):K) := by
  have sum : X^k*P=∑ j : Fin (d+1), monomial (k+j.val) (P.coeff j.val) := by
    conv_lhs => rw [P.as_sum_range' _ (Nat.lt_succ_of_le hd)]
    rw [Finset.mul_sum,Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [X_pow_mul_monomial k j.val (P.coeff j.val),Nat.add_comm j.val k]
  rw [sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [primitive_monomial,eval_monomial,div_mul_eq_mul_div]

/-- Three local primitive tests, at one nonzero clock, are full-rank
on an origin-cleared input of length three.  This is the standard native
Cauchy separation with the local clock's powers factored out. -/
theorem detect_short_primitive_tests (ho : HasOrder A b p) (pay : 6≤p)
    (Q : K[X]) (d : Q.natDegree≤2) (x : K) (nx : x≠0)
    (tests : ∀ k : Fin 3, (primitive (X^(1+k.val)*Q)).eval x=0) : Q=0 := by
  let a : Fin 3 → K := fun i => Q.coeff i.val*x^i.val
  have m (k : Fin 3) : (∑ j : Fin 3, a j/((k.val+j.val+2:ℕ):K))=0 := by
    have h := tests k
    rw [primitive_eval_power Q x _ 2 d] at h
    apply (mul_left_cancel₀ (pow_ne_zero (k.val+2) nx))
    rw [mul_zero,←h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have e : 1+k.val+j.val+1=k.val+j.val+2 := by omega
    have e' : k.val+j.val+2=(k.val+2)+j.val := by omega
    rw [e,mul_div_assoc]
    rw [e',pow_add]
    dsimp [a]
    ring
  have z := moments_detect ho (d:=2) (by decide) (by omega)
    (fun i j : Fin 3 => by have := i.isLt; have := j.isLt; omega) a m
  ext j
  rw [coeff_zero]
  by_cases h : j<3
  · exact (mul_eq_zero.mp (z ⟨j,h⟩)).resolve_right (pow_ne_zero j nx)
  · apply coeff_eq_zero_of_natDegree_lt
    omega

omit [CharZero K] in
private theorem first_nonzero {y : Fin s → K} (hy : y≠0) :
    ∃ i, y i≠0 ∧ ∀ j < i, y j=0 := by
  classical
  let S := Finset.univ.filter (fun i => y i≠0)
  have hS : S.Nonempty := by
    by_contra h
    apply hy
    ext i
    by_contra nz
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nz⟩⟩
  let i := S.min' hS
  refine ⟨i,(Finset.mem_filter.mp (S.min'_mem hS)).2,fun j hj => ?_⟩
  by_contra nz
  exact (not_le_of_gt hj) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,nz⟩))

omit [CharZero K] in
theorem pure_head_zero_on_clean {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    {v : Fin s → K} (mem : v∈zeroSpace A (3+k)) {i : Fin s} (clean : w i=0) :
    v i=0 := by
  obtain ⟨q,_,val⟩ := pure_head_repr bk mem
  rw [val,weightedEval_apply,clean,mul_zero]

set_option maxHeartbeats 400000 in
/-- A native grade-three contrast supported only on clean nonzero clocks
cannot have a nonzero scalar of the form XQ, deg Q <= 2. No fold, deleted
stage or new order predicate is used. Its first physical coordinate is
tested with the diagonal-retaining Volterra commutator. -/
theorem no_short_clean_contrast (ha : A.IsLowerTriangular) (ho : HasOrder A b p) (pay : 7≤p)
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (Q : K[X]) (d : Q.natDegree≤2)
    (mem : y-evalNodes A (X*Q) ∈ zeroSpace A 3)
    (clean : ∀ i, y i≠0 → w i=0) (clock : ∀ i, y i≠0 → nodes A i≠0) :
    Q=0 := by
  have dX : (X*Q).natDegree≤3 :=
    natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  by_cases yz : y=0
  · have m : evalNodes A (X*Q)∈zeroSpace A 3 := by
      simpa [yz] using (zeroSpace A 3).neg_mem mem
    have sep : PolySeparated A 3 := PolySeparated.of_coeff (coeff_separated ho (by omega))
    exact (mul_eq_zero.mp (sep _ dX m)).resolve_left X_ne_zero
  obtain ⟨i,iy,before⟩ := first_nonzero yz
  have ic := clean i iy
  have ci := clock i iy
  have mm : y∈treeSpace A 3 := by
    have all := (treeSpace A 3).add_mem (zeroSpace_le_treeSpace A _ mem) (evalNodes_mem_treeSpace A _ dX)
    simpa only [sub_add_cancel] using all
  have vm : volterra A y∈zeroSpace A 5 := volterra_treeSpace ho 3 (by omega) mm
  have vz := pure_head_zero_on_clean (band 2 (by decide)) vm ic
  rw [volterra_pivot ha i y before] at vz
  have a0 : A i i=0 :=
    sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp vz).resolve_right iy))
  let C₀ := diag (nodes A)
  have shifted (k : ℕ) :
      (C₀^k) y - evalNodes A (X^(1+k)*Q) ∈ zeroSpace A (3+k) := by
    induction k with
    | zero => simpa [Module.End.one_eq_id] using mem
    | succ k ih =>
      have step := diag_zeroSpace A (3+k) ih
      change C₀ ((C₀^k) y - evalNodes A (X^(1+k)*Q)) ∈ zeroSpace A (3+k+1) at step
      have ec : C₀ (evalNodes A (X^(1+k)*Q)) = evalNodes A (X^(1+(k+1))*Q) := by
        ext j
        simp only [C₀,diag_apply,evalNodes_apply,eval_mul,eval_pow,eval_X]
        rw [show 1+(k+1)=1+k+1 by omega,pow_succ']
        ring
      rw [map_sub,ec] at step
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact step
  apply detect_short_primitive_tests ho (by omega) Q d _ ci
  intro k
  let n := k.val
  let f := X^(1+n)*Q
  let v := (C₀^n) y
  have df : f.natDegree≤3+n := by
    dsimp [f]
    apply natDegree_mul_le.trans
    rw [natDegree_pow,natDegree_X]
    omega
  let W := zeroSpace A (3+n+1)
  have ev : mat A v - evalNodes A (primitive f) ∈ W := by
    have h : mat A (v-evalNodes A f)∈W := mat_zeroSpace_charZero A _ (shifted n)
    rw [map_sub] at h
    convert W.add_mem h (primitive_defect A f df) using 1
    abel
  have n2 : n≤2 := Nat.le_of_lt_succ k.isLt
  have bF : W=chain C₀ ⊥ w (1+(n+1)) := by
    rw [show W=zeroSpace A (3+(n+1)) by rfl,band (n+1) (by omega)]
  have zero := pure_head_zero_on_clean (A:=A) (w:=w) (k:=n+1) bF ev ic
  have pin (j : Fin s) (hj : j < i) : v j=0 := by
    change (diag (nodes A)^n) y j=0
    rw [clock_power_value,before _ hj,mul_zero]
  have out : mat A v i=0 := by
    rw [mat_apply,lowerTriangular_mulVec_pivot ha i _ pin,a0,zero_mul]
  simpa only [Pi.sub_apply,out,evalNodes_apply,zero_sub,neg_eq_zero] using zero

/-- The physical degree-three head's amplitude has nonzero constant.
The complementary contrast would otherwise have the forbidden short
origin-cleared trace. -/
theorem cubic_amplitude_nonzero_at_origin (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (pay : 7≤p)
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (P : K[X]) (nz : P≠0) (deg : P.natDegree≤3)
    (fit : ∀ i, w i≠0 → w i=P.eval (nodes A i)) : P.eval 0≠0 := by
  intro P0
  have div : X∣P := by rwa [X_dvd_iff,coeff_zero_eq_eval_zero]
  obtain ⟨Q,hQ⟩ := div
  have Qnz : Q≠0 := by intro q0; apply nz; simp [hQ,q0]
  have dQ : Q.natDegree≤2 := by
    rw [hQ,natDegree_mul X_ne_zero Qnz,natDegree_X] at deg
    omega
  let y := evalNodes A P-w
  have wm : w∈zeroSpace A 3 := by
    have h := ((clock_chain_le_iff _).mp (band 0 (by decide)).ge).2 0 (by decide : (0:ℕ)<1+0)
    simpa using h
  have m : y-evalNodes A (X*Q)∈zeroSpace A 3 := by
    rw [←hQ]
    convert (zeroSpace A 3).neg_mem wm using 1
    dsimp [y]
    abel
  apply Qnz (no_short_clean_contrast ha ho pay band Q dQ m ?_ ?_)
  · intro i iy
    by_contra wne
    exact iy (by simp [y,fit i wne])
  · intro i iy z
    have wz : w i=0 := by
      by_contra nw
      exact nw (by rw [fit i nw,z,P0])
    exact iy (by simp [y,z,P0,wz])

omit [CharZero K] in
/-- The complementary clean contrast must be visible at a nonzero clock.
Here the exact C(2) zero first row buys one Cauchy probe: grade 4 and
degree 4 are both detected at order 8, not 9. -/
theorem dirk_C2_has_clean_nonroot (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (pay : 8≤p) (c₂ : monomialStageDefect A 1=0)
    (P : K[X]) (nz : P≠0) (deg : P.natDegree≤3)
    (fit : ∀ i, monomialStageDefect A 2 i≠0 → monomialStageDefect A 2 i=P.eval (nodes A i)) :
    ∃ i, monomialStageDefect A 2 i=0 ∧ nodes A i≠0 ∧ P.eval (nodes A i)≠0 := by
  cases s with
  | zero =>
    have rank := (dirk_forward_rank_three ha ho (by omega)).1
    have cap := Submodule.finrank_le (zeroSpace A 3)
    rw [Module.finrank_fin_fun] at cap
    omega
  | succ s =>
    by_contra! no
    have row0 := dirk_first_row_of_zero_quadratic ha (congrFun c₂ 0)
    have sep : PolySeparated A 4 :=
      PolySeparated.of_coeff (coeff_defect_separated_zero_row ho row0 (by omega) (by omega))
    apply mul_ne_zero X_ne_zero nz
    apply sep _ (natDegree_mul_le.trans (by rw [natDegree_X]; omega))
    have he : evalNodes A (X*P)=diag (nodes A) (monomialStageDefect A 2) := by
      ext i
      rw [evalNodes_apply,diag_apply,eval_mul,eval_X]
      by_cases cz : nodes A i=0
      · rw [cz,zero_mul,zero_mul]
      by_cases z : monomialStageDefect A 2 i=0
      · rw [z,no i z cz,mul_zero]
      · rw [fit i z]
    rw [he]
    exact diag_zeroSpace A 3 (monomialStageDefect_mem A 2)


private theorem native_primitive_deriv (P : K[X]) : (primitive P).derivative=P := by
  ext k
  rw [coeff_derivative,primitive_coeff_succ]
  have n : (((k+1:ℕ):K))≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ (P.coeff k) n

omit [CharZero K] in
private theorem primitive_origin (P : K[X]) : (primitive P).eval 0=0 := by
  rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]

/-- Two nonzero, distinct prospective first clean clocks cannot both kill
the two paid primitives. Four foreign roots plus a triple origin exceed
degree six. -/
theorem two_clean_clocks_impossible (P : K[X]) (nz : P≠0) (deg : P.natDegree≤3)
    (u v : K) (un : u≠0) (vn : v≠0) (sep : u≠v)
    (u1 : (primitive (X*P)).eval u=0) (u2 : (primitive (X*(X*P))).eval u=0)
    (v1 : (primitive (X*P)).eval v=0) (v2 : (primitive (X*(X*P))).eval v=0) : False := by
  let Q := primitive (X*P)
  let T := primitive (X*(X*P))
  let F := X*Q-T
  have dQ : Q.derivative=X*P := native_primitive_deriv _
  have dF : F.derivative=Q := by
    dsimp [F]
    rw [derivative_sub,derivative_mul,derivative_X,one_mul,dQ]
    rw [show T.derivative=X*(X*P) from native_primitive_deriv _]
    rw [add_sub_cancel_right]
  have Fne : F≠0 := by
    intro z
    rw [z,derivative_zero] at dF
    rw [←dF,derivative_zero] at dQ
    exact (mul_ne_zero X_ne_zero nz) dQ.symm
  have Fdeg : F.natDegree≤6 := by
    have p := natDegree_mul_le (p:=(X:K[X])) (q:=P)
    have p' := natDegree_mul_le (p:=(X:K[X])) (q:=X*P)
    rw [natDegree_X] at p p'
    have q := primitive_natDegree_le p
    have t := primitive_natDegree_le p'
    have v := natDegree_mul_le (p:=(X:K[X])) (q:=Q)
    rw [natDegree_X] at v
    change (X*Q-T).natDegree≤6
    have bq : Q.natDegree≤5 := q.trans (by omega)
    have bt : T.natDegree≤6 := t.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le (v.trans (by omega)) bt)
  have div0 : X^3∣F := by
    suffices hh : (X-C (0:K))^3∣F by simpa using hh
    apply (le_rootMultiplicity_iff Fne).mp
    apply lt_rootMultiplicity_of_isRoot_iterate_derivative Fne
    intro n hn
    rcases (show n=0 ∨ n=1 ∨ n=2 by omega) with rfl|rfl|rfl
    · simp [F,T,IsRoot.def,primitive_origin]
    · simp [dF,Q,IsRoot.def,primitive_origin]
    · simp [dF,dQ,IsRoot.def,Function.iterate_succ_apply']
  have doub (x : K) (h₁ : Q.eval x=0) (h₂ : T.eval x=0) : (X-C x)^2∣F := by
    apply (le_rootMultiplicity_iff Fne).mp
    apply (one_lt_rootMultiplicity_iff_isRoot Fne).mpr
    exact ⟨by simp [F,IsRoot.def,h₁,h₂],by simpa [dF,IsRoot.def] using h₁⟩
  have cop (x y : K) (hne : x≠y) : IsCoprime (X-C x) (X-C y) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
  have oc (x : K) (hn : x≠0) : IsCoprime (X:K[X]) (X-C x) := by
    simpa using cop 0 x hn.symm
  have left := ((oc u un).pow).mul_dvd div0 (doub u u1 u2)
  have all := ((oc v vn).pow.mul_left (cop u v sep).pow).mul_dvd left (doub v v1 v2)
  have degAll : (X^3*(X-C u)^2*(X-C v)^2 : K[X]).natDegree=7 := by
    have u0 := (monic_X_sub_C u).ne_zero
    have v0 := (monic_X_sub_C v).ne_zero
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ u0)) (pow_ne_zero _ v0),
      natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ u0),natDegree_pow,natDegree_pow,natDegree_pow,
      natDegree_X,natDegree_X_sub_C,natDegree_X_sub_C]
  exact Fne (eq_zero_of_dvd_of_natDegree_lt all (by omega))

/-- The first physical clean nonzero clock of a native cubic profile is
already a nonroot, its true diagonal vanishes, and both native primitive
tests are zero there. Neither unique clocks nor sign assumptions are made. -/
theorem dirk_C2_first_clean_clock (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (pay : 8≤p) (c₂ : monomialStageDefect A 1=0)
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ (monomialStageDefect A 2) (1+k))
    (P : K[X]) (nz : P≠0) (deg : P.natDegree≤3)
    (fit : ∀ i, monomialStageDefect A 2 i≠0 → monomialStageDefect A 2 i=P.eval (nodes A i)) :
    ∃ i, monomialStageDefect A 2 i=0 ∧ nodes A i≠0 ∧ P.eval (nodes A i)≠0 ∧ A i i=0 ∧
      (∀ j < i, monomialStageDefect A 2 j=0 → nodes A j=0) ∧
      (primitive (X*P)).eval (nodes A i)=0 ∧ (primitive (X*(X*P))).eval (nodes A i)=0 := by
  let w := monomialStageDefect A 2
  let c := nodes A
  let y := headInput A w (X*P) (-X)
  have yval (i : Fin s) : y i=c i*(P.eval (c i)-w i) := by
    simp only [y,headInput_apply,eval_mul,eval_X,eval_neg,c]
    ring
  have dy : (X*P).natDegree≤4 := natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  have dn : (-X:K[X]).natDegree≤1 := by simp
  obtain ⟨j,jw,jc,jP⟩ := dirk_C2_has_clean_nonroot ha ho pay c₂ P nz deg fit
  have yn : y≠0 := by
    intro h
    have z := congrFun h j
    have jw' : w j=0 := jw
    rw [yval,jw',sub_zero,Pi.zero_apply] at z
    exact mul_ne_zero jc jP z
  obtain ⟨i,iy,pre⟩ := first_nonzero yn
  have iw : w i=0 := by
    by_contra nw
    apply iy
    have val : w i=P.eval (c i) := fit i nw
    rw [yval,val,sub_self,mul_zero]
  have ci : c i≠0 := by
    intro z
    apply iy
    rw [yval,z,zero_mul]
  have Pi : P.eval (c i)≠0 := by
    intro z
    apply iy
    rw [yval,iw,z,sub_zero,mul_zero]
  have m : y∈treeSpace A 4 := headInput_mem_treeSpace (band 1 (by decide)) dy dn
  have v := volterra_treeSpace ho 4 (by omega) m
  have z := pure_head_zero_on_clean (band 3 (by decide)) v iw
  rw [volterra_pivot ha i y pre] at z
  have a0 : A i i=0 := sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp z).resolve_right iy))
  let Y := headInput A w (X*(X*P)) (-(X^2))
  have eqY : Y=diag c y := by
    ext t
    simp only [Y,yval,headInput_apply,eval_mul,eval_X,eval_neg,eval_pow,diag_apply,c]
    ring
  have dy' : (X*(X*P)).natDegree≤5 := natDegree_mul_le.trans (by rw [natDegree_X];omega)
  have dn' : (-(X^2):K[X]).natDegree≤2 := by simp
  obtain ⟨R,_,ay⟩ := headInput_mat (band 1 (by decide)) (band 2 (by decide)) dy dn
  obtain ⟨T,_,aY⟩ := headInput_mat (band 2 (by decide)) (band 3 (by decide)) dy' dn'
  change mat A y=headInput A w (primitive (X*P)) R at ay
  change mat A Y=headInput A w (primitive (X*(X*P))) T at aY
  have obs (t : Fin s) (ht : t ≤ i) (wt : w t=0) :
      (primitive (X*P)).eval (c t)=0 ∧ (primitive (X*(X*P))).eval (c t)=0 := by
    have vy : mat A y t=0 := by
      rw [mat_apply,lowerTriangular_mulVec_pivot ha t y (fun k hk => pre k (hk.trans_le ht))]
      rcases lt_or_eq_of_le ht with h|rfl
      · rw [pre _ h,mul_zero]
      · rw [a0,zero_mul]
    have vY : mat A Y t=0 := by
      rw [mat_apply,lowerTriangular_mulVec_pivot ha t Y (fun k hk => by simp [eqY,pre k (hk.trans_le ht)])]
      rcases lt_or_eq_of_le ht with h|rfl
      · simp [eqY,pre _ h]
      · rw [a0,zero_mul]
    rw [ay,headInput_apply,wt,mul_zero,add_zero] at vy
    rw [aY,headInput_apply,wt,mul_zero,add_zero] at vY
    exact ⟨vy,vY⟩
  refine ⟨i,iw,ci,Pi,a0,?_,(obs i le_rfl iw).1,(obs i le_rfl iw).2⟩
  intro t ht tw
  change w t=0 at tw
  by_contra tn
  change c t≠0 at tn
  have unlike : c t≠c i := by
    intro e
    exact Pi (e ▸ ((by simpa only [yval,tw,sub_zero] using pre t ht : c t*P.eval (c t)=0)
      |> fun h => (mul_eq_zero.mp h).resolve_left tn))
  exact two_clean_clocks_impossible P nz deg _ _ tn ci unlike
    (obs t ht.le tw).1 (obs t ht.le tw).2 (obs i le_rfl iw).1 (obs i le_rfl iw).2

end RKResearch.Certified.Graded.HeadFiber
