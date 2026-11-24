module
public import RKCert.TableauHermiteGain
public import RKCert.HeadChart
public import RKCert.EndpointPhysical
public import RKCert.EndpointJacobi

@[expose] public section
namespace RKCert.Endpoint
open RKCert.Paired Polynomial
open scoped Classical
variable {K : Type*} [Field K] {s p : ℕ}

/-- The first failure of a global chronological match is a genuine failure
in its own numerical block. One mask patches an alleged matching last block. -/
theorem first_unmatched_block (c z : Fin s → K) (U : Submodule K (Fin s → K))
    (hU : MaskInvariant c U) (hout : z∉U) :
    ∃ (k : Fin s) (w : Fin s → K), w∈U ∧ (∀ i : Fin s, i<k → w i=z i) ∧
      ¬ blockMatch c z U (c k) (k.val+1) := by
  classical
  let M (n : ℕ) := ∃ w∈U, ∀i : Fin s, i.val<n → w i=z i
  have hex : ∃ n : ℕ, ¬M n := by
    refine ⟨s,fun ⟨w,hw,he⟩ => hout ?_⟩
    have eq : w=z := funext (fun i => he i i.isLt)
    rwa [← eq]
  let n := Nat.find hex
  have hn : ¬M n := Nat.find_spec hex
  have ns : n≤s := by
    apply Nat.find_min' hex
    rintro ⟨w,hw,he⟩
    have eq : w=z := funext (fun i => he i i.isLt)
    exact hout (eq ▸ hw)
  have hnpos : 0<n := by
    by_contra! hn0
    have he : n=0 := by omega
    apply hn
    exact ⟨0,U.zero_mem,fun i hi => False.elim (by omega)⟩
  let k : Fin s := ⟨n-1,by omega⟩
  have hk : k.val+1=n := by dsimp [k]; omega
  obtain ⟨w,hw,hwk⟩ := (not_not.mp (Nat.find_min hex (by omega : k.val<n)) : M k.val)
  refine ⟨k,w,hw,hwk,fun ⟨t,ht,htk⟩ => hn ?_⟩
  let y := w + blockMask c (c k) (t-w)
  refine ⟨y,U.add_mem hw (hU _ _ (U.sub_mem ht hw)),?_⟩
  intro i hi
  by_cases hn' : c i=c k
  · simp [y,blockMask,hn',htk i (by omega) hn']
  · have hp : i.val<k.val := by
      by_contra! hp
      have hi' : i=k := Fin.ext (by omega)
      exact hn' (congrArg c hi')
    simp [y,blockMask,hn',hwk i hp]

variable [CharZero K]

omit [CharZero K] in
/-- A genuine clock-polynomial product raises the grade of the head by the
degree of its multiplier, as long as the tree normalization budget is paid. -/
private theorem weightedGrade {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {j : ℕ} {w : Vec K s} (hw : w∈zeroSpace A j)
    (R : K[X]) (hR : R.natDegree+1≤p) :
    weightedEval (nodes A) w R ∈ zeroSpace A (j+R.natDegree) := by
  have he : weightedEval (nodes A) w R = w*evalNodes A R := by ext i; simp [mul_comm]
  rw [he]
  exact zeroSpace_mul_treeSpace ho hR hw (evalNodes_mem_treeSpace A R le_rfl)

/-- A real physical contrast is produced from a compatible one-head chart,
not supplied as an additional hypothesis. For every test R in the budget,
the same chronological failure knot annihilates the formal primitive RQP. -/
theorem head_contrast_at_physical_row {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {j H n : ℕ}
    (hHp : H+1≤p) (hsep : Separated A H)
    (U : Submodule K (Vec K s)) (hUF : U≤zeroSpace A j)
    (hC : ∀ v∈U,diag (nodes A) v∈U)
    (w : Vec K s) (hw : w∈zeroSpace A j)
    (hchart : zeroSpace A H ≤ OneEscape.chain (diag (nodes A)) U w n)
    (hdis : ∀ v∈U, ∀ i : Fin s, w i≠0 → v i=0)
    (P : K[X]) (hP : P≠0) (hdeg : P.natDegree≤j)
    (hhead : ∀ i : Fin s, w i≠0 → w i=P.eval (nodes A i))
    (Q : K[X]) (hQ : Q≠0) (hq : j+Q.natDegree≤H) :
    ∃ k : Fin s, (Q*P).eval (nodes A k)≠0 ∧
      ∀ R : K[X], j+Q.natDegree+R.natDegree+1≤H →
          (Paired.primitive (R*(Q*P))).eval (nodes A k)=0 := by
  let c := nodes A
  let z := evalNodes A (Q*P) - weightedEval c w Q
  have zval (i : Fin s) : z i=(Q*P).eval (c i)-Q.eval (c i)*w i := by simp [z,c]
  have zon (i : Fin s) (hi : w i≠0) : z i=0 := by
    rw [zval,eval_mul,hhead i hi]; exact sub_self _
  have hzout : z∉U := by
    intro hz
    have hqstage : weightedEval c w Q ∈ zeroSpace A H :=
      zeroSpace_mono A hq (weightedGrade ho hw Q (by omega))
    have hs := (zeroSpace A H).add_mem (zeroSpace_mono A (show j≤H by omega) (hUF hz)) hqstage
    have hpq : Q*P=0 := hsep _ ((natDegree_mul_le (p:=Q) (q:=P)).trans (by omega)) (by
      simpa only [z,sub_add_cancel] using hs)
    exact mul_ne_zero hQ hP hpq
  obtain ⟨k,v,hv,hprev,hbad⟩ := first_unmatched_block c z U (maskInvariant_of_diag hC) hzout
  have hn : (Q*P).eval (c k)≠0 := by
    intro hzero
    apply hbad
    refine ⟨0,U.zero_mem,fun i _ hci => ?_⟩
    by_cases hw0 : w i=0
    · simp [zval,hci,hzero,hw0]
    · simp [zon i hw0]
  refine ⟨k,hn,fun R hbudget => ?_⟩
  let T := R*(Q*P)
  let F := Paired.primitive T
  let m := H-1
  have hm : m+1=H := by dsimp [m]; omega
  have dt : T.natDegree≤m := by
    have h1 := natDegree_mul_le (p:=R) (q:=Q*P)
    have h2 := natDegree_mul_le (p:=Q) (q:=P)
    dsimp [T,m]; omega
  have drq := natDegree_mul_le (p:=R) (q:=Q)
  let hrem := weightedEval c v R + weightedEval c w (R*Q)
  have hre : hrem ∈ zeroSpace A m := by
    have hvR : weightedEval c v R ∈ U := by
      have he : weightedEval c v R = (fun i => R.eval (c i)*v i) := by ext i; simp
      rw [he]; exact mulByBlock_mem _ (maskInvariant_of_diag hC) (fun a => R.eval a) hv
    exact (zeroSpace A m).add_mem (zeroSpace_mono A (by dsimp [m]; omega) (hUF hvR))
      (zeroSpace_mono A (by dsimp [m]; omega) (weightedGrade ho hw _ (by omega)))
  let y := evalNodes A F - mat A (evalNodes A T) + mat A hrem
  have hY : y∈zeroSpace A H := by
    rw [←hm]
    exact (zeroSpace A (m+1)).add_mem
      (by simpa only [neg_sub] using (zeroSpace A (m+1)).neg_mem (primitive_defect A T dt))
      (mat_zeroSpace_charZero A m hre)
  have pre (i : Fin s) (hi : i.val<k.val+1) : y i=F.eval (c i) := by
    have eq : mat A (evalNodes A T) i=mat A hrem i := by
      apply strictlyCausal_mat ha
      intro l hl
      have hlk : l<k := by change l.val < i.val at hl; change l.val<k.val; omega
      change T.eval (c l)=weightedEval c v R l+weightedEval c w (R*Q) l
      rw [weightedEval_apply,weightedEval_apply,hprev l hlk,zval]
      simp only [T,eval_mul]; ring
    change F.eval (c i) - mat A (evalNodes A T) i + mat A hrem i=_
    rw [eq,sub_add_cancel]
  obtain ⟨u,hu,B,_,be⟩ := Clock.exists_head_poly (hchart hY)
  by_contra hne
  have hF : F.eval (c k) ≠ 0 := hne
  apply hbad
  let d := (Q*P).eval (c k) / F.eval (c k)
  refine ⟨d • u,U.smul_mem _ hu,fun i hi hci => ?_⟩
  change d*u i=z i
  by_cases hwi : w i=0
  · have e : u i=F.eval (c k) := by
      have he := be i
      rw [pre i hi,hwi,mul_zero,add_zero,hci] at he
      exact he.symm
    rw [e,zval,hwi,mul_zero,sub_zero,hci]
    exact div_mul_cancel₀ _ hF
  · rw [hdis u hu i hwi,mul_zero,zon i hwi]

/-- Actual native polynomial primitive in the same normalization as the finite endpoint sums. -/
theorem primitive_monomial_moment {n : ℕ} (e : Fin n → K) (x : K) (k : ℕ) :
    (Paired.primitive (X^k*ofFn n e)).eval x=moment e x k := by
  rw [ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t _
  rw [X_pow_mul_monomial,primitive_monomial,eval_monomial]
  ring

/-- The generic algebraic Jacobi gate at arbitrary physical knots, without
silently replacing the two endpoints by a positive ordered interval. -/
theorem physical_jacobi_gate {m : ℕ} (hm : 4≤m) (e : Fin (m+1) → K)
    (u v : K) (hu : u≠0) (hv : v≠0) (hvu : v≠u)
    (h1 : ∀ k : Fin m,moment e u (k.val+1)=0)
    (h2 : ∀ k : Fin 3,moment e v (k.val+2)=u*moment e v (k.val+1)) : e=0 := by
  let f := EndpointPhysical.rescale e u
  apply (EndpointPhysical.rescale_eq_zero_iff e hu).mp
  apply twoEndpointJacobi hm _ (v/u) (div_ne_zero hv hu) (fun h => hvu ((div_eq_one_iff_eq hu).mp h))
  · intro k
    have h := EndpointPhysical.moment_rescale e u 1 (k.val+1)
    rw [mul_one,h1 k] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hu)
  · intro k
    have vu : u*(v/u)=v := by field_simp
    have scale (t : ℕ) : moment e v t=u^(t+1)*moment f (v/u) t := by
      simpa only [vu] using EndpointPhysical.moment_rescale e u (v/u) t
    have h := h2 k
    rw [scale,scale,pow_succ u (k.val+2)] at h
    have hz : (u^(k.val+2)*u)*(moment f (v/u) (k.val+2)-moment f (v/u) (k.val+1))=0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero (pow_ne_zero _ hu) hu))

/-- A disjoint short polynomial head is IMPOSSIBLE in a doubling band of
the actual tableau: both noncoincident contrast knots and every required
primitive test are extracted on physical rows before the scalar gate is used. -/
theorem no_disjoint_polynomial_head_doubling {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {m n : ℕ} (hm : 4≤m)
    (hHp : 2*(m+1)+1≤p) (hsep : Separated A (2*(m+1)))
    (U : Submodule K (Vec K s)) (hUF : U≤zeroSpace A (m+1)) (hC : ∀ v∈U,diag (nodes A) v∈U)
    (w : Vec K s) (hw : w∈zeroSpace A (m+1))
    (hchart : zeroSpace A (2*(m+1)) ≤ OneEscape.chain (diag (nodes A)) U w n)
    (hdis : ∀ v∈U, ∀ i : Fin s, w i≠0 → v i=0)
    (P : K[X]) (hP : P≠0) (hdeg : P.natDegree≤m)
    (hhead : ∀ i : Fin s, w i≠0 → w i=P.eval (nodes A i)) : False := by
  classical
  have H := head_contrast_at_physical_row ha ho hHp hsep U hUF hC w hw hchart hdis P hP
    (show P.natDegree≤m+1 by omega) hhead
  obtain ⟨i,hi,hfirst⟩ := H X X_ne_zero (by rw [natDegree_X]; omega)
  let u := nodes A i
  have hu : u≠0 := fun h => hi (by simp [eval_mul,show nodes A i=0 from h])
  let Q : K[X] := X*(X-C u)
  have hQ : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have dq : Q.natDegree=2 := by
    dsimp only [Q]; rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨l,hl,hsecond⟩ := H Q hQ (by rw [dq]; omega)
  let v := nodes A l
  have hv : v≠0 := fun h => hl (by simp [Q,eval_mul,show nodes A l=0 from h])
  have hvu : v≠u := fun h => hl (by simp [Q,eval_mul,show nodes A l=u from h])
  let e := toFn (m+1) P
  have rep : ofFn (m+1) e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have zero := physical_jacobi_gate hm e u v hu hv hvu (fun k => ?_) (fun k => ?_)
  · apply hP
    rw [←rep,zero,map_zero]
  · have he := hfirst (X^k.val) (by rw [natDegree_X,natDegree_X_pow]; have := k.isLt; omega)
    have eq : X^k.val * (X*P) = X^(k.val+1)*P := by ring
    rw [eq,←rep,primitive_monomial_moment] at he
    exact he
  · have he := hsecond (X^k.val) (by rw [dq,natDegree_X_pow]; have := k.isLt; omega)
    have eq : X^k.val * (Q*P) = X^(k.val+2)*P - u • (X^(k.val+1)*P) := by
      rw [Polynomial.smul_eq_C_mul]; dsimp only [Q]; ring
    rw [eq,←rep,map_sub,map_smul,eval_sub,eval_smul,primitive_monomial_moment,primitive_monomial_moment] at he
    exact sub_eq_zero.mp he

end RKCert.Endpoint
