module
public import RKCert.ERKOrder13Chart
public import RKCert.ERKFiniteGhost
public import RKCert.OrderedIntervalMoments

@[expose] public section

/-! # Exact first full-odd pure band and degree-eight leakage -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [CharZero K] {s a d r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1600000

omit [CharZero K] in
theorem band13_next (C:Chart13 A d a r U w G) {j:ℕ} (hj:a+1≤j) :
    Band13 A a r U w j⊔(Band13 A a r U w j).map (diag (nodes A))=Band13 A a r U w (j+1) := by
  have e : headLen 6 a r (j+1)=headLen 6 a r j+1 := by unfold headLen;omega
  unfold Band13 forwardBand
  rw [e]
  exact chain_sup_map C.marked.stable (by unfold headLen;omega)

omit [CharZero K] in
theorem firstEscape_band13 (C:Chart13 A d a r U w G) (j:ℕ) :
    firstEscape A d 6≤Band13 A a r U w j := by
  unfold Band13 forwardBand headLen
  rw [C.marked.edge]
  have h:U≤chain (diag (nodes A)) U w (r+(6-4)+(j-(a+1))) ∧
         ∀k<r+(6-4)+(j-(a+1)),(diag (nodes A)^k) w∈chain (diag (nodes A)) U w (r+(6-4)+(j-(a+1))) :=
      (chain_le_iff _).mp le_rfl
  exact (chain_le_iff _).mpr ⟨h.1,fun k hk=>h.2 k (by omega)⟩

omit [CharZero K] in
theorem band13_separation (S:Saturated A b 6 1) (M:Margin A b 6 1 d)
    (C:Chart13 A d a r U w G) {j:ℕ} (hj:a+1≤j) (hmax:j≤10)
    (P:K[X]) (hp:P.natDegree≤a) (hm:evalNodes A P∈Band13 A a r U w j) : P=0 := by
  classical
  have wdt:=C.width
  have hinj : Function.Injective (polyEval A a) := (injective_iff_map_eq_zero _).mpr fun v hz=>by
    have hv : (ofFn (a+1) v).natDegree≤6 := by have := ofFn_natDegree_lt (show 1≤a+1 by omega) v;omega
    have vp : ofFn (a+1) v=0 :=
      separated_plus S M _ hv (by rw [evalNodes_ofFn A a v,hz];exact (defectPlus A d 6).zero_mem)
    ext i
    have eq:=congrArg (fun P:K[X]=>P.coeff i.val) vp
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at eq
  have pr : finrank K (polyBand A a)=a+1 := by unfold polyBand;rw [LinearMap.finrank_range_of_inj hinj];simp
  let Z:=Band13 A a r U w j
  have cap : finrank K Z≤finrank K U+headLen 6 a r j := RKCert.Paired.OrderTwelve.chain_rank_cap _
  have sm := Submodule.finrank_sup_add_finrank_inf_eq (polyBand A a) Z
  have eq := C.chart j hj hmax
  change treePlus A d j=polyBand A a⊔Z at eq
  rw [←eq,C.rich j hj hmax,pr] at sm
  have z : finrank K ↥(polyBand A a⊓Z)=0 := by have := C.marked.rank;unfold headLen at cap;omega
  have z' := Submodule.finrank_eq_zero.mp z
  have out : evalNodes A P=0 := (Submodule.mem_bot K).mp (z' ▸ Submodule.mem_inf.mpr ⟨eval_polyBand hp,hm⟩)
  exact separated_plus S M P (by omega) (by rw [out];exact (defectPlus A d 6).zero_mem)

omit [CharZero K] in
theorem order13_full_exact_F7 [LinearOrder K] [IsStrictOrderedRing K] (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b 13) (C:Chart13 A 0 6 r U w G) :
    zeroSpace A 7=Band13 A 6 r U w 7 := by
  classical
  have hb : Band13 A 6 r U w 7≤zeroSpace A 7 := fun _ hv=>tail_zero_iff.mp (band13_paid C (by decide) hv)
  apply le_antisymm _ hb
  intro u hu
  have hTree : u∈treePlus A 0 7 := (show treeSpace A 7≤treePlus A 0 7 from le_sup_left)
    (zeroSpace_le_treeSpace A 7 hu)
  rw [C.chart 7 (by decide) (by decide)] at hTree
  obtain ⟨v,⟨a,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hTree
  let P:=ofFn 7 a
  have hd:P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev:evalNodes A P=polyEval A 6 a := evalNodes_ofFn A 6 a
  have hP : evalNodes A P∈zeroSpace A 7 := by
    rw [ev,show polyEval A 6 a=u-z by rw [←eq];abel]
    exact (zeroSpace A 7).sub_mem hu (hb hz)
  have hzP:=RKCert.OrderedGram.ordered_anchored_separation ha ho P (by omega) (by omega) hP
  have zz : (0:Vec K (s+1))=polyEval A 6 a := by
    rw [←ev,hzP]
    ext i
    simp only [Pi.zero_apply,evalNodes_apply,eval_zero]
  rwa [←eq,←zz,zero_add]

theorem full13_decompose (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (C:Chart13 A 0 6 r U w G) {v:Vec K (s+1)}
    (hv:v∈zeroSpace A 8) :
    ∃ P:K[X],P.natDegree≤6∧(∃ t:K,P=t•odd5)∧ v-evalNodes A P∈Band13 A 6 r U w 8 := by
  classical
  have hE : v∈treePlus A 0 8 :=
    (show treeSpace A 8≤treePlus A 0 8 from le_sup_left) (zeroSpace_le_treeSpace A 8 hv)
  rw [C.chart 8 (by decide) (by decide)] at hE
  obtain ⟨p,⟨c,rfl⟩,z,hz,eq⟩:=Submodule.mem_sup.mp hE
  let P:=ofFn 7 c
  have pd:P.natDegree≤6:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have ev:evalNodes A P=polyEval A 6 c:=evalNodes_ofFn A 6 c
  have hPaid : evalNodes A P∈defectPlus A 0 8 := by
    rw [ev,show polyEval A 6 c=v-z by rw [←eq];abel]
    exact Submodule.sub_mem _ (tail_zero_iff.mpr hv) (band13_paid C (by decide) hz)
  have hP0:=marked_eval_origin ha (by have:=S.size;omega) P hPaid
  have hForm:=ghost13Full_decode P pd hP0 (fun k=>marked_moment_zero ho P hPaid (by omega) (by have:=k.isLt;omega))
  exact ⟨P,pd,hForm,by rw [ev,←eq];simpa only [add_sub_cancel_left] using hz⟩


omit [CharZero K] in
theorem band13_modulo_mesh (S:Saturated A b 6 1) (M:Margin A b 6 1 d)
    (C:Chart13 A d a r U w G) (j:ℕ) (hj:a+1≤j) (hmax:j≤10)
    (P:K[X]) (pD:P.natDegree≤a+1) (hP:evalNodes A P∈Band13 A a r U w j) :
    ∃ t:K,P=t•G := by
  have ng : G.coeff (a+1)≠0 := by
    rw [←C.meshDegree,coeff_natDegree,leadingCoeff_ne_zero]
    intro h
    have e:=C.meshDegree
    rw [h,natDegree_zero] at e
    omega
  let t := P.coeff (a+1)/G.coeff (a+1)
  let R:=P-t•G
  have rd:R.natDegree≤a := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    change (P-t•G).coeff i=0
    rw [coeff_sub,AddMonoidAlgebra.coeff_smul_apply,smul_eq_mul]
    by_cases h:i=a+1
    · subst i;unfold t;rw [div_mul_cancel₀ _ ng,sub_self]
    · have P0 := coeff_eq_zero_of_natDegree_lt (p:=P) (n:=i) (by omega)
      have G0 := coeff_eq_zero_of_natDegree_lt (p:=G) (n:=i) (by have := C.meshDegree;omega)
      rw [P0,G0,mul_zero,sub_self]
  have gb := firstEscape_band13 C j C.meshPaid
  have hm : evalNodes A R∈Band13 A a r U w j := by
    have e:evalNodes A R=evalNodes A P-t•evalNodes A G := by ext i;simp [R,evalNodes,eval_smul]
    rw [e]
    exact Submodule.sub_mem _ hP (Submodule.smul_mem _ _ gb)
  exact ⟨t,sub_eq_zero.mp (band13_separation S M C hj hmax R rd hm)⟩

omit [CharZero K] in
theorem band13_polynomial_shift (S:Saturated A b 6 1) (M:Margin A b 6 1 d)
    (C:Chart13 A d a r U w G) {P Q:K[X]} {v:Vec K (s+1)}
    {j:ℕ} (hj:a+1≤j) (hmax:j+1≤10)
    (dp:P.natDegree≤a) (dq:Q.natDegree≤a)
    (hp:v-evalNodes A P∈Band13 A a r U w j)
    (hq:diag (nodes A) v-evalNodes A Q∈Band13 A a r U w j) :
    ∃ t:K,X*P-Q=t•G := by
  let D:=diag (nodes A)
  let B:=Band13 A a r U w j
  let W:=Band13 A a r U w (j+1)
  have he:B⊔B.map D=W := band13_next C hj
  have m1 : D (v-evalNodes A P)∈W := by
    rw [←he]
    exact (show B.map D≤B⊔B.map D from le_sup_right) (Submodule.mem_map_of_mem hp)
  have m2 : D v-evalNodes A Q∈W := by
    rw [←he]
    exact (show B≤B⊔B.map D from le_sup_left) hq
  have hmem := W.sub_mem m2 m1
  rw [map_sub,show D v-evalNodes A Q-(D v-D (evalNodes A P))=
        D (evalNodes A P)-evalNodes A Q by abel] at hmem
  have e : evalNodes A (X*P-Q)=D (evalNodes A P)-evalNodes A Q := by ext i;simp [D,evalNodes]
  apply band13_modulo_mesh S M C (j+1) (by omega) hmax _ (diff_clock_degree P Q a dp dq)
  rwa [e]

theorem order13_full_no_leak (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G) {v:Vec K (s+1)}
    (pv:v∈zeroSpace A 8) (cv:diag (nodes A) v∈zeroSpace A 8) :
    v∈Band13 A 6 r U w 8 ∧ diag (nodes A) v∈Band13 A 6 r U w 8 := by
  obtain ⟨P,dP,⟨x,eP⟩,p0⟩:=full13_decompose ha ho S C pv
  obtain ⟨Q,dQ,⟨y,eQ⟩,q0⟩:=full13_decompose ha ho S C cv
  obtain ⟨t,e⟩:=band13_polynomial_shift S M C (by decide) (by decide) dP dQ p0 q0
  have hx : x=0 := by
    cases C.mesh with
    | full v eG =>
      rw [eP,eQ,eG,smul_smul] at e
      exact shift13Full x y (t*v) e
  have P0 : P=0 := by rw [eP,hx,zero_smul]
  have Q0 : Q=0 := by
    by_contra Qn
    have ee : -Q=t•G := by simpa only [P0,mul_zero,zero_sub] using e
    have n : (-Q).natDegree=G.natDegree := mesh_line_degree ee (neg_ne_zero.mpr Qn)
    rw [natDegree_neg,C.meshDegree] at n
    omega
  have zz : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp only [evalNodes_apply,eval_zero,Pi.zero_apply]
  exact ⟨by simpa only [P0,zz,sub_zero] using p0,by simpa only [Q0,zz,sub_zero] using q0⟩

end RKCert.Paired.FiniteMidpoint

