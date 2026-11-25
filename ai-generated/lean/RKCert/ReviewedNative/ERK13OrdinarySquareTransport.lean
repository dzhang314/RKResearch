module

public import RKCert.ReviewedNative.ERK13NativeFirstEscape
public import RKCert.ReviewedNative.NativeConsecutiveWeightX
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Literal order-13 clean-square transport. The nonzero-top branch only
returns clock invariance; its 14-class obstruction is a separate argument.
The directness and chart arguments use the actual original row spaces.
No eighth-clock hypothesis occurs in the factor recovery. -/
namespace RKResearch.Certified.Graded.ERK13OrdinarySquare
open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {U : Submodule K (Fin s→K)}
variable {w u v : Fin s→K} {G P Q R : K[X]}

private abbrev B (A : Matrix (Fin s) (Fin s) K)
    (U : Submodule K (Fin s→K)) (w : Fin s→K) (n : ℕ) :=
  chain (diag (nodes A)) U w n

private theorem band_rank_bound (n : ℕ) :
    finrank K (B A U w n)≤finrank K U+n := by
  induction n with
  | zero =>
    change finrank K U ≤ finrank K U + 0
    exact Nat.le_refl _
  | succ n ih =>
    by_cases paid : (diag (nodes A)^n) w∈B A U w n
    · have eq : B A U w (n+1)=B A U w n :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr paid)
      rw [eq]
      omega
    · change finrank K (↥(B A U w n ⊔ (K ∙ ((diag (nodes A)^n) w)) : Submodule K (Fin s → K))) ≤ _
      rw [Submodule.finrank_sup_span_singleton paid]
      omega

/-- The measured actual tree chart itself supplies directness against
every polynomial of degree ≤6: there is no assumed polynomial decoder. -/
theorem direct_polynomial_band {b : Fin s→K} (ho : HasOrder 13 A b) {j n : ℕ}
    (uRank : finrank K U=3)
    (chart : treeSpace A j=(coeffEval A 6).range⊔chain (diag (nodes A)) U w n)
    (rank : finrank K (treeSpace A j)=10+n) (H : K[X]) (hd : H.natDegree≤6)
    (hm : evalNodes A H∈chain (diag (nodes A)) U w n) : H=0 := by
  let C := (coeffEval A 6).range
  have cr : finrank K C≤7 := (LinearMap.finrank_range_le (coeffEval A 6)).trans_eq
    (Module.finrank_fin_fun K)
  have br := band_rank_bound (A:=A) (U:=U) (w:=w) n
  rw [uRank] at br
  have dim := Submodule.finrank_sup_add_finrank_inf_eq C (B A U w n)
  have eq : C⊔B A U w n=treeSpace A j := chart.symm
  rw [eq,rank] at dim
  have dis : C⊓B A U w n=⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have cp : evalNodes A H∈C := ⟨_,(evalNodes_eq_coeffEval A H hd).symm⟩
  have both : evalNodes A H∈C⊓B A U w n := ⟨cp,hm⟩
  rw [dis,Submodule.mem_bot] at both
  apply (PolySeparated.of_coeff (coeff_separated ho (q:=6) (by decide))) H hd
  rw [both]
  exact (zeroSpace A 6).zero_mem

/-- Extract the literal square and mesh polynomials from the actual
grade-eight direct-chart input. The degree-≤6 component is itself an
ordinary F8 defect because the entire five-term head has been paid. -/
theorem charts_of_paid_square
    (chart : treeSpace A 8=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 5)
    (bandPay : chain (diag (nodes A)) U w 5≤zeroSpace A 8)
    (squarePay : w*w∈zeroSpace A 8) (meshPay : evalNodes A G∈chain (diag (nodes A)) U w 4) :
    ∃ (P R Q : K[X]) (u v : Fin s→K), u∈U ∧ v∈U ∧
      P.natDegree≤6 ∧ R.natDegree≤4 ∧ Q.natDegree≤3 ∧ evalNodes A P∈zeroSpace A 8 ∧
      w*w=evalNodes A P+weightedEval (nodes A) w R+u ∧
      evalNodes A G=weightedEval (nodes A) w Q+v := by
  have sq := zeroSpace_le_treeSpace A 8 squarePay
  rw [chart] at sq
  obtain ⟨_,⟨a,rfl⟩,h,hh,eq⟩ := Submodule.mem_sup.mp sq
  let P := ofFn 7 a
  have pd : P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have pform : evalNodes A P=coeffEval A 6 a := by
    rw [evalNodes_eq_coeffEval A P pd]
    congr 1
    ext i
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  obtain ⟨u,hu,R,rd,hform⟩ := HeadFiber.exists_poly hh
  obtain ⟨v,hv,Q,qd,gform⟩ := HeadFiber.exists_poly meshPay
  have r4 : R.natDegree≤4 := by
    by_cases z : R=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr rd)
  have q3 : Q.natDegree≤3 := by
    by_cases z : Q=0
    · simp [z]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt z).mpr qd)
  have pp : evalNodes A P∈zeroSpace A 8 := by
    have m := (zeroSpace A 8).sub_mem squarePay (bandPay hh)
    rwa [←eq,←pform,add_sub_cancel_right] at m
  refine ⟨P,R,Q,u,v,hu,hv,pd,r4,q3,pp,?_,?_⟩
  · rw [←eq,←pform,hform]; abel
  · rw [gform,add_comm]

private theorem weighted_mono (n : ℕ) (a : K) :
    weightedEval (nodes A) w (monomial n a) = a • (diag (nodes A)^n) w := by
  ext i
  simp [HeadFiber.clock_power_value,mul_assoc]

private theorem weighted_in_band {Z : K[X]} {n : ℕ} (d : Z.natDegree<n) :
    weightedEval (nodes A) w Z∈B A U w n := by
  have inc := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) n).mp le_rfl
  rw [Z.as_sum_range' n d,map_sum]
  apply (B A U w n).sum_mem
  intro j hj
  rw [weighted_mono]
  exact (B A U w n).smul_mem _ (inc.2 j (Finset.mem_range.mp hj))

/-- A genuine degree-d clock polynomial advances an n-term head by at most d. -/
theorem polynomial_times_band {n d : ℕ} (pos : 0<n)
    (stable : U.map (diag (nodes A))≤U) {y : Fin s→K}
    (hy : y∈chain (diag (nodes A)) U w n) (Z : K[X]) (zd : Z.natDegree≤d) :
    evalNodes A Z*y∈chain (diag (nodes A)) U w (n+d) := by
  obtain ⟨h,hh,T,tb,form⟩ := HeadFiber.exists_poly hy
  have td : T.natDegree<n := by
    by_cases z : T=0
    · simpa only [z,natDegree_zero] using pos
    · exact (natDegree_lt_iff_degree_lt z).mpr tb
  have prod : (Z*T).natDegree<n+d := by
    have := natDegree_mul_le (p:=Z) (q:=T)
    omega
  have core := clock_function_mem
    (fun x (hx : x∈U) => stable (Submodule.mem_map_of_mem hx)) Z.eval hh
  have inc := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (n+d)).mp le_rfl
  have eq : evalNodes A Z*y =
      (fun i => Z.eval (nodes A i)*h i)+weightedEval (nodes A) w (Z*T) := by
    rw [form]
    ext i
    simp only [Pi.mul_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply,eval_mul]
    ring
  rw [eq]
  exact (B A U w (n+d)).add_mem (inc.1 core) (weighted_in_band prod)

/-- The clean square and paid mesh are multiplied on the original rows,
with the precise correction in the stable core. -/
theorem transport (stable : U.map (diag (nodes A))≤U)
    (off : ∀ i, (∃ h∈U,h i≠0) → w i=0) (hu : u∈U) (hv : v∈U)
    (square : w*w=evalNodes A P+weightedEval (nodes A) w R+u)
    (mesh : evalNodes A G=weightedEval (nodes A) w Q+v) :
    weightedEval (nodes A) w (G-R*Q)-evalNodes A (P*Q)∈U := by
  have keep := clock_function_mem
    (fun x (hx : x∈U) => stable (Submodule.mem_map_of_mem hx)) Q.eval hu
  have eq : weightedEval (nodes A) w (G-R*Q)-evalNodes A (P*Q) =
      (fun i => Q.eval (nodes A i)*u i) := by
    ext i
    have g := congrFun mesh i
    have h := congrFun square i
    simp only [evalNodes_apply,Pi.add_apply,weightedEval_apply] at g
    simp only [Pi.mul_apply,evalNodes_apply,Pi.add_apply,weightedEval_apply] at h
    have dis : v i*w i=0 := by
      by_cases vi : v i=0
      · rw [vi,zero_mul]
      · rw [off i ⟨v,hv,vi⟩,mul_zero]
    simp only [Pi.sub_apply,evalNodes_apply,weightedEval_apply,eval_sub,eval_mul]
    rw [g]
    calc
      _ = Q.eval (nodes A i)*(w i*w i-R.eval (nodes A i)*w i-P.eval (nodes A i))+
          v i*w i := by ring
      _ = _ := by rw [h,dis]; ring
  rwa [eq]

private theorem lower_top {D : K[X]} {n : ℕ} (degree : D.natDegree≤n+1)
    (top : D.coeff (n+1)=0) : D.natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  by_cases h : i=n+1
  · rwa [h]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

private theorem delta_cap (gd : G.natDegree=7) (rd : R.natDegree≤4)
    (qd : Q.natDegree≤3) : (G-R*Q).natDegree≤7 := by
  have prod := natDegree_mul_le (p:=R) (q:=Q)
  exact (natDegree_sub_le G (R*Q)).trans (max_le gd.le (by omega))

/-- A nonzero transported leading coefficient closes the *whole* actual
grade-ten tree chart under the clock. It does not assert a new rank at 11. -/
theorem clock_stable_of_top_ne (stable : U.map (diag (nodes A))≤U)
    (chart : treeSpace A 10=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 7)
    (gd : G.natDegree=7) (pd : P.natDegree≤6) (qd : Q.natDegree≤3) (rd : R.natDegree≤4)
    (law : weightedEval (nodes A) w (G-R*Q)-evalNodes A (P*Q)∈U)
    (nonzero : (G-R*Q).coeff 7≠0) :
    (treeSpace A 10).map (diag (nodes A))≤treeSpace A 10 := by
  let D := G-R*Q
  let a := D.coeff 7
  let L := D-monomial 7 a
  let E := treeSpace A 10
  have band : B A U w 7≤E := by rw [show E=treeSpace A 10 from rfl,chart]; exact le_sup_right
  have core : U≤B A U w 7 :=
    ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 7).mp le_rfl).1
  have bd : D.natDegree≤7 := delta_cap gd rd qd
  have lcap : L.natDegree≤7 := by
    have mono : (monomial 7 a).natDegree≤7 := natDegree_monomial_le a
    exact (natDegree_sub_le D _).trans (max_le bd mono)
  have ltop : L.coeff 7=0 := by simp [L,a,coeff_monomial]
  have ld : L.natDegree≤6 := lower_top (n:=6) lcap ltop
  have small : weightedEval (nodes A) w L∈E := band (weighted_in_band (by omega : L.natDegree<7))
  have pdq : (P*Q).natDegree≤9 := by
    have := natDegree_mul_le (p:=P) (q:=Q)
    omega
  have inP : evalNodes A (P*Q)∈E :=
    treeSpace_mono A (by decide : 9≤10) (evalNodes_mem_treeSpace A _ pdq)
  have wD : weightedEval (nodes A) w D∈E := by
    have h := E.add_mem (band (core law)) inP
    simpa only [D,sub_add_cancel] using h
  have top : a • (diag (nodes A)^7) w∈E := by
    have h := E.sub_mem wD small
    rw [←map_sub,show D-L=monomial 7 a by dsimp only [L]; abel,weighted_mono] at h
    exact h
  have last : (diag (nodes A)^7) w∈E :=
    (E.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nonzero)).mp top
  have in8 : B A U w 8≤E :=
    sup_le band ((Submodule.span_singleton_le_iff_mem ..).mpr last)
  have move : (B A U w 7).map (diag (nodes A))≤B A U w 8 :=
    le_sup_right.trans (clock_chain_next stable (by decide : 0<7)).le
  calc
    (treeSpace A 10).map (diag (nodes A)) =
      (coeffEval A 6).range.map (diag (nodes A))⊔(B A U w 7).map (diag (nodes A)) := by
        rw [chart,Submodule.map_sup]
    _ ≤ treeSpace A 10 := by
      refine sup_le ?_ (move.trans in8)
      rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
      exact treeSpace_mono A (by decide : 7≤10) (diag_treeSpace A 6 (coeffEval_mem_treeSpace A 6 t))

/-- The opposite (paid) top gives exact polynomial divisibility: a degree-≤6
Euclidean remainder belongs to B7, hence vanishes by E10's actual direct chart. -/
theorem mesh_dvd_square_times_q (stable : U.map (diag (nodes A))≤U)
    (low : ∀ H : K[X], H.natDegree≤6 → evalNodes A H∈chain (diag (nodes A)) U w 7 → H=0)
    (paid : evalNodes A G∈chain (diag (nodes A)) U w 4)
    (gd : G.natDegree=7) (pd : P.natDegree≤6) (qd : Q.natDegree≤3) (rd : R.natDegree≤4)
    (law : weightedEval (nodes A) w (G-R*Q)-evalNodes A (P*Q)∈U)
    (top : (G-R*Q).coeff 7=0) : G ∣ P*Q := by
  let H := (P*Q)/G
  let J := (P*Q)%G
  have ident : G*H+J=P*Q := EuclideanDomain.div_add_mod (P*Q) G
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have jd : J.natDegree≤6 := by
    have t := natDegree_mod_lt (P*Q) (q:=G) (by omega)
    change J.natDegree<G.natDegree at t
    omega
  have pq : (P*Q).natDegree≤9 := by have := natDegree_mul_le (p:=P) (q:=Q); omega
  have prod : G*H=P*Q-J := eq_sub_of_add_eq ident
  have und : (G*H).natDegree≤9 := by
    rw [prod]
    exact (natDegree_sub_le _ _).trans (max_le pq (by omega))
  have hd : H.natDegree≤2 := by
    by_cases z : H=0
    · simp [z]
    · rw [natDegree_mul gn z,gd] at und; omega
  have delta : (G-R*Q).natDegree≤6 := lower_top (n:=6) (delta_cap gd rd qd) top
  have wD : weightedEval (nodes A) w (G-R*Q)∈B A U w 7 := weighted_in_band (by omega)
  have core : U≤B A U w 7 :=
    ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 7).mp le_rfl).1
  have memPQ : evalNodes A (P*Q)∈B A U w 7 := by
    have t := (B A U w 7).sub_mem wD (core law)
    simpa only [sub_sub_cancel] using t
  have memGH : evalNodes A (G*H)∈B A U w 7 := by
    have h := polynomial_times_band (n:=4) (d:=2) (by decide) stable paid H hd
    have b67 : B A U w 6≤B A U w 7 := le_sup_left
    apply b67
    have e : evalNodes A H*evalNodes A G=evalNodes A (G*H) := by
      ext i; simp only [Pi.mul_apply,evalNodes_apply,eval_mul,mul_comm]
    rwa [e] at h
  have j0 : J=0 := by
    apply low J jd
    have j : J=P*Q-G*H := by rw [←ident]; abel
    rw [j,map_sub]
    exact (B A U w 7).sub_mem memPQ memGH
  exact ⟨H,by simpa only [j0,add_zero] using ident.symm⟩

/-- The remaining fraction obstruction runs on real HasOrder-13/F7/F8
data. Their actual moment budgets are six and five, respectively. -/
theorem zero_projection_of_divides {m : ℕ} {T : Matrix (Fin (m+1)) (Fin (m+1)) K}
    {b : Fin (m+1)→K} (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder 13 T b)
    (pPay : evalNodes T P∈zeroSpace T 8) (gPay : evalNodes T G∈zeroSpace T 7)
    (gd : G.natDegree=7) (pd : P.natDegree≤6) (qd : Q.natDegree≤3) (qn : Q≠0)
    (divides : G ∣ P*Q) : P=0 := by
  by_contra pn
  have c0 : nodes T (0:Fin (m+1))=0 := by
    change (∑ j,T 0 j*1)=0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have p0 : P.eval 0=0 := by
    have h := origin_zeroSpace ha 8 pPay
    change P.eval (nodes T (0:Fin (m+1)))=0 at h
    rwa [c0] at h
  have g0 : G.eval 0=0 := by
    have h := origin_zeroSpace ha 7 gPay
    change G.eval (nodes T (0:Fin (m+1)))=0 at h
    rwa [c0] at h
  obtain ⟨V,hV⟩ : (X:K[X]) ∣ P := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
  obtain ⟨W,hW⟩ : (X:K[X]) ∣ G := by simpa using (dvd_iff_isRoot (a:=(0:K))).mpr g0
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have vn : V≠0 := fun z => pn (by rw [hV,z,mul_zero])
  have wn : W≠0 := fun z => gn (by rw [hW,z,mul_zero])
  have vp (k : ℕ) (hk : k<5) : NativeConsecutiveWeightX.moment k V=0 := by
    have e := (probe_evalNodes ho P k (by omega)).symm.trans
      (probe_zeroSpace (k:=k) ho (by omega) pPay)
    change (primitive (((X:K[X])^k*X)*V)).eval 1=0
    simpa only [hV,mul_assoc] using e
  have wp (k : ℕ) (hk : k<6) : NativeConsecutiveWeightX.moment k W=0 := by
    have e := (probe_evalNodes ho G k (by omega)).symm.trans
      (probe_zeroSpace (k:=k) ho (by omega) gPay)
    change (primitive (((X:K[X])^k*X)*W)).eval 1=0
    simpa only [hW,mul_assoc] using e
  have vd : V.natDegree=5 := by
    rw [hV,natDegree_X_mul vn] at pd
    by_contra ne
    apply vn
    apply NativeMoments.x_moments_detect (n:=4) (by omega)
    intro i
    have e := vp i.val i.isLt
    change (primitive (((X:K[X])^i.val*X)*V)).eval 1=0 at e
    simpa only [mul_assoc] using e
  have wd : W.natDegree=6 := by rw [hW,natDegree_X_mul wn] at gd; omega
  obtain ⟨H,dH⟩ := divides
  have raw : (X:K[X])*(V*Q)=X*(W*H) := by simpa only [hV,hW,mul_assoc] using dH
  exact NativeConsecutiveWeightX.square_divisor_impossible V W Q vd wd qd qn vp wp
    ⟨H,mul_left_cancel₀ X_ne_zero raw⟩

/-- Once the top and the degree-six projection vanish, *seven* original
head clocks suffice. The top cancellation was earned before interpolation. -/
theorem factor_on_seven (off : ∀ i, (∃ h∈U,h i≠0) → w i=0) (hu : u∈U) (hv : v∈U)
    (square : w*w=weightedEval (nodes A) w R+u)
    (mesh : evalNodes A G=weightedEval (nodes A) w Q+v)
    (gd : G.natDegree=7) (qd : Q.natDegree≤3) (rd : R.natDegree≤4)
    (top : (G-R*Q).coeff 7=0) (sites : 7≤(HeadFiber.physicalSites (nodes A) w).card) :
    R.natDegree=4 ∧ Q.natDegree=3 ∧ G=R*Q ∧ ∀ i, w i≠0 → w i=R.eval (nodes A i) := by
  have dead (i : Fin s) (wi : w i≠0) (h : Fin s→K) (hh : h∈U) : h i=0 := by
    by_contra nz
    exact wi (off i ⟨h,hh,nz⟩)
  have repr (i : Fin s) (wi : w i≠0) : w i=R.eval (nodes A i) := by
    have h := congrFun square i
    simp only [Pi.mul_apply,Pi.add_apply,weightedEval_apply,dead i wi u hu,add_zero] at h
    exact mul_right_cancel₀ wi h
  have delta : (G-R*Q).natDegree≤6 := lower_top (n:=6) (delta_cap gd rd qd) top
  have eq : G-R*Q=0 := by
    apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (HeadFiber.physicalSites (nodes A) w)
      (degree_le_natDegree.trans_lt (by exact_mod_cast (show (G-R*Q).natDegree<
        (HeadFiber.physicalSites (nodes A) w).card by omega)))
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have wi := (Finset.mem_filter.mp hi).2
    have g := congrFun mesh i
    simp only [evalNodes_apply,Pi.add_apply,weightedEval_apply,dead i wi v hv,add_zero] at g
    rw [eval_sub,eval_mul,g,repr i wi]
    ring
  have fit := sub_eq_zero.mp eq
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at gd; omega
  have rn : R≠0 := fun z => gn (by rw [fit,z,zero_mul])
  have qn : Q≠0 := fun z => gn (by rw [fit,z,mul_zero])
  rw [fit,natDegree_mul rn qn] at gd
  exact ⟨by omega,by omega,fit,repr⟩

end
end RKResearch.Certified.Graded.ERK13OrdinarySquare
