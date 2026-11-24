module
public import RKCert.ReviewedNative.ERKOrder13PaidFrame
public import RKCert.ReviewedNative.OrderNineMultiScalar
public import RKCert.ERKOrder13Packets
public import RKCert.ERKFiniteMesh

@[expose] public section

/-! # Exact order-thirteen forward mesh, with the scalar decoder separated.
The imported packet sees only a polynomial, its origin coefficient, and
six vanishing or five adjacent primitive moments. It never sees a tableau. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial
open RKCert.Paired.FiniteMidpoint (dx5 dx6 odd6 dx5_degree dx6_degree odd6_degree
  scalarMoment mesh13Full_decode mesh13Prefix_decode)
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

inductive Order13Mesh (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K) (P : K[X]) : Prop
  | ordinary (first : firstSeed A b≠0) (a : K) (eq : P=a • odd6)
  | marked (first : firstSeed A b=0) (a t : K) (eq : P=a • dx5+t • dx6)

variable [CharZero K]

/-- Actual paid data fed to the checked rational packet. The constant
probe is refunded only in the truly marked branch. -/
theorem order13_paid_mesh (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    (F : Order13PaidFrame A b) (P : K[X]) (pd : P.natDegree≤7)
    (hp : evalNodes A P∈order13FirstEscape A b) : Order13Mesh A b P := by
  have m := F.escapePaid hp
  have origin := origin_marked_defect ha (j:=7) (by decide : 0<18) m
  have zero : P.coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero]
    have c0 : nodes A (0:Fin 19)=0 := by
      change (∑ j,A 0 j * 1)=0
      exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
    simpa only [evalNodes_apply,c0] using origin
  have eq (k : ℕ) (pay : k≤5) : scalarMoment P k=probe A b k (evalNodes A P) := by
    rw [scalarMoment,MultiOff.scalar_primitive,probe_evalNodes ho P k (by omega)]
  by_cases first : firstSeed A b=0
  · obtain ⟨a,t,h⟩ := mesh13Prefix_decode P pd zero (fun k=>by
      rw [eq _ (by have := k.isLt; omega),eq _ (by have := k.isLt; omega),
        paid_probe_marked_defect ha ho F.lastActive m k.val (by have := k.isLt;omega),
        paid_probe_marked_defect ha ho F.lastActive m (k.val+1) (by have := k.isLt;omega),sub_self])
    exact .marked first a t h
  · have u : evalNodes A P∈zeroSpace A 7 := by
      simpa only [markedDefectSpace,terminalMark,ite_eq_right first,sup_bot_eq] using m
    obtain ⟨a,h⟩ := mesh13Full_decode P pd zero (fun k=>by
      rw [eq _ (by have := k.isLt;omega)]
      exact probe_zeroSpace ho (by have := k.isLt;omega) u)
    exact .ordinary first a h

theorem order13_mesh_alias {P : K[X]} (M : Order13Mesh A b P)
    (small : P.natDegree≤6) (pn : P≠0) : firstSeed A b=0 ∧ P.natDegree=6 := by
  cases M with
  | ordinary first a eq =>
    have d := (RKCert.Paired.FiniteMidpoint.mesh_line_degree eq pn).trans odd6_degree
    omega
  | marked first a t eq =>
    exact ⟨first,(RKCert.Paired.FiniteMidpoint.mesh_span_degree eq
      (by rw [dx5_degree,dx6_degree];decide) (by rwa [dx5_degree]) pn).trans dx5_degree⟩

omit [CharZero K] in
private theorem pol_band_in_marked_tree {a j : ℕ} (le : a≤j) :
    (coeffEval A a).range ≤ markedTreeSpace A b j := by
  rintro _ ⟨t,rfl⟩
  exact (show treeSpace A j≤markedTreeSpace A b j from le_sup_left)
    (treeSpace_mono A le (coeffEval_mem_treeSpace A a t))

omit [CharZero K] in
private theorem coeff_of_poly_sep {a : ℕ} {V : Submodule K (Fin 19→K)}
    (sep : ∀ P : K[X],P.natDegree≤a → evalNodes A P∈V → P=0)
    (x : Fin (a+1)→K) (h : coeffEval A a x∈V) : x=0 := by
  apply injective_ofFn (a+1)
  rw [ofFn_zero]
  exact sep (ofFn (a+1) x) (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) x))
    (by rwa [OneOff.evalNodes_ofFn])

structure Order13FirstMesh (A : Matrix (Fin 19) (Fin 19) K) (b : Fin 19→K)
    (a : ℕ) (G : K[X]) : Prop where
  width : a=6 ∨ (a=5 ∧ firstSeed A b=0)
  degree : G.natDegree=a+1
  paid : evalNodes A G∈order13FirstEscape A b
  mesh : Order13Mesh A b G
  lowSeparation : ∀ P : K[X],P.natDegree≤a → evalNodes A P∈order13FirstEscape A b → P=0
  decomposition : markedTreeSpace A b (a+1)=(coeffEval A a).range⊔order13FirstEscape A b
  rank : finrank K (markedTreeSpace A b (a+1))=a+8+terminalDebit A b

theorem order13_first_mesh_of_frame (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 13)
    (F : Order13PaidFrame A b) : ∃ a G, Order13FirstMesh A b a G := by
  let W := order13FirstEscape A b
  have wR : finrank K W=7+terminalDebit A b := F.escapeRank
  have s5 (x : Fin 6→K) (hx : coeffEval A 5 x∈W) : x=0 :=
    marked_coeff_separated ha ho F.lastActive (by decide) (by decide) (by decide) x (F.escapePaid hx)
  have low5 := eval_eq_zero_of_coeff_separated (V:=W) s5
  by_cases hAlias : ∃ G : K[X],G.natDegree≤6 ∧ evalNodes A G∈W ∧ G≠0
  · obtain ⟨G,gd,gW,gn⟩ := hAlias
    have m := order13_paid_mesh ha ho F G (by omega) gW
    obtain ⟨first,dG⟩ := order13_mesh_alias m gd gn
    let Q := markedDefectSpace A b 6
    have nQ : evalNodes A G∉Q := by
      intro hm
      apply gn
      exact eval_eq_zero_of_coeff_separated
        (marked_coeff_separated ha ho F.lastActive (by decide) (q:=6) (j:=6) (by decide) (by decide))
        G dG.le hm
    have edge : W=Q⊔Submodule.span K {evalNodes A G} := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le (sup_le_sup le_sup_left le_rfl) ((Submodule.span_singleton_le_iff_mem ..).mpr gW)
      · rw [Submodule.finrank_sup_span_singleton nQ,wR]
        change _≤finrank K (markedDefectSpace A b 6)+1
        rw [F.defectRank]
        omega
    have hW : W≤markedTreeSpace A b 6 := by
      rw [edge]
      refine sup_le (sup_le_sup (zeroSpace_le_treeSpace A 6) le_rfl)
        ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
      exact (show treeSpace A 6≤markedTreeSpace A b 6 from le_sup_left) (evalNodes_mem_treeSpace A G dG.le)
    have inc := sup_le (pol_band_in_marked_tree (A:=A) (b:=b) (a:=5) (j:=6) (by decide)) hW
    have r := rank_coeff_sup_of_separated W s5
    have e := (Submodule.eq_of_le_of_finrank_le inc (by rw [F.rankMid,r,wR]; omega)).symm
    exact ⟨5,G,⟨Or.inr ⟨rfl,first⟩,dG,gW,m,low5,e,F.rankMid⟩⟩
  · have none (P : K[X]) (pd : P.natDegree≤6) (e : evalNodes A P∈W) : P=0 := by
      by_contra ne
      exact hAlias ⟨P,pd,e,ne⟩
    have sep := coeff_of_poly_sep none
    have inc : (coeffEval A 6).range⊔W≤markedTreeSpace A b 7 :=
      sup_le (pol_band_in_marked_tree (by decide)) (F.escapePaid.trans (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl))
    have r := rank_coeff_sup_of_separated W sep
    have hi : finrank K (markedTreeSpace A b 7)≤14+terminalDebit A b := F.upper 7 (by decide)
    have low : finrank K ((coeffEval A 6).range⊔W : Submodule K (Fin 19→K))=14+terminalDebit A b := by
      rw [r,wR]; omega
    have e := (Submodule.eq_of_le_of_finrank_le inc (hi.trans_eq low.symm)).symm
    have rank : finrank K (markedTreeSpace A b 7)=14+terminalDebit A b := by rw [e,low]
    have mem : evalNodes A (X^7 : K[X])∈(coeffEval A 6).range⊔W := e ▸
      (show treeSpace A 7≤markedTreeSpace A b 7 from le_sup_left) (evalNodes_mem_treeSpace A _ (by simp))
    obtain ⟨_,⟨x,rfl⟩,v,hv,hEq⟩ := Submodule.mem_sup.mp mem
    let P := ofFn 7 x
    have pd : P.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) x)
    let G : K[X] := X^7-P
    have dG : G.natDegree=7 := by
      rw [show G=X^7-P from rfl,natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
      simpa only [natDegree_X_pow] using Nat.lt_succ_of_le pd
    have gW : evalNodes A G∈W := by
      change evalNodes A (X^7-P)∈W
      rw [map_sub,show evalNodes A P=coeffEval A 6 x by exact OneOff.evalNodes_ofFn A 6 x,
        ←hEq,add_sub_cancel_left]
      exact hv
    exact ⟨6,G,⟨Or.inl rfl,dG,gW,order13_paid_mesh ha ho F G dG.le gW,none,e,rank⟩⟩

end
end RKResearch.Certified.Graded
