module
public import RKCert.FourDebutCut
public import RKCert.EndpointPhysical
@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape Module Polynomial
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {S : Finset K} {i : Fin s}

theorem masked_at_debut (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U)
    (db : Debut (nodes A) U S i) {P : Polynomial K} (h0 : P.eval 0=0) (roots : ∀a∈S,P.eval a=0) :
    ∃ v : Vec K s, v-evalNodes A P∈U ∧ PrefixZero v i ∧ v i=P.eval (nodes A i) := by
  obtain ⟨v,hv,hL,hN⟩ := masked_polynomial hT hU P
  refine ⟨v,hv,?_,hN _ db.outsideU⟩
  intro l hl
  by_cases h : Live U l
  · exact hL _ h
  · rw [hN _ h]
    by_cases z : nodes A l=0
    · rw [z,h0]
    · exact roots _ (db.old l hl h z)

theorem shifted_coeff {n : ℕ} (P : Polynomial K) (hp : P.natDegree≤n) (a : ℕ) :
    evalShift A (fun i : Fin (n+1)=>P.coeff i.val) a=evalNodes A (X^a*P) := by
  ext i
  rw [evalShift,Finset.sum_apply,evalNodes_apply,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),Finset.mul_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Pi.smul_apply,smul_eq_mul,pow_add]
  ring

set_option maxHeartbeats 1000000 in
/-- The first three outside debuts genuinely have nonzero head values.
The proof uses all shifted scalar moments, valid over complex fields as
well as over the reals, never a positivity inference about an unknown square. -/
theorem early_head [CharZero K] (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U) (hin : U≤zeroSpace A 3)
    (flag5 : zeroSpace A 5 ≤ chain (diag (nodes A)) U w 2)
    (flag6 : zeroSpace A 6 ≤ chain (diag (nodes A)) U w 3)
    (db : Debut (nodes A) U S i) (small : S.card≤2) : w i≠0 := by
  classical
  intro wi
  have c5 := zero_pure_at db.outsideU wi flag5
  have c6 := zero_pure_at db.outsideU wi flag6
  let H := Lagrange.nodal S id
  have hd : H.natDegree=S.card := Lagrange.natDegree_nodal
  have hz (a : K) (ha : a∈S) : H.eval a=0 := Lagrange.eval_nodal_at_node (v:=id) ha
  have heren : H.eval (nodes A i)≠0 := Lagrange.eval_nodal_not_at_node (fun a ha e => db.fresh (e.symm ▸ ha))
  have mask (k : ℕ) :
      ∃ v : Vec K s, v-evalNodes A (X^(k+1)*H)∈U ∧ PrefixZero v i ∧
        v i=(nodes A i)^(k+1)*H.eval (nodes A i) := by
    obtain ⟨v,hv,pre,atv⟩ := masked_at_debut hT hU db (P:=X^(k+1)*H) (by simp)
      (fun a haa => by simp [hz a haa])
    exact ⟨v,hv,pre,by simpa using atv⟩
  obtain ⟨v,hv,pfx,atv⟩ := mask 0
  have hg : (X^(0+1)*H).natDegree≤3 := by
    apply (Polynomial.natDegree_mul_le).trans
    rw [Polynomial.natDegree_X_pow,hd]; omega
  have block := evalNodes_mem_treeSpace A (X^(0+1)*H) hg
  have paid : v∈treeSpace A 3 := by
    simpa only [sub_add_cancel] using (treeSpace A 3).add_mem (zeroSpace_le_treeSpace A 3 (hin hv)) block
  have vn : v i≠0 := by rw [atv]; exact mul_ne_zero (pow_ne_zero _ db.nz) heren
  have refund := Pivot.refund ha ho (by omega : 3+2≤p) paid pfx vn c5
  let f : Fin (S.card+1)→K := fun j=>H.coeff j.val
  have vals (t : Fin (S.card+1)) : RKCert.Endpoint.moment f (nodes A i) (t.val+1)=0 := by
    obtain ⟨v,hv,pfx,_⟩ := mask t.val
    have deg (l : Fin (S.card+1)) : l.val+(t.val+1)≤5 := by omega
    have comp : v-evalShift A f (t.val+1)∈zeroSpace A 5 := by
      rw [show evalShift A f (t.val+1)=_ from shifted_coeff H hd.le (t.val+1)]
      exact zeroSpace_mono A (by decide : 3≤5) (hin hv)
    rw [←primitive_value ho (by omega) deg comp c6,mat_at_prefix ha i v pfx,refund,zero_mul]
  have vanished (t : Fin (S.card+1)) :
      (∑ j : Fin (S.card+1), (RKCert.EndpointPhysical.rescale f (nodes A i)) j /
        ((t.val+j.val+2:ℕ):K))=0 := by
    have eq := RKCert.EndpointPhysical.moment_rescale f (nodes A i) 1 (t.val+1)
    rw [mul_one,vals t] at eq
    have zero := (mul_eq_zero.mp eq.symm).resolve_left (pow_ne_zero _ db.nz)
    simpa only [RKCert.Endpoint.moment,one_pow,mul_one,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using zero
  have z := RKCert.Endpoint.shifted_hilbert_kernel 2 (by decide) _ vanished
  have f0 := (RKCert.EndpointPhysical.rescale_eq_zero_iff f db.nz).mp z
  have htop := congrFun f0 (⟨S.card,by omega⟩ : Fin (S.card+1))
  have hc : H.coeff S.card=0 := htop
  rw [←hd] at hc
  have mon : H.Monic := Lagrange.nodal_monic
  exact one_ne_zero (mon.coeff_natDegree.symm.trans hc)

theorem general_refund [CharZero K] {j n : ℕ} (ix : Fin n→Fin s) (d : Debut (nodes A) U S i)
    (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p) (hpay : j+2≤p) (jmin : 3≤j)
    (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U) (hin : U≤zeroSpace A 3) (nodesPaid : S.card+1≤j)
    (past : ∀k,ix k < i) (non : ∀k,¬ Live U (ix k)) (vals : ∀k,w (ix k)≠0)
    (hz : Function.Injective (fun k=>nodes A (ix k)))
    (flag : zeroSpace A (j+2)≤chain (diag (nodes A)) U w n) : A i i=0 := by
  let H := Lagrange.nodal S id
  let P : Polynomial K := X*H
  have p0 : P.eval 0=0 := by simp [P]
  have van (a : K) (h : a∈S) : P.eval a=0 := by
    have e : H.eval a=0 := Lagrange.eval_nodal_at_node (v:=id) h
    simp [P,e]
  obtain ⟨v,hm,pre,val⟩ := masked_at_debut hT hU d p0 van
  have hn : H.eval (nodes A i)≠0 := Lagrange.eval_nodal_not_at_node (fun a ha e=> d.fresh (e.symm ▸ ha))
  have vn : v i≠0 := by
    rw [val]; change (X*H).eval (nodes A i)≠0
    rw [eval_mul,eval_X]; exact mul_ne_zero d.nz hn
  have hd : P.natDegree≤j := by
    apply (Polynomial.natDegree_mul_le).trans
    rw [Polynomial.natDegree_X,show H.natDegree=S.card from Lagrange.natDegree_nodal]
    omega
  have f := zeroSpace_le_treeSpace A j (zeroSpace_mono A jmin (hin hm))
  have vt : v∈treeSpace A j := by
    simpa only [sub_add_cancel] using (treeSpace A j).add_mem f (evalNodes_mem_treeSpace A P hd)
  exact refund_by_old ix ha ho hpay vt pre vn d.outsideU past non vals hz flag

theorem masked_primitive [CharZero K] {j n : ℕ} (d : Debut (nodes A) U S i)
    (ha : SDIRK.lower A) (hT : U.map (diag (nodes A))≤U) (hU : MulClosed U)
    (hin : U≤zeroSpace A j) (flag : zeroSpace A (j+1)≤chain (diag (nodes A)) U w n) (ai : A i i=0)
    {P : Polynomial K} (dp : P.natDegree≤j) (p0 : P.eval 0=0) (roots : ∀a∈S,P.eval a=0) :
    ∃ Q : Polynomial K, Q.degree<(n:WithBot ℕ) ∧
      ∀ l ≤ i, ¬ Live U l → (primitive P).eval (nodes A l)=w l*Q.eval (nodes A l) := by
  obtain ⟨v,vp,pre,_⟩ := masked_at_debut hT hU d p0 roots
  obtain ⟨Q,h,_,eqn⟩ := primitive_output ha flag dp (hin vp) pre ai
  exact ⟨Q,h,eqn⟩

theorem debut_before {U : Submodule K (Vec K s)} {S T : Finset K} {i j : Fin s}
    (u : Debut (nodes A) U S i) (v : Debut (nodes A) U T j) (e : S⊆T) (c : nodes A i∈T) : i<j := by
  by_contra! he
  rcases lt_or_eq_of_le he with h|rfl
  · exact v.fresh (e (u.old j h v.outsideU v.nz))
  · exact v.fresh c

end RKCert.FourDebut
