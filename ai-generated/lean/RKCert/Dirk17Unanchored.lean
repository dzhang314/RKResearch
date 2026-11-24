module
public import RKCert.Dirk17Ranks
public import RKCert.DirkTwentyJoint
public import RKCert.DirkSignedOrbitSharp
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
noncomputable section
set_option maxRecDepth 3000

theorem true_last (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17):b (Fin.last 22)≠0:=by
  intro z
  let cut:22≤23:=by decide
  have trimmed:=order_on_lower_prefix ha ho cut (fun i hi=>by
    have endp:i=Fin.last 22:=Fin.ext (by change i.val=22;have:=i.isLt;omega)
    simpa [endp] using z)
  have bad:=odd_floor (m:=8) (by decide) (lower_prefix ha cut) trimmed
  omega

structure Unanchored (A:Fin 23→Fin 23→K) (b:Vec K 23):Prop where
  /-- Only the true last coordinate, never a projected last row. -/
  lastWeight:b (Fin.last 22)≠0
  cardinal:Pi.single (Fin.last 22) (1:K)∈treeSpace A 8
  clean:∀f∈zeroSpace A 8,f (Fin.last 22)=0
  D:PaidReverseBand A b 17 8
  words:∀j,2≤j→j≤8→marked A 17 j=dirkBack A b (j-2)
  dual:annih (dirkBack A b 6)=treeSpace A 8

theorem unanchored (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (non:q₂ (mat A) (nodes A) 1≠0):
    Unanchored A b:=by
  let R:=ranks ha ho
  have ex:excess A=1:=by simp [excess,non]
  have bank:finrank K (treeSpace A 8)=17:=by rw [R.e8,ex]
  have dual (q r:ℕ)(lo:8≤q)(sum:q+r=14):finrank K (treeSpace A q)=q+9 ∧ finrank K (dirkBack A b r)=r ∧
    dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r):=by
    obtain ⟨front,rest⟩:=paid_tail_duality ha ho (m:=8) (d:=17) (r₀:=6) bank.ge (by decide) (by decide)
      (q:=q) (r:=r) lo (by omega)
    exact ⟨by omega,rest⟩
  have words(j:ℕ) (lo:2≤j) (hi:j≤8):marked A 17 j=dirkBack A b (j-2):=
    (dual (16-j) (j-2) (by omega) (by omega)).2.2.1.symm
  let t:=Fin.last 22
  have hb:=true_last ha ho
  have after(j:Fin 23)(later:t<j):b j=0:=False.elim ((not_lt_of_ge (Fin.le_last j)) later)
  obtain ⟨d1,d2⟩:=twoOrbit_initial_zero (dual 14 0 (by decide) (by decide)).2.1
  have hy:=dirk_last_node ha t hb after d1 d2
  have ht:nodes A t=1:=(sub_eq_zero.mp (show 1-nodes A t=0 from hy)).symm
  have dg:A t t=0:=by
    have eqn:=congrFun d1 t
    change transMat A b t-mirror A t*b t=0 at eqn
    rw [causalDiag_transpose ha t b (fun j hj=>after j (Fin.rev_lt_rev.mp hj)),hy,zero_mul,sub_zero] at eqn
    exact (mul_eq_zero.mp eqn).resolve_right hb
  have col(i:Fin 23):A i t=0:=by
    rcases lt_or_eq_of_le (Fin.le_last i) with lt|eq
    · exact ha i t lt
    · simpa [eq,t] using dg
  have last(r:ℕ)(v:Vec K 23)(hv:v∈dirkBack A b r):v t=0:=dirkBack_prior ha t after hy d1 d2 r hv t (show t≤t from le_rfl)
  have card:Pi.single t (1:K)∈treeSpace A 8:=by
    rw [(dual 8 6 (by decide) (by decide)).2.2.2,mem_annih]
    intro v hv;simp [row_apply,Pi.single_apply,last 6 v hv]
  have zmark(j:ℕ) (lo:2≤j) (hi:j≤8):ReverseHermite.zeroMarked A 17 t j=dirkBack A b (j-2):=by
    apply le_antisymm
    · exact (inf_le_left:_≤marked A 17 j).trans (words j lo hi).le
    · intro v hv;exact ⟨(words j lo hi).symm ▸ hv,last _ v hv⟩
  refine ⟨hb,card,cardinal_clean_lower ho (j:=8) (by decide) t hb card,
    ⟨by decide,by decide,ht,col,⟨d1,d2⟩,?_,zmark⟩,words,(dual 8 6 (by decide) (by decide)).2.2.2.symm⟩
  intro r hi;exact (dual (14-r) r (by omega) (by omega)).2.1

theorem unanchored_joint_inside (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (h:Unanchored A b):
    jointWithOrigin A b 1≤zeroSpace A 8:=by
  intro v inside
  obtain ⟨⟨wb,wt⟩,_⟩:=jointWithOrigin_iff.mp inside
  have mem:v∈treeSpace A 8:=by
    rw [←h.dual,mem_annih]
    intro u hu
    obtain ⟨P,_,eqn⟩:=h.D.word_polynomial ha ho (h.D.nonlocal_cubic ha ho) (r:=6) (by decide) (by decide) hu
    rw [row_apply];apply Finset.sum_eq_zero;intro i _
    have vi:tau A b i*v i=0:=congrFun wt i
    rw [eqn i];linear_combination P.eval (mirror A i)*vi
  exact pure_of_weight_zero ho (q:=8) (m:=8) (by decide) (Or.inl (by decide))
    (ranks ha ho).e8_full mem wb (fun _=>Or.inr (by decide))

end
end RKCert.Paired.Seventeen
