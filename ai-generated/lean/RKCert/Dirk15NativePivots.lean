module

public import RKCert.Dirk15NativeReverse
public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # Actual forward and reverse chronological primitive refunds
A pivot is an original physical coordinate in the indicated chronology.
In particular the forward pivot is not selected by filtering output weights;
for the reverse pivot only its own proved weight is used. -/
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s p n H : ℕ}
variable {A : Fin s → Fin s → K} {b v : Vec K s} {P : K[X]}

theorem transMat_last_apply (ha : LowerArray A) (i : Fin s) (v : Vec K s)
    (hpre : ∀ j, i<j → v j=0) : transMat A v i=A i i*v i :=
  causalDiag_transpose ha i v (fun j hj => hpre j (Fin.rev_lt_rev.mp hj))

theorem commutatorR_reverse_leading (ha : LowerArray A) {i : Fin s}
    (hpre : ∀ j, i<j → v j=0) :
    commutatorR (transMat A) (diag (mirror A)) v i=-(A i i)^2*v i := by
  have e := transMat_last_apply ha i v hpre
  have e' := transMat_last_apply ha i (diag (mirror A) v) (fun j hj => by simp [hpre j hj])
  have e'' := transMat_last_apply ha i (transMat A v) (fun j hj => by
    rw [transMat_last_apply ha j v (fun k hk => hpre k (hj.trans hk)),hpre j hj,mul_zero])
  change diag (mirror A) (transMat A v) i -
    transMat A (diag (mirror A) v) i - transMat A (transMat A v) i=_
  rw [diag_apply,e',e'',e,diag_apply]
  ring

theorem exists_last_coordinate (hv : v≠0) :
    ∃ i : Fin s, v i≠0 ∧ ∀ j, i<j → v j=0 := by
  let w : Vec K s := fun i => v i.rev
  have hw : w≠0 := by
    intro h
    apply hv
    ext j
    simpa [w] using congrFun h j.rev
  obtain ⟨i,hi,hpre⟩ := exists_first_coordinate hw
  refine ⟨i.rev,hi,fun j hj => ?_⟩
  have hh := hpre j.rev (by simpa only [Fin.rev_rev,Fin.rev_lt_rev] using
    (Fin.rev_lt_rev.mpr hj : j.rev < i.rev.rev))
  simpa [w] using hh

variable [CharZero K]

namespace OrdinaryTrace

/-- One true clean forward pivot gives both necessary moments. No factor of
the output weights is ever cancelled in the forward direction. -/
theorem two_primitive_first_pivot (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (h : OrdinaryTrace A n v (X*P)) (hcap : n+2≤H) (hp : n+2≤p)
    {i : Fin s} (hi : v i≠0) (hpre : ∀ j < i,v j=0)
    (clean : ∀ w∈zeroSpace A H,w i=0) :
    A i i=0 ∧ Signature.paidMoment P (nodes A i) 1=0 ∧
      Signature.paidMoment P (nodes A i) 2=0 := by
  have hR : commutatorR (mat A) (diag (nodes A)) v ∈ zeroSpace A (n+2) :=
    commutator_mem_zeroSpace ho n hp h.stage
  have hRi := clean _ (zeroSpace_mono A hcap hR)
  rw [commutatorR_leading ha hpre] at hRi
  have hz : A i i=0 := sq_eq_zero_iff.mp
    (neg_eq_zero.mp ((mul_eq_zero.mp hRi).resolve_right hi))
  have hstep {m : ℕ} {w : Vec K s} {Q : K[X]}
      (ht : OrdinaryTrace A m w Q) (hm : m+1≤H) (hw : ∀ j < i,w j=0) :
      (formalPrimitive Q).eval (nodes A i)=0 := by
    have e := clean _ (zeroSpace_mono A hm ht.primitive.pure)
    have hmat : mat A w i=0 := by simpa only [hz,zero_mul] using causalDiag_mat ha i w hw
    simpa only [Pi.sub_apply,evalNodes_apply,hmat,zero_sub,neg_eq_zero] using e
  refine ⟨hz,?_,?_⟩
  · simpa only [Signature.paidMoment,pow_one] using hstep h (by omega) hpre
  · simpa only [Signature.paidMoment,pow_two,mul_assoc] using
      hstep h.clock hcap (fun j hj => by simp [hpre j hj])

/-- The true contrast is nonzero on a nonterminal coordinate; the endpoint
is removed by the scalar weight (1−x), not by assuming order after deletion. -/
theorem nonterminal_clock_witness {d : ℕ} (hP : P≠0) (hd : P.natDegree≤d)
    (h : OrdinaryTrace A n v P) (ho : HasTreeOrderAtLeast A b p) (hp : n+d+4≤p)
    (t : Fin s) (ht : nodes A t=1) : ∃ i, i≠t ∧ (diag (nodes A) v) i≠0 := by
  by_contra! nh
  have hv : diag (nodes A) v-diag (nodes A) (diag (nodes A) v)=0 := by
    ext i
    by_cases e : i=t
    · subst i
      simp [ht]
    · simp [nh i e,diag_apply] 
  have H : OrdinaryTrace A (n+2) (diag (nodes A) v-diag (nodes A) (diag (nodes A) v))
      (X*P-X*(X*P)) := (h.clock.mono (by omega : n+1≤n+2)).sub h.clock.clock
  rw [hv,show X*P-X*(X*P)=X*((1-X)*P) by ring] at H
  have dQ := natDegree_mul_le (p:=(1-X : K[X])) (q:=P)
  have dX : (1-X : K[X]).natDegree≤1 := by
    simpa using (natDegree_sub_le (1:K[X]) X)
  have hb : (d+1)+(n+2)+1≤p := by omega
  have eq := OrdinaryTrace.zero_numeric (n:=n+2) (d:=d+1) (k:=1)
    (by simpa only [pow_one] using H) (by omega) ho hb
  refine hP ((mul_eq_zero.mp eq).resolve_left ?_)
  exact sub_ne_zero.mpr (fun e => by have he := congrArg (Polynomial.eval (0:K)) e; simp at he)

end OrdinaryTrace

namespace ReverseTrace

/-- A nonzero marked polynomial profile is detected after one clock
multiplication, by the true weighted scalar moments. -/
theorem clock_witness {d : ℕ} (h : ReverseTrace A b p n v P)
    (ho : HasTreeOrderAtLeast A b p) (hP : P≠0) (hd : P.natDegree≤d)
    (hp : n+d+2≤p) : diag (mirror A) v≠0 := by
  intro hz
  apply hP
  apply primitive_shift_detect P hd 1 one_ne_zero (k:=1)
  intro i
  have he := (h.clock (by omega)).weighted_moment ho i.val (by have := i.isLt; omega)
  rw [hz] at he
  have he' : X^i.val*(X*P)=X^(1+i.val)*P := by rw [pow_add,pow_one]; ac_rfl
  simpa only [row_apply,Pi.zero_apply,zero_mul,Finset.sum_const_zero,he'] using he.symm

end ReverseTrace

variable {s : ℕ} {A : Fin (s+1) → Fin (s+1) → K} {b v : Vec K (s+1)}

omit [CharZero K] in
theorem physical_terminal_commutator_zero (T : PhysicalTerminal A b) (v : Vec K (s+1)) :
    commutatorR (transMat A) (diag (mirror A)) v (Fin.last s)=0 := by
  change diag (mirror A) (transMat A v) _ - transMat A (diag (mirror A) v) _ -
    transMat A (transMat A v) _=0
  simp [T.trans_zero_terminal]

namespace ReverseTrace

/-- At a true reversed clean pivot, primitive discrepancies vanish because
they are paid and terminal-zero. Cancellation is limited to the locally
verified nonzero output weight. -/
theorem two_primitive_last_pivot (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p)
    (T : PhysicalTerminal A b) (h : ReverseTrace A b p n v (X*P))
    (hcap : n+2≤H) (hp : n+3≤p) {i : Fin (s+1)}
    (hi : v i≠0) (hpre : ∀ j,i<j → v j=0) (hbi : b i≠0)
    (clean : ∀ w∈markedTerminalZero A p H,w i=0) :
    A i i=0 ∧ Signature.paidMoment P (mirror A i) 1=0 ∧
      Signature.paidMoment P (mirror A i) 2=0 := by
  have hR : commutatorR (transMat A) (diag (mirror A)) v ∈ markedTerminalZero A p H :=
    ⟨marked_mono A p hcap (h.commutator ho hp),
      prior_last_iff.mpr (physical_terminal_commutator_zero T _)⟩
  have hRi := clean _ hR
  rw [commutatorR_reverse_leading ha hpre] at hRi
  have hz : A i i=0 := sq_eq_zero_iff.mp
    (neg_eq_zero.mp ((mul_eq_zero.mp hRi).resolve_right hi))
  have hstep {m : ℕ} {w : Vec K (s+1)} {Q : K[X]}
      (ht : ReverseTrace A b p m w Q) (hm : m+1≤H) (hmp : m+2≤p)
      (hw : ∀ j,i<j → w j=0) : (formalPrimitive Q).eval (mirror A i)=0 := by
    have ht' := ht.primitive ho hmp
    have hdef : transMat A w-weightedEval (mirror A) b (formalPrimitive Q)∈
        markedTerminalZero A p H :=
      ⟨marked_mono A p hm ht'.pure,prior_last_iff.mpr (by
        simp [T.trans_zero_terminal,terminal_mirror_zero T])⟩
    have e := clean _ hdef
    have hm : transMat A w i=0 := by rw [transMat_last_apply ha i w hw,hz,zero_mul]
    simp only [Pi.sub_apply,weightedEval_apply,hm,zero_sub,neg_eq_zero] at e
    exact (mul_eq_zero.mp e).resolve_right hbi
  refine ⟨hz,?_,?_⟩
  · simpa only [Signature.paidMoment,pow_one] using hstep h (by omega) (by omega) hpre
  · simpa only [Signature.paidMoment,pow_two,mul_assoc] using
      hstep (h.clock (by omega)) hcap hp (fun j hj => by simp [hpre j hj])

end ReverseTrace
end RKCert.Paired
