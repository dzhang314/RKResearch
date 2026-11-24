module
public import RKCert.DirkEvenReverseProfile
@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {s p n:ℕ} {A:Fin s→Fin s→K}
variable {b w:Vec K s} {P:K[X]}
noncomputable section

theorem rev_zero_numeric (h:ReverseTrace A b p n 0 P) (ho:HasTreeOrderAtLeast A b p)
    (hp:2*n+1≤p) : P=0 := by
  apply primitive_shift_detect P h.degree 1 one_ne_zero (k:=0)
  intro i
  have eq:=h.weighted_moment ho i.val (by omega)
  simpa [row_apply] using eq.symm

omit [CharZero K] in
theorem reverse_scale (h:ReverseTrace A b p n w P) (a:K) :
    ReverseTrace A b p n (a • w) (a • P) := by
  refine ⟨(Polynomial.natDegree_smul_le _ _).trans h.degree,?_⟩
  simpa [smul_sub] using (marked A p n).smul_mem a h.pure

omit [CharZero K] in
theorem rev_shift (h:ReverseTrace A b p n w P) (a:K) (hp:n+2≤p) :
    ReverseTrace A b p (n+1) (diag (mirror A) w-a • w) (X*P-a • P) :=
  (h.clock hp).sub ((reverse_scale h a).mono (by omega))

def timesY (y w:Vec K s) (k:ℕ) : Vec K s := fun i=>y i^k*w i

omit [CharZero K] in
theorem rev_clock_pow (h:ReverseTrace A b p n w P) (k:ℕ) (hp:n+k+1≤p) :
    ReverseTrace A b p (n+k) (timesY (mirror A) w k) (X^k*P) := by
  induction k with
  | zero =>
    have zero:timesY (mirror A) w 0=w := by ext i; simp [timesY]
    simpa only [zero, Nat.add_zero,pow_zero,one_mul] using h
  | succ k ih =>
    have x:diag (mirror A) (timesY (mirror A) w k)=timesY (mirror A) w (k+1) := by
      ext i
      simp only [diag_apply,timesY,pow_succ']; ring
    have new:= (ih (by omega)).clock (by omega)
    rw [x,←mul_assoc,←pow_succ'] at new
    exact new

omit [CharZero K] in
theorem exists_last_coordinate (h:w≠0) : ∃i:Fin s,w i≠0 ∧ ∀j,i < j → w j=0 := by
  have hrev:ReverseHermite.rev w≠0 := fun eq => h (ReverseHermite.rev.injective (eq.trans (map_zero _).symm))
  obtain ⟨k,hk,prev⟩:=exists_first_coordinate hrev
  refine ⟨k.rev,hk,fun j hj=>?_⟩
  have h' : j.rev < k := by simpa using (Fin.rev_lt_rev.mpr hj)
  simpa using prev j.rev h'

omit [CharZero K] in
theorem reverse_at (ha:LowerArray A) (i:Fin s) (hpre:∀j,i < j → w j=0) :
    transMat A w i=A i i*w i :=
  causalDiag_transpose ha i w (fun j hj => hpre j (Fin.rev_lt_rev.mp hj))

omit [CharZero K] in
theorem reverse_after (ha:LowerArray A) (i:Fin s) (hpre:∀j,i < j → w j=0) (l:Fin s) (hl:i < l) :
    transMat A w l=0 := by
  change (∑k:Fin s,A k l*w k)=0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk:k < l
  · rw [ha k l hk,zero_mul]
  · rw [hpre k (lt_of_lt_of_le hl (le_of_not_gt hk)),mul_zero]

omit [CharZero K] in
theorem reverse_refund_eq (ha:LowerArray A) (i:Fin s) (hpre:∀j,i < j → w j=0) :
    commutatorR (transMat A) (diag (mirror A)) w i = -(A i i)^2*w i := by
  have x:=reverse_at ha i hpre
  have a:=reverse_at ha i (w:=diag (mirror A) w) (fun j hj=> by simp [hpre j hj])
  have c:=reverse_at ha i (w:=transMat A w) (reverse_after ha i hpre)
  change diag (mirror A) (transMat A w) i - transMat A (diag (mirror A) w) i -
    transMat A (transMat A w) i=_
  rw [diag_apply,a,c,x,diag_apply]
  ring

variable {m:ℕ} {T:Fin (s+1)→Fin (s+1)→K} {β v:Vec K (s+1)}

theorem reverse_word_vanish (hm:7≤m) (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack T β 1).map (diag (mirror T))≤dirkBack T β 1)
    {j:ℕ} (lo:3≤j) (hi:j≤m) {w:Vec K (s+1)} (hw:w∈marked T (2*m) j)
    (wt:w (Fin.last s)=0) (i:Fin (s+1)) (hτ:tau T β i=0) : w i=0 := by
  have hword:=marked_to_words hm ha ho he (by omega) hi hw wt
  obtain ⟨Q,_,hq⟩:=word_polynomial hm ha ho he non (by omega) (by omega) hword
  simp [hq i,hτ]

theorem refund_diagonal (hm:7≤m) (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack T β 1).map (diag (mirror T))≤dirkBack T β 1)
    {j:ℕ} (lo:1≤j) (hi:j+2≤m) (h:ReverseTrace T β (2*m) j v P)
    (i:Fin (s+1)) (hτ:tau T β i=0) (vi:v i≠0) (pre:∀k,i < k → v k=0) : T i i=0 := by
  obtain ⟨_,ct,col,_⟩:=last_physical hm ha ho he
  have wt:commutatorR (transMat T) (diag (mirror T)) v (Fin.last s)=0 := by
    change (mirror T (Fin.last s)*transMat T v (Fin.last s) -
      transMat T _ (Fin.last s))-transMat T _ (Fin.last s)=0
    simp [ReverseHermite.trans_terminal _ col,mirror,ct]
  have hR:=reverse_word_vanish hm ha ho he non (by omega) hi (h.commutator ho (by omega)) wt i hτ
  rw [reverse_refund_eq ha i pre] at hR
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp (neg_eq_zero.mp ((mul_eq_zero.mp hR).resolve_right vi))

theorem pivot_primitive (hm:7≤m) (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack T β 1).map (diag (mirror T))≤dirkBack T β 1)
    {j:ℕ} (lo:2≤j) (hi:j+1≤m) (h:ReverseTrace T β (2*m) j v P)
    (i:Fin (s+1)) (hb:β i≠0) (hτ:tau T β i=0) (pre:∀k,i < k → v k=0) (ad:T i i=0) :
    (formalPrimitive P).eval (mirror T i)=0 := by
  obtain ⟨_,ct,col,_⟩:=last_physical hm ha ho he
  have wt:(transMat T v-weightedEval (mirror T) β (formalPrimitive P)) (Fin.last s)=0 := by
    simp [ReverseHermite.trans_terminal _ col,mirror,ct]
  have hh:=reverse_word_vanish hm ha ho he non (by omega) hi
    ((h.primitive ho (by omega)).pure) wt i hτ
  rw [Pi.sub_apply,reverse_at ha i pre,ad,zero_mul,zero_sub,neg_eq_zero,weightedEval_apply] at hh
  exact (mul_eq_zero.mp hh).resolve_right hb

/-- The first actual nonzero coordinate in reverse chronology earns a
diagonal refund and every remaining scalar primitive test, not just a
matching ansatz. -/
theorem physical_reverse_pivot (hm:7≤m) (ha:LowerArray T) (ho:HasTreeOrderAtLeast T β (2*m))
    (he:s+1+3=3*m) (non:¬(dirkBack T β 1).map (diag (mirror T))≤dirkBack T β 1)
    {j:ℕ} (lo:2≤j) (hi:j+2≤m) (h:ReverseTrace T β (2*m) j v P)
    (active:∀i,v i≠0 → β i≠0 ∧ tau T β i=0) (hP:P≠0) :
    ∃i:Fin (s+1), v i≠0 ∧ β i≠0 ∧ tau T β i=0 ∧ T i i=0 ∧
      ∀k:ℕ,j+k+1≤m → (formalPrimitive (X^k*P)).eval (mirror T i)=0 := by
  have nz:v≠0:=by
    intro hz
    rw [hz] at h
    exact hP (rev_zero_numeric h ho (by omega))
  obtain ⟨i,vi,pre⟩:=exists_last_coordinate nz
  obtain ⟨bi,τi⟩:=active i vi
  have ad:=refund_diagonal hm ha ho he non (by omega) hi h i τi vi pre
  refine ⟨i,vi,bi,τi,ad,?_⟩
  intro k hk
  have h':=rev_clock_pow h k (by omega)
  exact pivot_primitive hm ha ho he non (by omega) hk h' i bi τi
    (fun l hl=>by simp [timesY,pre l hl]) ad

end
end RKCert.Paired.Terminal
