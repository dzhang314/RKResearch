module
public import RKCert.FourDebutComplete
public import RKCert.DirkCleanTracePivot
@[expose] public section
namespace RKCert.FiveDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape RKCert.FourDebut Polynomial
variable {K : Type*} [Field K] [CharZero K] {s p j n : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {S : Finset K} {i : Fin s}
noncomputable section

/-- A grade-five core is sufficient to make each of the first three
distinct nonzero outside debut amplitudes nonzero. This does not require
a grade-three mask or any hypothesis about grade eight. -/
theorem early_three (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 7≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (f₆ : zeroSpace A 6≤chain (diag (nodes A)) U w 2)
    (f₇ : zeroSpace A 7≤chain (diag (nodes A)) U w 3)
    (d : Debut (nodes A) U S i) (small : S.card≤2) : w i≠0 := by
  classical
  intro bad
  have clean₆:=zero_pure_at d.outsideU bad f₆
  have clean₇:=zero_pure_at d.outsideU bad f₇
  let H:=Lagrange.nodal S id
  have deg:H.natDegree=S.card:=Lagrange.natDegree_nodal
  have fresh : H.eval (nodes A i)≠0 := Lagrange.eval_nodal_not_at_node (fun a ha e=> d.fresh (e.symm ▸ ha))
  have mask (k : ℕ) (hk:k≤2) :
      ∃ v, OrdinaryTrace A 5 v (X^(1+k)*H) ∧ PrefixZero v i ∧
        v i=(nodes A i)^(1+k)*H.eval (nodes A i) := by
    obtain ⟨v,pure,pre,here⟩:=masked_at_debut inv alg d (P:=X^(1+k)*H) (by simp) (by
      intro a ha
      have e:H.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
      simp [e])
    exact ⟨v,⟨natDegree_mul_le.trans (by rw [natDegree_X_pow,deg];omega),inc pure⟩,pre,by simpa using here⟩
  obtain ⟨v,tr,pre,here⟩:=mask 0 (by decide)
  have pos:v i≠0:=by rw [here];exact mul_ne_zero (pow_ne_zero _ d.nz) fresh
  have diag0:=(tr.primitive_zero_at_first_clean ha ho (by omega) (show 5+2≤7 by decide) pos pre clean₇).1
  have zero : H=0 := primitive_shift_detect H (k:=1) (d:=S.card) deg.le _ d.nz (fun l=>by
    obtain ⟨t,th,earlier,_⟩:=mask l.val (by have:=l.isLt;omega)
    have e:=clean₆ _ th.primitive.pure
    have z:mat A t i=0:=by simpa only [diag0,zero_mul] using causalDiag_mat ha i t earlier
    simpa only [Pi.sub_apply,z,evalNodes_apply,zero_sub,neg_eq_zero] using e)
  exact Lagrange.nodal_ne_zero zero

omit [CharZero K] in
/-- The fifth debut is explicit: the commutator of the cleared x times
the four old site factors vanishes along three genuinely active old
amplitudes, forcing its whole quadratic head multiplier to vanish. -/
theorem refund_fifth (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 7≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (f₇ : zeroSpace A 7≤chain (diag (nodes A)) U w 3)
    (d : Debut (nodes A) U S i) (small : S.card≤4) (ix : Fin 3→Fin s)
    (prev : ∀ k, ix k < i) (outside : ∀ k, ¬Live U (ix k))
    (weight : ∀ k, w (ix k)≠0) (inj : Function.Injective (fun k=>nodes A (ix k))) : A i i=0 := by
  classical
  let H:=Lagrange.nodal S id
  have deg:H.natDegree=S.card:=Lagrange.natDegree_nodal
  have fresh : H.eval (nodes A i)≠0 := Lagrange.eval_nodal_not_at_node (fun a ha e=> d.fresh (e.symm ▸ ha))
  obtain ⟨v,pure,pre,here⟩:=masked_at_debut inv alg d (P:=X*H) (by simp) (by
    intro a ha
    have e:H.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
    simp [e])
  have tr : OrdinaryTrace A 5 v (X*H) := ⟨natDegree_mul_le.trans (by rw [natDegree_X,deg];omega),inc pure⟩
  have pos:v i≠0 := by rw [here,eval_mul,eval_X];exact mul_ne_zero d.nz fresh
  exact refund_by_old ix ha ho hp tr.stage pre pos d.outsideU prev outside weight inj f₇

end
end RKCert.FiveDebut
