module
public import RKCert.ERKOrder13FullOdd
public import RKCert.ERKOrder13MarkedRankTwoReduction
public import RKCert.ERKOrder13MarkedLatePure
public import RKCert.ERKOrder13MarkedThreeTwo

@[expose] public section
/-! # Exact remaining marked charts for the ordered order-thirteen endpoint
A remaining two-chain must be early and has the stated literal pure factor.
The early pure moment eliminations and the higher marked head ranks are not
asserted by this file. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.TerminalSteering Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2800000

theorem marked13_rank_two_early_factors (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G) :
    (terminal s:Vec K (s+1))∈treeSpace A 7 ∧
    ∃ (v:Vec K (s+1)) (P Q:K[X]), Chart13 A 1 a 2 U v G ∧ MulClosed U ∧
      (∀i,Live U i→v i=0) ∧ G=P*Q ∧ P.natDegree=a-2 ∧ Q.natDegree=3 ∧
      (∀i,v i≠0→v i=P.eval (nodes A i)) := by
  have lo:=zeroSpace_finrank ha ho (n:=3) (by decide)
  change 3≤finrank K (zeroSpace A 4) at lo
  have hi:=Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha S.separated (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at hi
  rw [S.fRank 5 le_rfl (by decide)] at hi
  have four:finrank K (zeroSpace A 4)=4 := by
    by_contra neq
    exact marked13_rank_three_two_impossible ha ho S M C (by omega)
  obtain ⟨v,P,Q,C,alg,dis,sq,fit,pd,qd,rep⟩:=marked13_rank_two_four_literal_pure ha ho S M C four
  refine ⟨?_,v,P,Q,C,alg,dis,fit,pd,qd,rep⟩
  by_contra late
  exact marked13_late_clean_pure_impossible ha ho S M C alg dis sq late

theorem order13_fin19_remaining_marked {A:Fin 19→Fin 19→K} {b:Vec K 19}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13) :
    ∃ (a r:ℕ) (U:Submodule K (Vec K 19)) (v:Vec K 19) (G:K[X]),
      Chart13 A 1 a r U v G ∧
        ((3≤r∧r≤5) ∨ (r=2 ∧ (terminal 18:Vec K 19)∈treeSpace A 7 ∧ MulClosed U ∧
          (∀i,Live U i→v i=0) ∧ ∃ P Q:K[X],G=P*Q ∧ P.natDegree=a-2 ∧ Q.natDegree=3 ∧
          (∀i,v i≠0→v i=P.eval (nodes A i)))) := by
  have S:=order13_actual_saturation ha ho
  have M:=order13_fin19_prefix_margin ha ho
  obtain ⟨a,r,U,w,G,C⟩:=actual_chart13 ha ho S M
  by_cases hr:r=2
  · subst r
    obtain ⟨early,v,P,Q,cv,alg,dis,fit,pd,qd,rep⟩:=marked13_rank_two_early_factors ha ho S M C
    exact ⟨a,2,U,v,G,cv,Or.inr ⟨rfl,early,alg,dis,P,Q,fit,pd,qd,rep⟩⟩
  · have size:=C.marked.rank
    have low:=C.marked.rTwo
    have rtail:=Submodule.finrank_mono (marked13_terminal_in_core C)
    rw [tail_rank 1 (by decide)] at rtail
    exact ⟨a,r,U,w,G,C,Or.inl ⟨by omega,by omega⟩⟩

end RKCert.Paired.FiniteMidpoint
