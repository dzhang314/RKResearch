module
public import RKCert.ERKOrder13MarkedEarlyGhost
public import RKCert.ERKOrder13MarkedLateGhost
public import RKCert.ERKOrder13MarkedPureFactor

@[expose] public section
/-! # Actual rank-two marked reduction left after the full-odd exclusion
All genuine ghosts are excluded; the remaining pure pencil factor is a
literal polynomial identity, not an inference from projected evaluations.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}

theorem marked13_rank_two_four_literal_pure (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (h4:finrank K (zeroSpace A 4)=4) :
    ∃ (v:Vec K (s+1)) (P Q:K[X]), Chart13 A 1 a 2 U v G ∧ MulClosed U ∧
      (∀ i,Live U i→v i=0) ∧ v*v∈Band13 A a 2 U v 8 ∧ G=P*Q ∧ P.natDegree=a-2 ∧ Q.natDegree=3 ∧
      (∀ i,v i≠0→v i=P.eval (nodes A i)) := by
  obtain ⟨v,C,alg,dis⟩:=marked13_four_clean ha ho S M C h4
  have vf: v∈defectPlus A 1 4 := (marked13_four_paid ho S M C h4).2
  have vs: v*v∈defectPlus A 1 8 := Fplus_mul (j:=4) (k:=4) vf vf
  obtain ⟨H,hd,gp,ghost⟩:=marked13_decompose ha ho S M C vs
  have h0:H=0 := by
    by_contra hn
    by_cases e:(terminal s:Vec K (s+1))∈treeSpace A 7
    · exact marked13_early_clean_ghost_impossible ha ho S M C h4 alg dis e hd hn gp ghost
    · exact marked13_late_clean_ghost_impossible ha ho S M C h4 alg dis e hd hn ghost
  have p:v*v∈Band13 A a 2 U v 8 := by
    have e:evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp
    simpa only [h0,e,sub_zero] using ghost
  obtain ⟨P,Q,_,_,eq,pd,qd,rep⟩:=marked13_pure_literal_factor ha ho S M C dis p
  exact ⟨v,P,Q,C,alg,dis,p,eq,pd,qd,rep⟩

end RKCert.Paired.FiniteMidpoint
