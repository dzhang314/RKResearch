module
public import RKCert.DirkPaidTailDual
public import RKCert.DirkFiveTenSurplus
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

omit [CharZero K] in
/-- Record the real C(2) test, not a chosen origin or quadrature convention. -/
private theorem twenty_choice (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) :
    ∃e:ℕ,e≤1 ∧ ((e=0 ∧ q₂ (mat A) (nodes A) 1=0) ∨ (e=1 ∧ q₂ (mat A) (nodes A) 1≠0)) ∧
    1+e≤finrank K (zeroSpace A 3) ∧
    (∀a,polyEval A (10-e) a∈zeroSpace A 10→a=0) ∧
    ∀a,polyEval A (9-e) a∈zeroSpace A 11→a=0:=by
  by_cases h:q₂ (mat A) (nodes A) 1=0
  · have org:=dirk_first_row ha h
    exact ⟨0,by decide,Or.inl ⟨rfl,h⟩,dirk_forward_rank_three ha ho (by decide),
      poly_separated_delayed_first org ho (by decide) (by decide),
      poly_separated_delayed_first org ho (by decide) (by decide)⟩
  · exact ⟨1,by decide,Or.inr ⟨rfl,h⟩,dirk_forward_rank_three_nonzero ha ho (by decide) h,
      poly_separated_delayed ho (by decide) (by decide),poly_separated_delayed ho (by decide) (by decide)⟩

omit [CharZero K] in
theorem twenty_midpoint_21 (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20)
    (rank:finrank K (zeroSpace A 3)+9≤finrank K (zeroSpace A 10)) :
    21≤finrank K (treeSpace A 10):=by
  obtain ⟨e,ei,_,h3,sep,_⟩:=twenty_choice ha ho
  have r:=treeSpace_rank_of_delayed (A:=A) (q:=10-e) (m:=10) (by omega) sep
  omega

structure TwentyRanks (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (e:ℕ) :Prop where
  flag: (e=0 ∧ q₂ (mat A) (nodes A) 1=0) ∨ (e=1 ∧ q₂ (mat A) (nodes A) 1≠0)
  three:finrank K (zeroSpace A 3)=1+e
  five:3+e≤finrank K (zeroSpace A 5) ∧ finrank K (zeroSpace A 5)≤4+e
  six:5+e≤finrank K (zeroSpace A 6)
  nine:8+e≤finrank K (zeroSpace A 9) ∧ finrank K (zeroSpace A 9)≤9+e
  ten:finrank K (zeroSpace A 10)=10+e
  eleven:finrank K (zeroSpace A 11)≤12+e
  scalar:∀a,polyEval A (10-e) a∈zeroSpace A 10→a=0
  full:treeSpace A 10=LinearMap.range (polyEval A (10-e)) ⊔ zeroSpace A 10
  dual:∀(q r:ℕ),10≤q→q+r=17→finrank K (treeSpace A q)=q+11 ∧
    finrank K (dirkBack A b r)=r ∧ dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r)
  words:∀j,2≤j→j≤9→marked A 20 j=dirkBack A b (j-2)
  seeds:backSeed1 A b=0 ∧ q₂ (transMat A) (mirror A) b=0

theorem twenty_rank_of_paid (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28)
    (rank:finrank K (zeroSpace A 3)+9≤finrank K (zeroSpace A 10)) :
    ∃e, TwentyRanks A b e:=by
  obtain ⟨e,er,flag,r3,s10,s11⟩:=twenty_choice ha ho
  have et:=twenty_midpoint_21 ha ho rank
  have dual (q r:ℕ) (low:10≤q) (sum:q+r=17):finrank K (treeSpace A q)=q+11 ∧
      finrank K (dirkBack A b r)=r ∧ dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r):=by
    have d:=paid_tail_duality ha ho (d:=21) (r₀:=7) et size (by decide) (r:=r) low (by omega)
    exact ⟨by have:=d.1;omega,d.2⟩
  have m10:=treeSpace_rank_of_delayed (A:=A) (q:=10-e) (m:=10) (by omega) s10
  have m11:=treeSpace_rank_of_delayed (A:=A) (q:=9-e) (m:=11) (by omega) s11
  have e10:finrank K (treeSpace A 10)=21:=(dual 10 7 (by decide) (by decide)).1
  have e11:finrank K (treeSpace A 11)=22:=(dual 11 6 (by decide) (by decide)).1
  have r₃:finrank K (zeroSpace A 3)=1+e:=by omega
  have r₁₀:finrank K (zeroSpace A 10)=10+e:=by omega
  have f6:=dirk_grade_six_surplus ha ho (by decide)
  have f5:=grade_five_ten_surplus ha ho (by decide)
  have e35:=flag_gain ha ho (a:=3) (n:=5) (by decide) (by decide) (by decide)
  have e69:=flag_gain ha ho (a:=6) (n:=9) (by decide) (by decide) (by decide)
  have e910:=flag_gain ha ho (a:=9) (n:=10) (by decide) (by decide) (by decide)
  refine ⟨e,⟨flag,r₃,⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,r₁₀,by omega,s10,
    poly_pure_full_of_paid_rank (by omega) s10 (by omega),dual,?_,?_⟩⟩
  · intro j low high
    exact (dual (19-j) (j-2) (by omega) (by omega)).2.2.1.symm
  · exact twoOrbit_initial_zero (dual 17 0 (by decide) (by decide)).2.1
end
end RKCert.Paired.Terminal

