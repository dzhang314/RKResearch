module

public import RKCert.ReviewedNative.ERKOrder15TerminalSquareCredit
import RKCert.ReviewedNative.ERKOrder15MassRigidity
import all RKCert.ReviewedNative.ERKOrder15GradeTen

@[expose] public section

/-! # Exactly two actual clock shifts suffice after terminal entry

The previous private shift-mod-mesh proof is reused through the pinned
native module. Terminal mass, rather than a fictitious third ordinary
square shift, supplies the last independent scalar test. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial Module RKCert.Endpoint RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

omit [CharZero K] in
private theorem adjacent_unit_of_charged (ho : HasOrder 15 A b) (seed : firstSeed A b=0)
    (P : K[X]) (pd : P.natDegree≤8) (k : ℕ) (hk : k≤5)
    (h : chargedProbe A b k (evalNodes A P)=0) :
    (formalPrimitive (X^k*P)).eval 1=(formalPrimitive (X^(k+1)*P)).eval 1 := by
  simp only [chargedProbe,seed,ite_true,LinearMap.sub_apply,sub_eq_zero] at h
  rw [formalPrimitive_eq_native,formalPrimitive_eq_native,←probe_evalNodes ho P k (by omega),
    ←probe_evalNodes ho P (k+1) (by omega)]
  exact h

/-- The square of the physical head and its next two shifts actually
belong to the grade-ten head band. No further square credit is assumed. -/
theorem Order15PaidStaircase.three_terminal_squares (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder 15 A b)
    (seed : firstSeed A b=0) (term : coordinate (K:=K) (Fin.last s)∈treeSpace A 8)
    (dis : ∀ i, LiveCore.live U i → w i=0) :
    ∀ k≤2, (diag (nodes A)^k) (w*w)∈order15HeadBand A a 2 10 U w := by
  let D := diag (nodes A)
  let B := a-4
  have ab := S.base_degree
  obtain ⟨w0,wp⟩ := S.terminal_head_first_powers ho seed term dis
  have sq := square_shifts_of_ordinary_head w0 wp
  have w5 : w∈zeroSpace A 5 := by simpa using wp 0 (by decide)
  have data (i : ℕ) : ∃ P : K[X], i≤2 → P.natDegree≤a ∧ P.coeff 0=0 ∧
      (D^i) (w*w)-evalNodes A P∈order15HeadBand A a 2 10 U w ∧
      (∀ k≤B,chargedProbe A b k (evalNodes A P)=0) ∧
      (formalPrimitive P).eval 1=b (Fin.last s)*P.eval 1 := by
    by_cases h : i≤2
    · obtain ⟨P,m⟩ := S.terminal_ghost_decompose ha ho seed term w0 w5 (sq i h).1 (sq i h).2
      exact ⟨P,fun _=>m⟩
    · exact ⟨0,fun z=>(h z).elim⟩
  choose P ok using data
  have shift (i : ℕ) (hi : i<2) : ∃ t : K,X*P i-P (i+1)=C t*G := by
    obtain ⟨pd,_,pc,_⟩ := ok i hi.le
    obtain ⟨qd,_,qc,_⟩ := ok (i+1) (by omega)
    rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply] at qc
    exact grade_ten_mesh_shift S ho pd qd pc qc
  have conv (i : ℕ) (hi : i<2) :
      ∃ t : K,D (evalNodes A (P i))-evalNodes A (P (i+1))=t•evalNodes A G := by
    obtain ⟨t,e⟩ := shift i hi
    refine ⟨t,?_⟩
    rw [clock_eval_X,←map_sub,e]
    ext k; simp
  have chargedG (k : ℕ) (hk : k≤5) : chargedProbe A b k (evalNodes A G)=0 := by
    apply chargedProbe_paid ha ho S.frame.lastActive k (S.frame.escapePaid S.first.paid)
    simp [terminalDebit,seed]
    omega
  have account := extend_charged_probe_window (fun i=>evalNodes A (P i)) (evalNodes A G) B 2
    (fun i hi => (ok i hi).2.2.2.1) conv (fun k hk=>chargedG k (by dsimp [B] at hk;omega))
  obtain ⟨t,e⟩ := shift 0 (by decide)
  obtain ⟨p0,o0,_,_,m0⟩ := ok 0 (by decide)
  obtain ⟨p1,_,_,_,m1⟩ := ok 1 (by decide)
  have gd := S.first.degree
  have root := order15_escape_origin ha S.frame G S.first.paid
  have vanish : P 0=0 := RKCert.ReviewedNative.JacobiMoments.two_shift_terminal_rigid
    ab.1 ab.2 p0 p1 o0 gd root
    (fun k hk=>adjacent_unit_of_charged ho seed (P 0) (by omega) k (by omega)
      (account k (by dsimp [B];omega)))
    (fun k hk=>adjacent_unit_of_charged ho seed G (by omega) k hk (chargedG k hk))
    m0 m1 e
  have all (i : ℕ) (hi : i≤2) : P i=0 := by
    induction i with
    | zero => exact vanish
    | succ i ih =>
      obtain ⟨t,eq⟩ := shift i (by omega)
      rw [ih (by omega),mul_zero,zero_sub] at eq
      by_cases z : t=0
      · simpa [z] using eq
      · have d := congrArg natDegree eq
        rw [natDegree_neg,natDegree_C_mul z,gd] at d
        have q := (ok (i+1) hi).1
        omega
  intro i hi
  have e := (ok i hi).2.2.1
  rwa [all i hi,map_zero,sub_zero] at e

end
end RKResearch.Certified.Graded
