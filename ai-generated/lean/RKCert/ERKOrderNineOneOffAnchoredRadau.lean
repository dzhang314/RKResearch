module

public import RKCert.ERKOrderNineOneOffCleanClocks
public import RKCert.ERKOrderNineRadau

@[expose] public section

/-! # Exact anchored-polynomial kernel and the paid terminal coordinate -/
namespace RKCert.Paired.OneOff
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

noncomputable def anchorRadau : K[X] := X*radauQuartic

theorem anchorRadau_at_one : (anchorRadau : K[X]).eval 1=1/126 := by
  norm_num [anchorRadau,radauQuartic]

omit [CharZero K] in
theorem anchorRadau_coeff_five : (anchorRadau : K[X]).coeff 5=1 := by
  rw [anchorRadau,coeff_X_mul]
  simp [radauQuartic,coeff_monomial]

/-- Any degree-five polynomial part in a grade-five relation at p9
belongs to this one-dimensional span, with its own top coefficient. -/
theorem anchored_radau_span {A : Fin s→Fin s→K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b 9) (P : K[X]) (dp : P.natDegree≤5)
    (p0 : P.eval 0=0)
    (mom : ∀ j : Fin 4, probe A b j.val (evalNodes A P)=0) :
    P=C (P.coeff 5)*anchorRadau := by
  have hC : P.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
  obtain ⟨Q,e⟩ := X_dvd_iff.mpr hC
  have dq : Q.natDegree≤4 := by
    by_cases n : Q=0
    · simp [n]
    · have h := natDegree_mul X_ne_zero n
      rw [←e,natDegree_X] at h
      omega
  have dec := radau_quartic_decoder Q dq (fun j =>
    anchor_probe_coeff ho Q dq (by have := j.isLt; omega) (e ▸ mom j))
  have cf : P.coeff 5=Q.coeff 4 := by rw [e,coeff_X_mul]
  calc
    P=X*Q := e
    _=X*(C (Q.coeff 4)*radauQuartic) := congrArg (X * ·) dec
    _=C (P.coeff 5)*anchorRadau := by rw [cf,anchorRadau]; ring

/-- Under maximal rank the actual terminal row kills every third-grade
defect. The proof pays exactly grade three plus grade five plus one. -/
theorem rank_five_full_terminal_defect {A : Fin 12→Fin 12→K} {b u : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rank : finrank K (treeSpace A 5)=10) (hu : u∈zeroSpace A 3) :
    u (Fin.last 11)=0 := by
  obtain ⟨hb,_,_,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨_,_,e,_,_,_⟩ := order9_rank_five_full ha ho rank
  let j : Fin 12 := Fin.last 11
  let w : Vec K 12 := Pi.single j 1
  have hm : u*w∈zeroSpace A (3+5) := zeroSpace_mul_treeSpace ho (by decide : 5+1≤9) hu e
  have p : probe A b 0 (u*w)=0 := probe_zeroSpace ho (k:=0) (by decide) hm
  have e1 : u*w=(u j) • w := by
    ext l
    by_cases h : l=j
    · simp [w,h,Pi.mul_apply]
    · simp [w,h,Pi.mul_apply]
  have wb : probe A b 0 w=b j := by simp [probe,row_apply,w,Pi.single_apply]
  rw [e1,map_smul,smul_eq_mul,wb] at p
  exact (mul_eq_zero.mp p).resolve_right hb

end RKCert.Paired.OneOff
