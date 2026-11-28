module

public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagData

@[expose] public section

namespace RKResearch.Certified.DIRK12FactorialTwentyFlag
open ScaledIntegerFlagReplay
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem check0 : (List.range 12).all (fun e => if 0≤e then blockP 0 e else true)=true := by decide +kernel

private theorem check1 : (List.range 11).all (fun e => if 1≤e then blockP 1 e else true)=true := by decide +kernel

private theorem check2 : (List.range 10).all (fun e => if 2≤e then blockP 2 e else true)=true := by decide +kernel

private theorem check3 : (List.range 9).all (fun e => if 3≤e then blockP 3 e else true)=true := by decide +kernel

private theorem check4 : (List.range 8).all (fun e => if 4≤e then blockP 4 e else true)=true := by decide +kernel

private theorem check5 : (List.range 7).all (fun e => if 5≤e then blockP 5 e else true)=true := by decide +kernel


private theorem checked (d : Nat) (h : d<6) :
    (List.range (12-d)).all (fun e => if d≤e then blockP d e else true)=true := by
  rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5

private theorem ordered_products (d e : Nat) (h : d+e<12) (hle : d≤e)
    (i : Fin (packet.size d)) (j : Fin (packet.size e)) :
    checkProduct packet d e i j=true := by
  have h0 := checked d (by omega)
  have h1 := List.all_eq_true.mp h0 e (List.mem_range.mpr (by omega))
  rw [if_pos hle] at h1
  exact List.all_eq_true.mp (List.all_eq_true.mp h1 i (List.mem_finRange i))
    j (List.mem_finRange j)

theorem product_receipt (d e : Nat) (h : d+e<12)
    (i : Fin (packet.size d)) (j : Fin (packet.size e)) :
    checkProduct packet d e i j=true := by
  by_cases le : d≤e
  · exact ordered_products d e h le i j
  · have h1 := ordered_products e d (by omega) (by omega) j i
    unfold checkProduct at h1 ⊢
    rw [Nat.add_comm d e,mul_comm]
    exact h1

end RKResearch.Certified.DIRK12FactorialTwentyFlag
