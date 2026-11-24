module

public import RKCert.DirkClockRetractionOps
public import RKCert.DirkWeightedFiveComplete

@[expose] public section

/-! # Native fifth-debut contradiction for any five-grade clock core

Unlike the ordinary masked algebra argument, this version does not
require the core to be closed under products. The weighted package is
derived entirely from original-array stage and moment conditions; the
contracted operator is not asserted to have Runge--Kutta order.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint RKCert.OneEscape RKCert.FourDebut
open RKCert.Paired.LocalProjection RKCert.Paired.PivotProjection
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s→Fin s→K} {b w : Vec K s} {U : Submodule K (Vec K s)}

set_option maxHeartbeats 1200000 in
theorem projected_weighted_five (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (inc : U≤zeroSpace A 5)
    (band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k)) :
    Nonempty (WeightedFive K s) := by
  obtain ⟨P⟩ := exists_clock_retraction (nodes A) U inv
  let c := nodes A
  let C := diag c
  let N := mat A
  let F := zeroSpace A
  let W := chain C ⊥ (P.projection w)
  have paid (j : ℕ) (hj : 5≤j) (hu : j≤7) : F j=chain C U w (j-4) := by
    have e := band (j-5) (by omega)
    rwa [show 5+(j-5)=j by omega,show 1+(j-5)=j-4 by omega] at e
  have mapPaid (j : ℕ) (hj : 5≤j) (hu : j≤7) {x : Vec K s} (hx : x∈F j) :
      P.projection x∈W (j-4) := by
    change P.projection x∈chain C ⊥ (P.projection w) (j-4)
    rw [←P.map_chain,←paid j hj hu]
    exact Submodule.mem_map_of_mem hx
  have hscalar (H : K[X]) : weightedEval c (1:Vec K s) H=evalNodes A H := by
    ext i
    simp [c]
  refine ⟨⟨c,P.projection 1,P.projection w,P.contractedOp N,
    P.diagonal*((fun i => A i i)*P.diagonal),
    P.contractedOp_causal (causalDiag_mat ha),?_,?_,?_⟩⟩
  · intro H dH vanish
    have e := (OrdinaryTrace.scalar A dH).probe ho 0 (by omega)
    simp only [probe,pow_zero,mul_one,one_mul] at e
    have rowU (x : Vec K s) (hx : x∈U) : row b x=0 := by
      have h := probe_zeroSpace ho (by omega : 0+5+1≤p) (inc hx)
      simpa only [probe,pow_zero,mul_one] using (LinearMap.mem_ker.mp h)
    rw [←P.preserve_functional (row b) rowU (evalNodes A H)] at e
    rw [←hscalar,P.weighted,vanish,map_zero] at e
    exact e.symm
  · intro j jl ju H q dH dq
    let v := weightedEval c (1:Vec K s) H-weightedEval c w q
    have qmem : weightedEval c w q∈F j := by
      rw [paid j jl (by omega)]
      have a := polynomial_head_mem (U:=U) (c:=c) (w:=w) dq
      convert a using 1
      ext i
      simp [weightedEval_apply,mul_comm]
    have tr : OrdinaryTrace A j v H := by
      change OrdinaryTrace A j (weightedEval c (1:Vec K s) H-weightedEval c w q) H
      rw [hscalar]
      exact (OrdinaryTrace.scalar A dH).sub_pure qmem
    have old := mapPaid (j+1) (by omega) (by omega) tr.primitive.pure
    have cor := mapPaid (j+1) (by omega) (by omega)
      ((zeroSpace_mono A (show 6≤j+1 by omega))
        (mat_zeroSpace_charZero A 5 (inc (P.defect v))))
    change P.contractedOp N
      (weightedEval c (P.projection 1) H-weightedEval c (P.projection w) q) -
        weightedEval c (P.projection 1) (formalPrimitive H) ∈ W (j-3)
    rw [←P.weighted,←P.weighted,←P.weighted,←map_sub,P.contractedOp_on_projection,
      hscalar (formalPrimitive H),sub_right_comm,←map_sub]
    have h := (W ((j+1)-4)).sub_mem old cor
    rwa [show j+1-4=j-3 by omega] at h
  · intro H dH
    let x := weightedEval c (1:Vec K s) H
    have xPaid : x∈treeSpace A 5 := by
      change weightedEval c (1:Vec K s) H∈treeSpace A 5
      rw [hscalar]
      exact (OrdinaryTrace.scalar A dH).stage
    have old : P.projection (commutatorR N C x)∈W 3 :=
      mapPaid 7 (by decide) (by decide) (commutator_mem_zeroSpace ho 5 (by omega) xPaid)
    have n6 (t : Vec K s) (ht : t∈U) : N t∈F 6 :=
      mat_zeroSpace_charZero A 5 (inc ht)
    have n7 (t : Vec K s) (ht : t∈U) : P.projection (N t)∈W 3 :=
      mapPaid 7 (by decide) (by decide) ((zeroSpace_mono A (by decide : 6≤7)) (n6 t ht))
    have err : commutatorR (P.contractedOp N) C (P.projection x) -
        P.projection (commutatorR N C x) ∈ W 3 := by
      rw [P.contractedOp_commutator_error]
      refine (W 3).add_mem ((W 3).add_mem ((W 3).sub_mem (n7 _ (P.defect (C x))) ?_) ?_)
        (n7 _ (P.defect (N (P.projection x))))
      · exact mapPaid 7 (by decide) (by decide) (diag_zeroSpace A 6 (n6 _ (P.defect x)))
      · exact mapPaid 7 (by decide) (by decide) (mat_zeroSpace_charZero A 6 (n6 _ (P.defect x)))
    change commutatorR (P.contractedOp N) C (weightedEval c (P.projection 1) H)∈W 3
    rw [←P.weighted]
    simpa only [sub_add_cancel] using (W 3).add_mem err old

theorem no_invariant_grade5_head (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (inc : U≤zeroSpace A 5)
    (band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k)) : False := by
  obtain ⟨D⟩ := projected_weighted_five ha ho hp inv inc band
  exact D.impossible

end
end RKCert.Paired
