module
public import RKCert.DirkLocalLeak
public import RKCert.DirkLocalWords
public import RKCert.DirkWeightedFourInterface
@[expose] public section
namespace RKCert.Paired.LocalProjection
open RKCert.Endpoint Polynomial RKCert.OneEscape RKCert.Paired.Terminal
variable {K:Type*} [Field K] {s m:ℕ}
noncomputable section

theorem transMatch {A:Fin s→Fin s→K} (ha:LowerArray A) (i:Fin s) (x z:Vec K s)
    (hh:∀l,i ≤ l → x l=z l) : transMat A x i=transMat A z i := by
  change (∑l:Fin s, A l i*x l)=(∑l:Fin s, A l i*z l)
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl:i ≤ l
  · rw [hh l hl]
  · rw [ha l i (lt_of_not_ge hl),zero_mul,zero_mul]

variable [CharZero K] {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

/-- A genuine local D3 line in an even-boundary tableau produces the
weighted four-debut package, including both graded error families and exact
quadrature after the projection. It is not a reduced RK method. -/
theorem weighted_four_of_local (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (localc:(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1) :
    Nonempty (WeightedFour K (s+1)) := by
  classical
  let y:=mirror A
  let d:=tau A b
  let N:=transMat A
  obtain ⟨w,hw,words⟩:=local_words hm ha ho he localc
  obtain ⟨h,hd,pre,loc,zeroSum⟩:=local_pivot hm ha ho he localc
  let Q:=kill d h
  let M:=Q.comp N
  let W:=Q w
  let base:=Q b
  have Qweight (v:Vec K (s+1)) (P:K[X]):Q (weightedEval y v P)=weightedEval y (Q v) P :=
    kill_weighted y d h loc v P
  have projWord (r:ℕ) (hr:1≤r) (rh:r≤m-2) :
      (dirkBack A b r).map Q=chain (diag y) ⊥ W (r-1) := by
    rw [words r hr rh,word_one hm ha ho he]
    exact kill_chain y d h loc hd w (r-1)
  have dword:d∈dirkBack A b 1 := by
    rw [word_one hm ha ho he]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨_,ct,col,_⟩:=last_physical hm ha ho he
  have pureN {j:ℕ} {v:Vec K (s+1)} {P:K[X]} (hj:3≤j) (jh:j+1≤m)
      (tr:ReverseTrace A b (2*m) j v P) :
      N v-weightedEval y b (formalPrimitive P)∈dirkBack A b (j-1) := by
    have wt:(N v-weightedEval y b (formalPrimitive P)) (Fin.last s)=0 := by
      simp [N,y,ReverseHermite.trans_terminal _ col,mirror,ct]
    have paid:=marked_to_words hm ha ho he (j:=j+1) (by omega) jh ((tr.primitive ho (by omega)).pure) wt
    simpa only [show j+1-2=j-1 by omega] using paid
  refine ⟨⟨y,base,W,M,?_,?_,?_,?_⟩⟩
  · intro i x z hx
    exact kill_causal d h pre i (N x) (N z) (fun l hl=>transMatch ha l x z (fun k hk=>hx k (hl.trans hk)))
  · intro P hp
    change row (weightedEval y (Q b) P) 1=_
    rw [←Qweight,preserves_sum d _ h zeroSum]
    exact (ReverseTrace.scalar A b hp).weighted_sum ho (by omega)
  · intro j hj jh P q hp hq
    have hqword:weightedEval y w q∈dirkBack A b (j-2) := by
      rw [words (j-2) (by omega) (by omega),show j-2-1=j-3 by omega]
      have hh:=RKCert.FourDebut.polynomial_head_mem (c:=y) (w:=w) (U:=dirkBack A b 1) hq
      convert hh using 1
      ext i
      simp [mul_comm]
    let x:=weightedEval y b P-weightedEval y w q
    have tr:ReverseTrace A b (2*m) j x P :=
      (ReverseTrace.scalar A b hp).sub_pure (back_sub_marked ho (by omega) (by omega) hqword)
    have qx:Q x=weightedEval y base P-weightedEval y W q := by
      dsimp only [x];rw [map_sub,Qweight,Qweight]
    have leak:M (Q x)-Q (N x)∈(dirkBack A b (j-1)).map Q :=
      Submodule.map_mono (twoOrbit_mono _ _ _ _ _ (by omega : 2≤j-1)) (local_leak_bound h dword x)
    have hz:=((dirkBack A b (j-1)).map Q).add_mem leak ⟨_,pureN hj (by omega) tr,rfl⟩
    rw [show Q (N x-weightedEval y b (formalPrimitive P)) = Q (N x)-weightedEval y base (formalPrimitive P) by rw [map_sub,Qweight],sub_add_sub_cancel,qx,projWord _ (by omega) (by omega)] at hz
    simpa only [show j-1-1=j-2 by omega] using hz
  · intro j hj jh P hp
    let x:=weightedEval y b P
    have orig:commutatorR N (diag y) x∈dirkBack A b j := by
      have wt:commutatorR N (diag y) x (Fin.last s)=0 := by
        change (mirror A (Fin.last s)*transMat A x (Fin.last s) -
          transMat A _ (Fin.last s))-transMat A _ (Fin.last s)=0
        simp [ReverseHermite.trans_terminal _ col,mirror,ct]
      have hh:=marked_to_words hm ha ho he (j:=j+2) (by omega) (by omega)
        ((ReverseTrace.scalar A b hp).commutator ho (by omega)) wt
      simpa using hh
    have leak:commutatorR M (diag y) (Q x)-Q (commutatorR N (diag y) x)∈
        (dirkBack A b j).map Q :=
      Submodule.map_mono (twoOrbit_mono _ _ _ _ _ hj) (local_commutator_bound h dword loc x)
    have hz:=((dirkBack A b j).map Q).add_mem leak ⟨_,orig,rfl⟩
    rw [sub_add_cancel,projWord _ (by omega) (by omega)] at hz
    dsimp only [x] at hz
    rwa [Qweight] at hz

end
end RKCert.Paired.LocalProjection
