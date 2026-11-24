module

public import RKCert.ReviewedNative.LocalLinearContrast

@[expose] public section

/-! # Small true mixed traces force chronological reverse primitive tests -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
variable {h r j : ℕ} {U : Submodule K (Fin s→K)} {τ f : Fin s→K} {P Q : K[X]}

set_option maxHeartbeats 1000000 in
theorem physical_local_reverse_port (ha : ∀i j,i ≤ j → A i j=0) (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ)
    (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (pay : 2*h+3≤p) (h7 : 7≤h) (fit : LocalLinearTraces A b U τ f r j P Q)
    (dQ : Q.natDegree≤4) (dP : P=0 ∨ P.natDegree+r+1≤4) (qn : Q≠0)
    (H : K[X]) (dH : H.natDegree≤2) (hn : H≠0) :
    ∃ a : K, H.eval a≠0 ∧
      ∀ R : K[X], H.natDegree+R.natDegree+4≤h → (primitive ((H*R)*Q)).eval a=0 := by
  let y := reflectedClock A
  let L := primitiveBack A b
  let N := mat A.transpose
  let W := contrast y b f Q
  have rb : 1≤r ∧ r≤2 := by rcases F.coreRank with z|z <;> omega
  have mono : Monotone L := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have coreJ : U≤L (h-1) := F.core.le.trans (mono (by omega))
  have coreH : U≤L h := coreJ.trans (mono (by omega))
  have Npay : (L (h-1)).map N≤L h := by
    have e : (L (h-1)).map N≤L ((h-1)+1) := adjointFlag_transpose _ _
    rwa [show h-1+1=h by omega] at e
  obtain ⟨u,hu,form⟩ := contrast_decompose fit F.invariant
  let D := weightedEval y W H
  have noFit : D∉U := by
    intro now
    have sub : (H*P).natDegree≤h-r := by
      rcases dP with zz|bd
      · simp [zz]
      · exact natDegree_mul_le.trans (by omega)
    have tp := weighted_primitive_band F.headMem (H*P) sub
    have tH : weightedEval y τ (H*P)∈L h := by
      rw [show r+(h-r)=h by omega] at tp
      exact tp
    have uu : weightedEval y u H∈L h := coreH (reflected_clock_weighted_core F.invariant hu H)
    have bw : weightedEval y b (H*Q)∈L h := by
      have d : D=weightedEval y b (H*Q)-weightedEval y τ (H*P)-weightedEval y u H :=
        scaled_contrast_decomposition form
      have eq : weightedEval y b (H*Q)=D+weightedEval y τ (H*P)+weightedEval y u H := by rw [d]; abel
      rw [eq]
      exact (L h).add_mem ((L h).add_mem (coreH now) tH) uu
    have hz := weighted_reflected_annihilation_zero ho (d:=6) (g:=h+1)
      (natDegree_mul_le.trans (by omega) : (H*Q).natDegree≤6) (by omega) (by omega) (full.le bw)
    exact mul_ne_zero hn qn hz
  obtain ⟨i,w,hw,prior,bad⟩ := reverse_first_unmatched_joint y f D U
    (clock_mask_invariant (fun _ hu=>F.invariant (Submodule.mem_map_of_mem hu)))
    (clock_mask_invariant (fun _ hu=>fit.preserves (Submodule.mem_map_of_mem hu))) noFit
  have fz : f i=0 := by
    by_contra live
    apply bad
    refine ⟨0,U.zero_mem,fun k _ _ same=>?_⟩
    simp only [Pi.zero_apply,D,weightedEval_apply,W]
    simp [contrast,same,live]
  have qnz : Q.eval (y i)≠0 := by
    intro killed
    apply bad
    refine ⟨0,U.zero_mem,fun k _ yy _=>?_⟩
    simp only [Pi.zero_apply,D,weightedEval_apply,W]
    simp [contrast,yy,killed]
  have hnz : H.eval (y i)≠0 := by
    intro killed
    apply bad
    refine ⟨0,U.zero_mem,fun k _ yy _=>?_⟩
    simp only [Pi.zero_apply,D,weightedEval_apply,W]
    simp [yy,killed]
  have τoff (k : Fin s) (yy : y k=y i) (ff : f k=f i) : τ k=0 := by
    have raw := congrFun fit.tauTrace k
    simp only [Pi.mul_apply,weightedEval_apply] at raw
    rw [ff,fz,mul_zero,show reflectedClock A k=y i from yy] at raw
    exact (mul_eq_zero.mp raw.symm).resolve_left qnz
  refine ⟨y i,hnz,fun R budget=>?_⟩
  let M := H*R
  let G := primitive (M*Q)
  have mDeg : M.natDegree≤H.natDegree+R.natDegree := natDegree_mul_le
  have mq : (M*Q).natDegree≤h := natDegree_mul_le.trans (by omega)
  have balance := reflected_primitive_of_polynomial (A:=A) (b:=b) (by omega) (M*Q) mq
  have mp : (M*P).natDegree≤h-r-1 := by
    rcases dP with z|bd
    · simp [z]
    · exact natDegree_mul_le.trans (by omega)
  have nτ : N (weightedEval y τ (M*P))∈L h := by
    have e := weighted_primitive_band F.headMem (M*P) mp
    rw [show r+(h-r-1)=h-1 by omega] at e
    exact Npay (Submodule.mem_map_of_mem e)
  have nu : N (weightedEval y u M)∈L h :=
    Npay (Submodule.mem_map_of_mem (coreJ (reflected_clock_weighted_core F.invariant hu M)))
  have rem : N (weightedEval y W M)-weightedEval y b G∈L h := by
    have form' : W=weightedEval y b Q-weightedEval y τ P-u := form
    rw [scaled_contrast_decomposition (M:=M) form',map_sub,map_sub]
    have eq :
        N (weightedEval y b (M*Q))-N (weightedEval y τ (M*P))-N (weightedEval y u M)-weightedEval y b G =
          (N (weightedEval y b (M*Q))-weightedEval y b G)-N (weightedEval y τ (M*P))-N (weightedEval y u M) := by abel
    rw [eq]
    exact (L h).sub_mem ((L h).sub_mem balance nτ) nu
  let z := N (weightedEval y w R)-(N (weightedEval y W M)-weightedEval y b G)
  have wz : N (weightedEval y w R)∈L h :=
    Npay (Submodule.mem_map_of_mem (coreJ (reflected_clock_weighted_core F.invariant hw R)))
  have mem : z∈L h := (L h).sub_mem wz rem
  have same (k : Fin s) (ik : i≤k) : z k=G.eval (y k)*b k := by
    have before (l : Fin s) (kl : k<l) :
        (weightedEval y w R-weightedEval y W M) l=0 := by
      have e := prior l (ik.trans_lt kl)
      simp only [D,weightedEval_apply] at e
      simp only [Pi.sub_apply,weightedEval_apply,M,eval_mul,e]
      ring
    have eq := causal_transpose ha k (weightedEval y w R-weightedEval y W M)
      (fun l ll=>before l (Fin.rev_lt_rev.mp ll))
    change N (weightedEval y w R-weightedEval y W M) k=0 at eq
    rw [map_sub,Pi.sub_apply,sub_eq_zero] at eq
    simp [z,weightedEval_apply,eq]
  change z ∈ primitiveBack A b h at mem
  rw [F.band h (by omega) le_rfl] at mem
  obtain ⟨v,hv,T,_,parts⟩ := HeadFiber.exists_poly mem
  let kappa := G.eval (y i)
  change kappa=0
  by_contra kz
  let scale := H.eval (y i)*Q.eval (y i)/kappa
  apply bad
  refine ⟨scale • v,U.smul_mem scale hv,?_⟩
  intro k ik yy ff
  have vK : v k=kappa*b k := by
    have eq := congrFun parts k
    rw [same k ik,Pi.add_apply,weightedEval_apply,τoff k yy ff,mul_zero,add_zero,yy] at eq
    exact eq.symm
  simp only [Pi.smul_apply,smul_eq_mul,D,weightedEval_apply,W]
  rw [vK]
  simp only [contrast,ff,fz,ite_eq_left,yy]
  dsimp only [scale]
  rw [←mul_assoc,div_mul_cancel₀ _ kz]
  ring

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
