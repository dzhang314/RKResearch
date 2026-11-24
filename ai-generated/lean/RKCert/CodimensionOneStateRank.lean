module
public import RKCert.OrderNineSevenOff

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial Module RKCert.Paired RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] {s:ℕ}

/-- Two consecutive scalar tests on a codimension-one off interpolation grid.
The head need only have degree at most two, and the number of knots is free. -/
theorem off_interpolation_pair {q : ℕ} [Infinite K] (S : Finset K) (N:S.card=q+2)
    (P Q : K[X]) (dP:P.natDegree≤2) (dQ:Q.natDegree<q+2) (nondiv : ¬P∣Q)
    (pn : ∀x∈S,P.eval x≠0) (T U : K[X]) (dT:T.natDegree≤q) (dU:U.natDegree≤q)
    (atQ:∀x∈S,Q.eval x=P.eval x*T.eval x) (atXQ:∀x∈S,(X*Q).eval x=P.eval x*U.eval x) : False := by
  let R:=nodalHull S
  have dr : R.natDegree=q+2 := (natDegree_nodalHull S).trans N
  have cp : IsCoprime P R := by
    unfold R nodalHull
    exact IsCoprime.prod_right fun x hx=>((irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
      fun h=>pn x hx (dvd_iff_isRoot.mp h)).symm
  have dx : (X*Q).natDegree≤q+2 := (natDegree_mul_le ..).trans (by rw [natDegree_X]; omega)
  obtain ⟨a,ea⟩:=scalar_hull_of_roots S (Q-P*T)
    ((natDegree_sub_le_of_le dQ.le (natDegree_mul_le_of_le dP dT)).trans (by omega))
    (fun x hx=>by rw [eval_sub,eval_mul,atQ x hx,sub_self])
  obtain ⟨b,eb⟩:=scalar_hull_of_roots S (X*Q-P*U)
    ((natDegree_sub_le_of_le dx (natDegree_mul_le_of_le dP dU)).trans (by omega))
    (fun x hx=>by rw [eval_sub,atXQ x hx,eval_mul,sub_self])
  change Q-P*T=C a*R at ea
  change X*Q-P*U=C b*R at eb
  have an : a≠0 := by intro e; rw [e,map_zero,zero_mul] at ea; exact nondiv ⟨T,sub_eq_zero.mp ea⟩
  let V:K[X]:=C a*X-C b
  have dV:P∣V:=cp.dvd_of_dvd_mul_right (show P∣V*R from ⟨U-X*T,by dsimp [V]; linear_combination -X*ea+eb⟩)
  have nz:V≠0:=by
    intro e
    apply an
    simpa [V,coeff_C_mul,coeff_C] using congrArg (fun F:K[X]=>F.coeff 1) e
  have tiny:V.natDegree≤1:=natDegree_sub_le_of_le
    ((natDegree_C_mul_le a (X:K[X])).trans (natDegree_X (R:=K)).le) (show (C b).natDegree≤0 by simp)
  have dp1: P.natDegree≤1:=(natDegree_le_of_dvd dV nz).trans tiny
  have full:(Q-P*T).natDegree=q+2:=by rw [ea,natDegree_C_mul an,dr]
  have low:=(natDegree_sub_le_of_le (show Q.natDegree≤q+1 by omega)
    (natDegree_mul_le_of_le dp1 dT))
  omega

/-- The fixed five-on-node interpolation profile, with a free off-test degree. -/
noncomputable def pairBase (A : Fin s→Fin s→K) (q : ℕ) :
    ((Fin 5→K)×(Fin (q+1)→K)) →ₗ[K] Vec K s :=
  (polyEval A 4).coprod ((diag (qdef A)).comp (polyEval A q))

theorem pairBase_apply (A : Fin s→Fin s→K) (q : ℕ) (v : (Fin 5→K)×(Fin (q+1)→K)) :
    pairBase A q v=evalNodes A (ofFn 5 v.1)+diag (qdef A) (evalNodes A (ofFn (q+1) v.2)) := by
  rw [evalNodes_ofFn A 4,evalNodes_ofFn A q]
  rfl

theorem pairBase_injective {q:ℕ} {A : Fin s→Fin s→K} (M : 5≤(onNodes A).card)
    (N : q+1≤(supportedNodes A (qdef A)).card) : Function.Injective (pairBase A q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let V:=ofFn 5 z.1
  let W:=ofFn (q+1) z.2
  have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
  have dW : W.natDegree<q+1:=ofFn_natDegree_lt (by omega) _
  have atAll (i : Fin s) : V.eval (nodes A i)+qdef A i*W.eval (nodes A i)=0 := by
    rw [pairBase_apply] at hz
    exact congrFun hz i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' V (onNodes A)
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_onNodes.mp hx; simpa [hi] using atAll i) (by omega)
  have w0 : W=0:=eq_zero_of_natDegree_lt_card_of_eval_eq_zero' W (supportedNodes A (qdef A))
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx
                  exact (mul_eq_zero.mp (by simpa [v0] using atAll i)).resolve_left hi) (by omega)
  exact Prod.ext (injective_ofFn 5 (v0.trans (ofFn_zero _).symm))
    (injective_ofFn (q+1) (w0.trans (ofFn_zero _).symm))

theorem off_poly_of_base {q:ℕ} {A : Fin s→Fin s→K} (M:5≤(onNodes A).card)
    (P F : K[X]) (fit : ∀i,qdef A i≠0→P.eval (nodes A i)=qdef A i)
    (onF : ∀x∈onNodes A,F.eval x=0)
    (range : evalNodes A F∈LinearMap.range (pairBase A q)) :
    ∃ T:K[X], T.natDegree≤q ∧ ∀x∈supportedNodes A (qdef A), F.eval x=P.eval x*T.eval x := by
  obtain ⟨v,hv⟩:=range
  rw [pairBase_apply] at hv
  let V:=ofFn 5 v.1
  let T:=ofFn (q+1) v.2
  have he (i : Fin s) : V.eval (nodes A i)+qdef A i*T.eval (nodes A i)=F.eval (nodes A i) :=
    congrFun hv i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (onNodes A) (fun x hx=>by
    obtain ⟨i,hi,rfl⟩:=mem_onNodes.mp hx
    simpa [hi,onF _ hx] using he i) (by
      have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
      omega)
  refine ⟨T,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _),?_⟩
  intro x hx
  obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx
  simpa [v0,fit i hi] using (he i).symm

variable [CharZero K]

theorem pairBase_le_both {q : ℕ} (hq:4≤q) {A : Fin s→Fin s→K} (P:K[X])
    (fit:∀i,qdef A i≠0→P.eval (nodes A i)=qdef A i) :
    LinearMap.range (pairBase A q)≤treeSpace A (q+2) ⊓ onOffSpace A := by
  rintro _ ⟨v,rfl⟩
  rw [pairBase_apply]
  refine ⟨(treeSpace A (q+2)).add_mem ?_ ?_,pairProfile_mem_onOffSpace fit _ _⟩
  · apply evalNodes_mem_treeSpace; have:=ofFn_natDegree_lt (by decide : 0<5) v.1; omega
  · apply zeroSpace_le_treeSpace
    rw [Nat.add_comm q 2]
    apply chainSpan_le_zeroSpace (qdef_mem A) q
    exact chainSpan_iff_polynomial.mpr ⟨_,Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _),rfl⟩

/-- All (5+q+2) branch-state functions are representable in the actual
grade-(q+2) tree space when there are exactly five on and (q+2) off
sites, q≥4, and the degree-two-or-lower head does not divide the on hull. -/
theorem five_on_state_le {q:ℕ} (hq:4≤q) {A : Fin s→Fin s→K} (M:(onNodes A).card=5)
    (N:(supportedNodes A (qdef A)).card=q+2) (P : K[X]) (dP:P.natDegree≤2)
    (fit : ∀i,qdef A i≠0→P.eval (nodes A i)=qdef A i)
    (nondiv : ¬P∣nodalHull (onNodes A)) : onOffSpace A≤treeSpace A (q+2) := by
  let : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  let Q:=nodalHull (onNodes A)
  let V:=treeSpace A (q+2) ⊓ onOffSpace A
  have dQ : Q.natDegree=5 := (natDegree_nodalHull _).trans M
  have dr : finrank K (LinearMap.range (pairBase A q))=5+(q+1) := by
    rw [LinearMap.finrank_range_of_inj (pairBase_injective (by omega : 5≤(onNodes A).card)
        (by omega : q+1≤(supportedNodes A (qdef A)).card)),Module.finrank_prod,
        Module.finrank_fin_fun,Module.finrank_fin_fun]
  have hdim : 5+(q+2)≤finrank K V := by
    by_contra! small
    have inc : LinearMap.range (pairBase A q)≤V := pairBase_le_both hq P fit
    have e:=Submodule.eq_of_le_of_finrank_le inc (by omega)
    have mh (F:K[X]) (d:F.natDegree≤q+2) : evalNodes A F∈LinearMap.range (pairBase A q) := by
      rw [e]
      refine ⟨evalNodes_mem_treeSpace A F d,?_⟩
      have z : evalNodes A (0:K[X])=0 := by ext i; simp
      have hs := pairProfile_mem_onOffSpace fit F (0:K[X])
      rw [z,map_zero,add_zero] at hs
      exact hs
    obtain ⟨T,dT,tq⟩:=off_poly_of_base (by omega : 5≤(onNodes A).card) P Q fit
      (fun x h=>nodalHull_eval_of_mem h) (mh Q (by omega))
    have dx : (X*Q).natDegree≤q+2 := (natDegree_mul_le ..).trans (by rw [natDegree_X]; omega)
    obtain ⟨U,dU,tu⟩:=off_poly_of_base (by omega : 5≤(onNodes A).card) P (X*Q) fit
      (fun _ h=>by rw [eval_mul,show Q.eval _=0 from nodalHull_eval_of_mem h,mul_zero]) (mh _ dx)
    exact off_interpolation_pair _ N P Q dP (by omega) nondiv (fun _ hx=>by
      obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx; rwa [fit i hi]) T U dT dU tq tu
  have eqv : V=onOffSpace A:=Submodule.eq_of_le_of_finrank_le inf_le_right (by
    rw [onOffSpace_rank,M,N]; exact hdim)
  exact eqv ▸ (show V≤treeSpace A (q+2) from inf_le_left)

end RKCert.FixedFactor
