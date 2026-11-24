module
public import RKCert.NodalHermiteRank
public import RKCert.DirkPolynomialMarked
public import RKCert.ReverseHermiteRank

@[expose] public section

/-! # The exact moment charge for a reflected nodal gain

An arbitrary number of failed blocks is paid by the genuine scalar moment
budget via a shifted Hilbert test. This uses signed weights and works over
all characteristic-zero fields, even when the observations are not ordered. -/
namespace RKCert.Endpoint
open RKCert.Paired Polynomial
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}

theorem failed_at_least_of_scalar_budget (c v:Vec K s) (U:Submodule K (Vec K s))
    (hm:MaskInvariant c U) (mass:∀w∈U,∑ i,w i=0) {r:ℕ}
    (mom:∀P:K[X],P.natDegree<2*r →
      (∑ i,weightedEval c v P i)=(formalPrimitive P).eval 1) :
    r≤(failedNodes c v U s).card := by
  by_contra! tooFew
  let S:=failedNodes c v U s
  let H:K[X]:=nodalHull S
  have hH:H.natDegree=S.card:=natDegree_nodalHull S
  have z:H=0:=by
    apply primitive_shift_detect H hH.le 1 one_ne_zero (k:=1)
    intro k
    let P:K[X]:=X^(1+k.val)*H
    have pay:P.natDegree<2*r:=by
      have h:=natDegree_mul_le (p:=X^(1+k.val)) (q:=H)
      rw [natDegree_X_pow,hH] at h
      have hlt:=k.isLt
      change S.card<r at tooFew
      dsimp only [P]
      omega
    have p0:P.eval 0=0:=by simp [P]
    have on (a:K)(aS:a∈S):P.eval a=0:=by
      simp [P,H,nodalHull_eval_of_mem aS]
    obtain ⟨w,hw,eq⟩:=exists_masked_prefix_lift c v hm s P p0 on
    have e:w=weightedEval c v P:=by
      ext i
      rw [weightedEval_apply,eq i i.isLt]
    simpa only [e,mom P pay] using mass w hw
  exact (monic_nodalHull S).ne_zero z

end
end RKCert.Endpoint

namespace RKCert.Paired.ReverseHull
open RKCert.Endpoint Polynomial Module
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ}
variable {A:Fin s→Fin s→K} {b:Vec K s}

/-- Exact scalar moments on the reflected numerical clock, without placing
any rooted-tree order hypothesis on a reflected method. -/
theorem reflected_scalar_budget (ho:HasTreeOrderAtLeast A b p) (P:K[X])
    (pay:P.natDegree+1≤p) :
    (∑ i,weightedEval (mirror A) b P i)=(formalPrimitive P).eval 1 := by
  have h:OrdinaryTrace A 0 (1:Vec K s) (1:K[X]):=by
    have h1:evalNodes A (1:K[X])=(1:Vec K s):=by ext i;simp
    rw [←h1]
    exact OrdinaryTrace.scalar A (by simp)
  have e:=h.pair_polynomial ho (reflectPolynomial P) (by have:=reflectPolynomial_degree P;omega)
  rw [one_mul,reflectPolynomial_integral,←weightedEval_reflect] at e
  simpa [row_apply] using e

/-- Incoming rank with primitive membership stated directly, allowing
either full or terminal-zero complementary columns. -/
theorem incoming_paid_polynomial (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {r:ℕ} (pay:2*r≤p) (V W:Submodule K (Vec K s))
    (inc:V≤W) (hm:MaskInvariant (mirror A) W)
    (mass:∀w∈W,∑ i,w i=0) (hNV:V.map (transMat A)≤W)
    (paid:∀P:K[X],P.natDegree+1≤2*r →
      transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)∈W) :
    finrank K V+r≤finrank K W := by
  let T:=revVec (K:=K) (s:=s)
  let Vr:=V.map T.toLinearMap
  let Wr:=W.map T.toLinearMap
  let y:=mirror A
  have hmr:MaskInvariant (T y) Wr:=by
    rintro a _ ⟨w,hw,rfl⟩
    exact ⟨_,hm a w hw,rfl⟩
  have zeror (w:Vec K s)(hw:w∈Wr):∑i,w i=0:=by
    obtain ⟨x,hx,rfl⟩:=hw
    change (∑i:Fin s,x i.rev)=0
    rw [show (∑i:Fin s,x i.rev)=∑i,x i from Equiv.sum_comp Fin.revPerm x]
    exact mass x hx
  have wc (P:K[X]):weightedEval (T y) (T b) P=T (weightedEval y b P):=by
    ext i;simp only [T,revVec_apply,weightedEval_apply]
  have fail:r≤(failedNodes (T y) (T b) Wr s).card:=by
    apply failed_at_least_of_scalar_budget _ _ _ hmr zeror
    intro P hP
    rw [wc]
    change (∑i:Fin s,weightedEval y b P i.rev)=_
    rw [show (∑i:Fin s,weightedEval y b P i.rev)=∑i,weightedEval y b P i from
      Equiv.sum_comp Fin.revPerm _]
    exact reflected_scalar_budget ho P (by omega)
  have rank:=incoming_nodal_gain (T y) (T b) Vr Wr (reverseOp A)
    (reverseOp_strict ha) hmr (Submodule.map_mono inc) (by
      rintro _ ⟨v,hv,rfl⟩
      rw [show T.toLinearMap v=revVec v from rfl,reverseOp_rev]
      exact Submodule.mem_map_of_mem (hNV (Submodule.mem_map_of_mem hv))) r fail (by
      intro P hP
      rw [wc,wc,show T=revVec from rfl,reverseOp_rev,←map_sub]
      exact Submodule.mem_map_of_mem (paid P hP))
  simpa only [Vr,Wr,LinearEquiv.finrank_map_eq] using rank

theorem primitive_annihilator_paid (ho:HasTreeOrderAtLeast A b p)
    (P:K[X]) {j:ℕ} (pay:j+P.natDegree+2≤p) :
    transMat A (weightedEval (mirror A) b P)-weightedEval (mirror A) b (formalPrimitive P)
      ∈annih (treeSpace A j) := by
  have h:=weighted_reverse_primitive (P:=P) ho (n:=P.natDegree) le_rfl (by omega)
  change _∈annih (treeSpace A (p-1-(P.natDegree+1))) at h
  exact mem_annih.mpr (fun v hv=>mem_annih.mp h v (treeSpace_mono A (by omega) hv))

/-- Any nodally stable hull containing the genuine complementary
annihilator pays this many incoming dimensions. Neither the hull nor the
lower input space is assumed to be a complete grade of a backward flag. -/
theorem incoming_actual_budget (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {j r:ℕ} (pay:j+2*r+1≤p) (V W:Submodule K (Vec K s))
    (inc:V≤W) (hm:MaskInvariant (mirror A) W)
    (mass:∀w∈W,∑ i,w i=0) (hNV:V.map (transMat A)≤W)
    (cover:annih (treeSpace A j)≤W) :
    finrank K V+r≤finrank K W := by
  apply incoming_paid_polynomial ha ho (by omega) V W inc hm mass hNV
  intro P hP
  exact cover (primitive_annihilator_paid ho P (by omega))

omit [CharZero K] in
theorem transMat_zero_column (t:Fin s) (col:∀i,A i t=0) (v:Vec K s) :
    transMat A v t=0 := by
  change (∑ i:Fin s,A i t*v i)=0
  simp [col]

/-- The only primitive rows needed at an original terminal coordinate are
already zero there when its reflected clock is zero and its column is
zero. This is an actual coordinate restriction, not stage deletion. -/
theorem incoming_actual_budget_terminal (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    {j r:ℕ} (pay:j+2*r+1≤p) (t:Fin s) (y0:mirror A t=0) (col:∀i,A i t=0)
    (V W:Submodule K (Vec K s)) (inc:V≤W) (hm:MaskInvariant (mirror A) W)
    (mass:∀w∈W,∑ i,w i=0) (hNV:V.map (transMat A)≤W)
    (cover:(annih (treeSpace A j)⊓LinearMap.ker (LinearMap.proj t))≤W) :
    finrank K V+r≤finrank K W := by
  apply incoming_paid_polynomial ha ho (by omega) V W inc hm mass hNV
  intro P hP
  apply cover
  refine ⟨primitive_annihilator_paid ho P (by omega),?_⟩
  change transMat A (weightedEval (mirror A) b P) t - weightedEval (mirror A) b (formalPrimitive P) t=0
  rw [transMat_zero_column t col,weightedEval_apply,y0,formalPrimitive_eval_zero,zero_mul,sub_self]

end
end RKCert.Paired.ReverseHull
