module

public import RKCert.ReviewedNative.ERK19ZeroReversePorts

public section

/-! # Forward primitive ports of the actual width-29 zero-seed head

The reverse quadratic support, compensated hidden rows, contrast rows,
and live terminal account for at least 28 original coordinates. The
physical forward correction is exact up to one named spare row, not
an assumed four- or five-point quadrature chart.
-/
namespace RKResearch.Certified.ERK19

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKResearch.Certified.Graded.Reverse.Hidden
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

private def flip (P : K[X]) : K[X] := P.comp (1-X)

private theorem flip_involution (P : K[X]) : flip (flip P)=P := by
  unfold flip
  rw [comp_assoc,show ((1-X:K[X]).comp (1-X))=X by simp,comp_X]

private theorem flip_degree (P : K[X]) : (flip P).natDegree≤P.natDegree := by
  unfold flip
  apply natDegree_comp_le.trans
  rw [one_sub_X_natDegree,mul_one]

private theorem flip_eval (P : K[X]) (i : Fin s) :
    (flip P).eval (nodes A i)=P.eval (reflectedClock A i) := by
  simp [flip,eval_comp,reflectedClock]

/-- Reflection of the exact physical contrast law. Both sides use the
same original tableau and its paid clock moments. -/
theorem forward_contrast_moment (ho : HasOrder p A b) (Q E H : K[X])
    (qpay : H.natDegree+Q.natDegree+2≤p) (epay : H.natDegree+E.natDegree+3≤p) :
    (primitive (H*((1-X)*Q.comp (1-X)))).eval 1=
      ∑ i,H.eval (nodes A i)*reverseContrast A b Q E i := by
  let J := flip H
  let B := J*(X*Q)
  let D := H*((1-X)*flip Q)
  have dj : J.natDegree≤H.natDegree := flip_degree H
  have bd : B.natDegree+1≤p := by
    have m := natDegree_mul_le (p:=J) (q:=X*Q)
    have n := natDegree_mul_le (p:=X) (q:=Q)
    rw [natDegree_X] at n
    change B.natDegree≤J.natDegree+(X*Q).natDegree at m
    omega
  have dd : D.natDegree+1≤p := by
    have m := natDegree_mul_le (p:=H) (q:=(1-X)*flip Q)
    have n := natDegree_mul_le (p:=(1-X : K[X])) (q:=flip Q)
    have r := flip_degree Q
    rw [one_sub_X_natDegree] at n
    change D.natDegree≤H.natDegree+((1-X)*flip Q).natDegree at m
    omega
  have eq : flip B=D := by
    unfold flip
    change (J*(X*Q)).comp (1-X)=D
    rw [mul_comp,mul_comp,X_comp]
    change flip J*((1-X)*flip Q)=D
    rw [show flip J=H from flip_involution H]
  have pr := probe_evalNodes ho D 0 (by omega)
  rw [pow_zero,one_mul] at pr
  have m1 : (∑i,D.eval (nodes A i)*b i)=(primitive D).eval 1 := by
    simpa only [probe,pow_zero,mul_one,row_apply,dotProduct,evalNodes_apply,mul_comm] using pr
  have m2 : (∑i,weightedEval (reflectedClock A) b B i)=∑i,D.eval (nodes A i)*b i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [weightedEval_apply,←eq,flip_eval]
  have prim : (primitive D).eval 1=(primitive B).eval 1 :=
    m1.symm.trans (m2.symm.trans (reflected_polynomial_mass ho B bd))
  have w := reverse_contrast_moment ho Q E J (by omega) (by omega)
  have m3 : (∑i,weightedEval (reflectedClock A) (reverseContrast A b Q E) J i)=
      ∑i,H.eval (nodes A i)*reverseContrast A b Q E i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [weightedEval_apply]
    have e := flip_eval (A:=A) (flip H) i
    rw [flip_involution] at e
    rw [show J.eval (reflectedClock A i)=H.eval (nodes A i) from e.symm]
  exact prim.trans (w.symm.trans m3)

end

noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

/-- Exact physical forward port data with a named optional spare coordinate.
No arbitrary nonzero weight or distinctness beyond the contrast is assumed. -/
structure Width29ForwardPorts (A : Matrix (Fin 29) (Fin 29) K) (b θ : Fin 29 → K)
    (Q E P : K[X]) (spare : Finset (Fin 29)) : Prop where
  quintic : P.natDegree=5
  reflected : P=Q.comp (1-X)
  spareCap : spare.card≤1
  footprint : spare.card+(activeRows (quadraticSeed A b)).card+
    (activeRows (reverseContrast A b Q E)).card=23
  supported : ∀ i,reverseContrast A b Q E i=0 → i≠Fin.last 28 → i∉spare → θ i=0
  supportAway : ∀ i,reverseContrast A b Q E i=0 → i≠Fin.last 28 → i≠0 → θ i=0
  atOrigin : θ 0=P.eval 0
  exceptionalOrigin : reverseContrast A b Q E 0=0 → P.eval 0≠0 →
    (0:Fin 29)∈spare ∧ quadraticSeed A b 0=0 ∧ b 0=0
  on : ∀ i,reverseContrast A b Q E i≠0 → θ i=P.eval (nodes A i) ∧ θ i≠0
  origin : reverseContrast A b Q E 0=0 → (0:Fin 29)∉spare → P.eval 0=0
  moments : ∀ H : K[X], H.natDegree≤12 →
    (primitive (H*((1-X)*P))).eval 1=∑ i,H.eval (nodes A i)*reverseContrast A b Q E i
  port : ∀ i,reverseContrast A b Q E i≠0 → ∀ H : K[X],H.natDegree≤3 →
    mat A (weightedEval (nodes A) θ H) i=(primitive (H*P)).eval (nodes A i)

variable [CharZero K]

set_option maxHeartbeats 950000 in
/-- Produce the genuine forward residual, moments through degree twelve, and all
paid degree-three physical primitive ports. -/
theorem Width29ZeroHead.forward_ports (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    {h : Fin 29→K} {Q E : K[X]} (H : Width29ZeroHead A b h Q E)
    (Z : Width29ZeroCover A b) (F : Width29HiddenFrame A b)
    (dim : finrank K (hiddenCarrier A b)=5) :
    ∃ θ P spare, Width29ForwardPorts A b θ Q E P spare := by
  let t := Fin.last 28
  let c := nodes A
  let d := quadraticSeed A b
  let U := hiddenCarrier A b
  let Y := reflectedClock A
  let G := blindRows c b d 0 t
  let W := reverseContrast A b Q E
  let P := flip Q
  have pd : P.natDegree=5 := by
    have a := flip_degree Q
    have b := flip_degree (flip Q)
    rw [flip_involution] at b
    change P.natDegree≤Q.natDegree at a
    change Q.natDegree≤P.natDegree at b
    have q := H.quintic
    omega
  have gd : G.card=5 := by
    have e := Hidden.carrier_rank (c:=c) (d:=d) (o:=0) (t:=t) Z.lastLive
    change finrank K U=G.card at e
    change finrank K U=5 at dim
    rw [dim] at e
    exact e.symm
  have wG (i : Fin 29) (ig : i∈G) : W i=0 := by
    by_contra nz
    have e := ((mem_blindRows i).mp ig).2.2.2
    change (Y i)*b i=0 at e
    exact mul_ne_zero (H.active nz).2.1 (H.active nz).2.2.1 e
  have wD (i : Fin 29) (di : d i≠0) : W i=0 := by
    by_contra nz
    exact di (H.active nz).1
  have wT : W t=0 := by
    by_contra n
    apply (H.active n).2.1
    change 1-nodes A t=0
    rw [Z.lastClock,sub_self]
  have disGD : Disjoint G (activeRows d) := Finset.disjoint_left.mpr fun i hi hd =>
    (mem_activeRows i).mp hd ((mem_blindRows i).mp hi).2.2.1
  have disGW : Disjoint G (activeRows W) := Finset.disjoint_left.mpr fun i hi hw =>
    (mem_activeRows i).mp hw (wG i hi)
  have disDW : Disjoint (activeRows d) (activeRows W) := Finset.disjoint_left.mpr fun i hd hw =>
    (mem_activeRows i).mp hw (wD i ((mem_activeRows i).mp hd))
  have tail : t∉(G∪activeRows d)∪activeRows W := by
    have gt : t∉G := fun h => ((mem_blindRows t).mp h).2.1 rfl
    simp only [Finset.mem_union,mem_activeRows,gt,show d t=0 from Z.lastSeed,wT,ne_self_iff_false,
      or_self,not_false_eq_true]
  let used := insert t ((G∪activeRows d)∪activeRows W)
  let spare := Finset.univ \ used
  have four : 4≤(weightedSites Y W).card := H.fourSites
  have cnt : (weightedSites Y W).card≤(activeRows W).card := Finset.card_image_le
  have price : used.card=(activeRows d).card+(activeRows W).card+6 := by
    dsimp only [used]
    rw [Finset.card_insert_of_notMem tail,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disGW,disDW⟩),
      Finset.card_union_of_disjoint disGD,gd]
    omega
  have foot : spare.card+(activeRows d).card+(activeRows W).card=23 := by
    have e := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ used)
    change spare.card+used.card=(Finset.univ : Finset (Fin 29)).card at e
    rw [price,Finset.card_univ,Fintype.card_fin] at e
    omega
  have spareCap : spare.card≤1 := by
    have q : 18≤(activeRows d).card := H.quadraticRows
    omega
  have covered (i : Fin 29) (ti : i≠t) (wi : W i=0) (si : i∉spare) :
      i∈G ∨ d i≠0 := by
    have loc : i∈used := by
      by_contra n
      exact si (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,n⟩)
    simpa only [used,Finset.mem_insert,Finset.mem_union,mem_activeRows,ti,wi,ne_self_iff_false,
      false_or,or_false] using loc
  obtain ⟨k,hk,fit⟩ := carrier_filler (c:=c) (d:=d) (o:=0) (t:=t)
    (f:=evalNodes A P-h) Z.lastLive
  let θ := evalNodes A P-h-k
  have read (i : Fin 29) (di : d i≠0) : h i=P.eval (c i) := by
    rw [show P.eval (c i)=Q.eval (Y i) from flip_eval (A:=A) Q i]
    have e := H.traceQ i
    rw [mul_comm (Q.eval _)] at e
    exact mul_left_cancel₀ di e
  have atCovered (i : Fin 29) (covered : i∈G∨d i≠0) : θ i=0 := by
    rcases covered with ig|di
    · change (evalNodes A P-h) i-k i=0
      rw [fit i ig,sub_self]
    · simp only [θ,Pi.sub_apply,evalNodes_apply,read i di,carrier_zero_on_active Z.lastSeed hk di,
        sub_self,c]
  have off (i : Fin 29) (wi : W i=0) (ti : i≠t) (si : i∉spare) : θ i=0 :=
    atCovered i (covered i ti wi si)
  have away (i : Fin 29) (wi : W i=0) (ti : i≠t) (oi : i≠0) : θ i=0 := by
    by_cases loc : i∈G∨d i≠0
    · exact atCovered i loc
    have ig : i∉G := fun e => loc (Or.inl e)
    have dz : d i=0 := by by_contra e; exact loc (Or.inr e)
    have live : Y i*b i≠0 := by
      intro e
      exact ig ((mem_blindRows i).mpr ⟨oi,ti,dz,e⟩)
    have hi : h i=0 := by
      have e := H.traceE i
      change (Y i*b i)*h i=E.eval (Y i)*d i at e
      rw [dz,mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_left live
    have qi : Q.eval (Y i)=0 := by
      have e : (Y i*b i)*Q.eval (Y i)=0 := by
        simp only [W,reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,
          show quadraticSeed A b i=0 from dz,mul_zero,sub_zero] at wi
        change (Y i*Q.eval (Y i))*b i=0 at wi
        linear_combination wi
      exact (mul_eq_zero.mp e).resolve_left live
    have ki : k i=0 := (mem_ambientHidden.mp hk).1 i ig ti
    simp only [θ,Pi.sub_apply,evalNodes_apply,hi,ki,sub_zero,show
      P.eval (nodes A i)=Q.eval (Y i) from flip_eval (A:=A) Q i,qi]
  have on (i : Fin 29) (wi : W i≠0) : θ i=P.eval (c i) ∧ θ i≠0 := by
    have e : θ i=P.eval (c i) := by
      simp only [θ,Pi.sub_apply,evalNodes_apply,(H.active wi).2.2.2.2,
        H.clean i wi _ (F.toNine hk),sub_zero,c]
    exact ⟨e,e.symm ▸ ((flip_eval (A:=A) Q i).symm ▸ (H.active wi).2.2.2.1)⟩
  have h0 : h 0=0 := origin_zeroSpace ha 5 H.staircase.headGrade
  have k0 : k 0=0 := origin_zeroSpace ha 9 (F.toNine hk)
  have c0 : nodes A 0=0 := by
    change (∑ j,A 0 j * (1:K))=0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j),zero_mul]
  have at0 : θ 0=P.eval 0 := by
    simp only [θ,Pi.sub_apply,evalNodes_apply,c0,h0,k0,sub_zero]
  have origin (w0 : W 0=0) (n0 : (0:Fin 29)∉spare) : P.eval 0=0 :=
    at0.symm.trans (off 0 w0 (by decide) n0)
  have exceptional (w0 : W 0=0) (p0 : P.eval 0≠0) :
      (0:Fin 29)∈spare ∧ d 0=0 ∧ b 0=0 := by
    have sp : (0:Fin 29)∈spare := by by_contra no; exact p0 (origin w0 no)
    have dz : d 0=0 := by
      by_contra live
      exact p0 (at0.symm.trans (atCovered 0 (Or.inr live)))
    have y1 : Y 0=1 := by change 1-nodes A 0=1; rw [c0,sub_zero]
    refine ⟨sp,dz,?_⟩
    by_contra live
    have w : Q.eval 1*b 0=0 := by
      change (weightedEval Y b (X*Q)-weightedEval Y d E) 0=0 at w0
      simpa only [Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,y1,one_mul,dz,mul_zero,sub_zero]
        using w0
    have q0 := (mul_eq_zero.mp w).resolve_right live
    apply p0
    have e := flip_eval (A:=A) Q 0
    change P.eval (nodes A 0)=Q.eval (Y 0) at e
    rwa [c0,y1,q0] at e
  refine ⟨θ,P,spare,⟨pd,rfl,spareCap,foot,off,away,at0,exceptional,on,origin,?_,?_⟩⟩
  · intro R dr
    exact forward_contrast_moment ho Q E R (by have := H.quintic; omega) (by have := H.auxDegree; omega)
  · intro i wi R dr
    have dp : (R*P).natDegree≤8 := natDegree_mul_le.trans (by omega)
    have z := H.clean i wi _ (primitive_defect A (R*P) dp)
    have small : weightedEval c h R∈zeroSpace A 8 := by
      have e : weightedEval c h R=h*evalNodes A R := by ext i; simp [c,mul_comm]
      rw [e]
      exact zeroSpace_mul_treeSpace ho (m:=5) (n:=3) (by decide) H.staircase.headGrade
        (evalNodes_mem_treeSpace _ _ dr)
    have kc : weightedEval c k R∈U := by
      have e : weightedEval c k R=fun j => R.eval (c j)*k j := by ext j; simp
      rw [e]
      exact clock_function_mem (fun _ h => F.stable (Submodule.mem_map_of_mem h)) R.eval hk
    have f1 := H.clean i wi _ (mat_zeroSpace_charZero A 8 small)
    have f2 := H.clean i wi _ (zeroSpace_mono A (by decide : 7≤9)
      (mat_zeroSpace_charZero A 6 (H.staircase.inside kc)))
    have e : weightedEval c θ R=
        evalNodes A (R*P)-weightedEval c h R-weightedEval c k R := by
      ext j
      simp only [weightedEval_apply,Pi.sub_apply,evalNodes_apply,eval_mul,θ,c]
      ring
    rw [e,map_sub,map_sub,Pi.sub_apply,Pi.sub_apply,f1,f2,sub_zero,sub_zero]
    exact sub_eq_zero.mp z

end
end RKResearch.Certified.ERK19

namespace RKResearch.Certified.ERK19
open RKResearch Polynomial RKResearch.Certified.Graded.Reverse
open scoped Classical
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

/-- Combine the original signed reverse and forward physical ports, with
only the exact native order and zero first seed as hypotheses. -/
theorem width29_zero_physical_ports (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ h Q E i j k θ P spare, Width29ZeroHead A b h Q E ∧
      Width29ReversePortSequence A b Q E i j k ∧ Width29ForwardPorts A b θ Q E P spare := by
  obtain ⟨h,Q,E,i,j,k,H,R⟩ := width29_zero_reverse_ports ha ho zero
  obtain ⟨θ,P,spare,F⟩ := H.forward_ports ha ho (width29_zero_cover_data ha ho zero)
    (width29_hidden_frame ha ho zero) (ordered_width29_hidden_rank_five ha ho zero)
  exact ⟨h,Q,E,i,j,k,θ,P,spare,H,R,F⟩

end RKResearch.Certified.ERK19

