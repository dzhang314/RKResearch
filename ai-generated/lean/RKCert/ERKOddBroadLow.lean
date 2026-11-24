module
public import RKCert.ERKOddBroadTrace

@[expose] public section
/-! # Small ordered ordinary defects are invisible to a full linear wide band -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p m h:ℕ} {A:Fin s→Fin s→K} {b f:Vec K s}
noncomputable section

theorem linear_contrast_moment (ho:HasTreeOrderAtLeast A b p) (Q P R:K[X])
    (payQ:R.natDegree+Q.natDegree+1≤p)(payP:R.natDegree+P.natDegree+2≤p):
    (∑i,weightedEval (mirror A) (linearContrast A b Q P) R i)=
      (Paired.primitive (R*Q)).eval 1:=by
  have q:(R*Q).natDegree≤R.natDegree+Q.natDegree:=natDegree_mul_le
  have r:(R*P).natDegree≤R.natDegree+P.natDegree:=natDegree_mul_le
  rw [linear_contrast_filter]
  simp only [Pi.sub_apply,Finset.sum_sub_distrib]
  rw [linear_seed_mass ho (R*P) (by omega),sub_zero,reflected_scalar_budget ho (R*Q) (by omega),
    formalPrimitive_eq_treePrimitive]

theorem linear_contrast_two_nonzero (ho:HasTreeOrderAtLeast A b p) (Q P:K[X])
    (qn:Q≠0)(payQ:2*Q.natDegree+5≤p)(payP:Q.natDegree+P.natDegree+6≤p):
    ∀u:K,∃i,linearContrast A b Q P i≠0 ∧ mirror A i≠0 ∧ mirror A i≠u:=by
  intro u
  let y:=mirror A
  let W:=linearContrast A b Q P
  let H:K[X]:=X*(X-C u)
  have dH:H.natDegree≤2:=natDegree_mul_le.trans (by simp)
  let R:=H^2*Q
  have dR:R.natDegree≤4+Q.natDegree:=by
    have z:=natDegree_mul_le (p:=H^2) (q:=Q)
    rw [natDegree_pow] at z
    dsimp only [R];omega
  by_contra! no
  have z:(∑i,weightedEval y W R i)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    by_cases wi:W i=0
    · rw [weightedEval_apply,wi,mul_zero]
    change ∀ i, W i≠0→y i≠0→y i=u at no
    by_cases xi:y i=0
    · simp [R,H,xi]
    · have e:y i=u:=no i wi xi
      simp [R,H,e]
  have t:=linear_contrast_moment ho Q P R (by omega) (by omega)
  change (∑i,weightedEval y W R i)=_ at t
  rw [z,show R*Q=(H*Q)^2 by dsimp [R];ring] at t
  have pos:=RKCert.OrderedGram.pow_square_pos 0 (H*Q)
    (mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)) qn)
  rw [pow_zero,one_mul] at pos
  exact pos.ne' t.symm

theorem ordered_broad_invisible_given_reps (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b p)
    (B:BroadLinearCover A b m h) (Q P:K[X]) (dQ:Q.natDegree≤4)
    (qm:2*Q.natDegree+5≤p)(pm:Q.natDegree+P.natDegree+6≤p)
    (qb:m+Q.natDegree+5≤p)(pb:m+P.natDegree+6≤p)(fit:LinearFits A b f Q P):
    ∀i,backSeed1 A b i*f i=0 ∧ b i*f i=0:=by
  have vanish:Q=0:=by
    by_contra nz
    classical
    let y:=mirror A
    let W:=linearContrast A b Q P
    have two:=linear_contrast_two_nonzero ho Q P nz qm pm
    let D:Finset (Fin s):=Finset.univ.filter (fun i=>W i≠0 ∧ y i≠0)
    have ne:D.Nonempty:=by
      obtain ⟨i,wi,yi,_⟩:=two 0
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,wi,yi⟩⟩
    let i:=D.max' ne
    let u:=y i
    have iD:W i≠0 ∧ u≠0:=(Finset.mem_filter.mp (D.max'_mem ne)).2
    let E:=D.filter (fun i=>y i≠u)
    have En:E.Nonempty:=by
      obtain ⟨j,wj,yj,uj⟩:=two u
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,wj,yj⟩,uj⟩⟩
    let j:=E.max' En
    have jE:=Finset.mem_filter.mp (E.max'_mem En)
    have jD:W j≠0 ∧ y j≠0:=(Finset.mem_filter.mp jE.1).2
    have zero (k:Fin s)(wk:W k≠0)(R:K[X])(dr:R.natDegree≤3)
        (off:∀l:Fin s,k<l→W l≠0→R.eval (y l)=0):
        (Paired.primitive (R*Q)).eval (y k)=0:=by
      have e:transMat A (weightedEval y W R) k=0:=by
        apply causal_transpose ha
        intro l kl
        rw [weightedEval_apply]
        by_cases wl:W l=0
        · rw [wl,mul_zero]
        · rw [off l (Fin.rev_lt_rev.mp kl) wl,zero_mul]
      have sp:=fit.contrast_support wk
      have zz:=broad_linear_port ho B Q P R (by omega) (by omega) sp.1
      change transMat A (weightedEval y W R) k=_ at zz
      rw [e] at zz
      exact (mul_eq_zero.mp zz.symm).resolve_right sp.2.1
    apply nz (ordered_quartic_physical Q dQ iD.2 jD.2 jE.2 ?_ ?_)
    · intro R dr
      rw [show R*(X*Q)=(R*X)*Q by ring]
      apply zero i iD.1 (R*X) (natDegree_mul_le.trans (by rw [natDegree_X];omega))
      intro l lt wl
      have z:y l=0:=by
        by_contra h
        exact (not_le_of_gt lt) (D.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wl,h⟩))
      simp [z]
    · intro R dr
      let S:K[X]:=R*(X*(X-C u))
      rw [show R*(X*(X-C u)*Q)=S*Q by dsimp [S];ring]
      apply zero j jD.1 S
      · have a:=natDegree_mul_le (p:=R) (q:=X*(X-C u))
        have e:=natDegree_mul_le (p:=X) (q:=X-C u)
        rw [natDegree_X,natDegree_X_sub_C] at e
        dsimp only [S];omega
      · intro l lt wl
        by_cases z:y l=0
        · simp [S,z]
        have n:y l=u:=by
          by_contra neq
          exact (not_le_of_gt lt) (E.le_max' _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,wl,z⟩,neq⟩))
        simp [S,n]
  intro i
  have q:=fit.1 i
  rw [vanish,eval_zero,zero_mul] at q
  refine ⟨q,?_⟩
  by_cases h:backSeed1 A b i=0
  · simpa only [h,mul_zero] using fit.2 i
  · rw [(mul_eq_zero.mp q).resolve_left h,mul_zero]
end
end RKCert.Paired.ReverseHull

