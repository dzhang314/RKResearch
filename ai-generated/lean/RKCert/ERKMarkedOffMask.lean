module
public import RKCert.OrderTwelveOffMask

@[expose] public section
/-! # Codimension-one causal off-mask bootstrap without a graded equality
The proof uses only a single line of incoming primitive observations.
This slightly more general form allows a terminal coordinate line known
to be an actual core mask. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {U W:Submodule K (Vec K (s+1))}

theorem off_mask_bootstrap_codim_one (ha:StrictLower A) (hU:MulClosed U)
    (hinv:U.map (diag (nodes A))≤U) (subset:W≤U)
    (dim:finrank K W+1=finrank K U)
    (advance:∀v∈W,mat A v∈U)
    (primitives:∀k≤3,mat A (evalNodes A (X^k))-evalNodes A (Paired.primitive (X^k))∈U) :
    ∃h:K,∀j,¬Live U j→nodes A j=0∨nodes A j=h := by
  classical
  let c:=nodes A
  have u3 : W≤U := subset
  let V := W.comap U.subtype
  let L := V.dualAnnihilator
  have vdim : finrank K V=finrank K W := (Submodule.comapSubtypeEquivOfLe u3).finrank_eq
  have ldim : finrank K L=1 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq V
    change finrank K V + finrank K L = finrank K U at h
    omega
  let f (j:Fin (s+1)) : U→ₗ[K] K := (LinearMap.proj j).comp ((mat A).comp U.subtype)
  have fl (j:Fin (s+1)) (hj:¬Live U j) : f j∈L := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro q hq
    change mat A q.val j=0
    let x : Vec K (s+1) := q.val
    have hx : x∈W := hq
    have hw : mat A x∈U := advance x hx
    by_contra hn;exact hj ⟨_,hw,hn⟩
  obtain ⟨e,he,ei⟩:=core_indicator hU
  let M (k:ℕ) : Vec K (s+1) := fun j=> e j*c j^k
  let N (k:ℕ) : Vec K (s+1) := fun j=> (1-e j)*c j^k
  have hm (k:ℕ) : M k∈U := by
    have H := poly_preserves hinv (X^k) e he
    have E : (fun j => (X^k:K[X]).eval (nodes A j)*e j)=M k := by
      ext j;simp [M,c,mul_comm]
    rwa [E] at H
  have exacts (j:Fin (s+1)) (hj:¬Live U j) (k:ℕ) (hk:k≤3) :
      mat A (M k) j+mat A (N k) j=c j^(k+1)/(k+1:ℕ) := by
    have H := primitives k hk
    have hz : (mat A (evalNodes A (X^k)) - evalNodes A (Paired.primitive (X^k))) j=0 := by
      by_contra hh;exact hj ⟨_,H,hh⟩
    have E : evalNodes A (X^k)=M k+N k := by ext l;simp [evalNodes,M,N,c];ring
    have ep : X^k = monomial k (1:K) := by simp [← C_mul_X_pow_eq_monomial]
    have he : (Paired.primitive (X^k:K[X])).eval (c j)=c j^(k+1)/(k+1:ℕ) := by
      rw [ep,primitive_monomial,eval_monomial];ring
    change mat A (evalNodes A (X^k)) j-(Paired.primitive (X^k:K[X])).eval (c j)=0 at hz
    rw [E,map_add,Pi.add_apply,he] at hz
    exact sub_eq_zero.mp hz
  let Z := Finset.univ.filter (fun j => ¬Live U j ∧ c j≠0)
  by_cases hZ:Z.Nonempty
  · let q := Z.min' hZ
    have hq := (Finset.mem_filter.mp (Z.min'_mem hZ)).2
    let h := c q
    refine ⟨h,fun j hj=>?_⟩
    by_contra! none
    let T := Finset.univ.filter (fun j => ¬Live U j ∧ c j≠0 ∧ c j≠h)
    have hT:T.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,none.1,none.2⟩⟩
    let j' := T.min' hT
    have hhj := (Finset.mem_filter.mp (T.min'_mem hT)).2
    let y := c j'
    have preQ (l:Fin (s+1)) (hl:l<q) (hu:¬Live U l) : c l=0 := by
      by_contra hn
      exact (not_le_of_gt hl) (Z.min'_le l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,hn⟩))
    have preJ (l:Fin (s+1)) (hl:l<j') (hu:¬Live U l) : c l=0 ∨ c l=h := by
      by_contra! hn
      exact (not_le_of_gt hl) (T.min'_le l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,hn.1,hn.2⟩))
    have zero (k:ℕ) (hk:0<k) : mat A (N k) q=0 := by
      have e := strictlyCausal_mat ha q (N k) 0 (fun l hl => by
        by_cases hh:Live U l
        · simp [N,ei,hh]
        · simp [N,preQ l hl hh,zero_pow hk.ne'])
      simpa only [map_zero,Pi.zero_apply] using e
    have fQ (k:ℕ) (hk:0<k) (hk3:k≤3) : f q ⟨M k,hm k⟩=h^(k+1)/(k+1:ℕ) := by
      have hM := exacts q hq.1 k hk3
      rw [zero k hk,add_zero] at hM
      exact hM
    have fqn : (⟨f q,fl q hq.1⟩:L)≠0 := by
      intro hn
      have hF:=congrArg (fun x:L=>x.val ⟨M 1,hm 1⟩) hn
      change f q ⟨M 1,hm 1⟩=0 at hF
      rw [fQ 1 (by decide) (by decide)] at hF
      exact (div_ne_zero (pow_ne_zero _ hq.2) (by norm_num)) hF
    let fq : L := ⟨f q,fl q hq.1⟩
    let fj : L := ⟨f j',fl j' hhj.1⟩
    obtain ⟨a,ea⟩ := (finrank_eq_one_iff_of_ne_zero' (K:=K) fq fqn).mp ldim fj
    have jf (k:ℕ) (hk:0<k) (hk3:k≤3) : mat A (M k) j'=a*(h^(k+1)/(k+1:ℕ)) := by
      have H := congrArg (fun x:L=>x.val ⟨M k,hm k⟩) ea
      change a * f q ⟨M k,hm k⟩=mat A (M k) j' at H
      rwa [fQ k hk hk3,eq_comm] at H
    have scales (k:ℕ) (hk:0<k) : mat A (N k) j'=h^(k-1)*mat A (N 1) j' := by
      rw [← smul_eq_mul,← Pi.smul_apply,←map_smul]
      apply strictlyCausal_mat ha
      intro l hl
      by_cases hL : Live U l
      · simp [N,ei,hL]
      · rcases preJ l hl hL with z|p
        · simp [N,ei,hL,z,zero_pow hk.ne']
        · simp only [N,ei,hL,ite_false,sub_zero,one_mul,Pi.smul_apply,smul_eq_mul,p,pow_one]
          rw [←pow_succ,show k-1+1=k by omega]
    have e1:=exacts j' hhj.1 1 (by decide)
    have e2:=exacts j' hhj.1 2 (by decide)
    have e3:=exacts j' hhj.1 3 (by decide)
    rw [jf 1 (by decide) (by decide)] at e1
    rw [jf 2 (by decide) (by decide),scales 2 (by decide)] at e2
    rw [jf 3 (by decide) (by decide),scales 3 (by decide)] at e3
    norm_num at e1 e2 e3
    have ee : y^2*(y-h)^2=0 := by
      dsimp only [y];linear_combination -4*e3+6*h*e2-2*h^2*e1
    exact (mul_ne_zero (pow_ne_zero 2 hhj.2.1) (pow_ne_zero 2 (sub_ne_zero.mpr hhj.2.2))) ee
  · refine ⟨0,fun j hj=>Or.inl ?_⟩
    by_contra h
    exact hZ ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,h⟩⟩

end RKCert.Paired.FiniteMidpoint
