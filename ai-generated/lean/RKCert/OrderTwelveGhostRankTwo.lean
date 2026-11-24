module
public import RKCert.OrderTwelveLeakage
public import RKCert.OrderTwelveCoreRows
@[expose] public section

/-! # The nonzero-ghost rank-two chart cannot separate seventeen stages

This is an actual tableau theorem with the chart hypotheses explicitly
listed. It does not assert that the rank-two chart has already been derived
in every tableau, or that the ghost coefficient must be nonzero. -/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {i:Fin (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

theorem exclude_nonzero_ghost_two (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀j,i<j→b j=0)
    (hh:HeadData A 2 U w) (hU:MulClosed U) (hdis:∀ j,Live U j→w j=0)
    (htop:pBand A ⊔ chain (diag (nodes A)) U w 7=⊤)
    (α:K) (hα:α≠0)
    (hghost:w*w-α • evalNodes A ghost8∈chain (diag (nodes A)) U w 5) : False := by
  classical
  let c:=nodes A
  have hUrank:finrank K U=3 := by have h := hh.rank;omega
  have hw5 : w∈zeroSpace A 5 := by
    rw [hh.f5]
    have hx := (chain_le_iff (T:=diag c) (U:=U) (w:=w) 2).mp le_rfl
    simpa only [pow_zero,one_apply_eq_self] using hx.2 0 (by decide)
  have hwi:=f5_vanish_at_last_active ha ho hs hi hl hw5
  have hc:=active_last_normal ha hs hi hl
  have hdelta:(Pi.single i (1:K):Vec K (s+1))-evalNodes A mesh6∈chain (diag c) U w 3 := by
    rw [←hh.f6]
    exact mesh_at_end ha ho hs hi hl
  obtain ⟨u,hu,Q,hQ,hx⟩:=exists_head_poly hdelta
  obtain ⟨v,hv,R,hR,hy⟩:=exists_head_poly hghost
  have hQ' : (-Q).natDegree≤2 := by
    rw [natDegree_neg]
    by_cases hq:Q=0
    · simp [hq]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hq).mpr hQ)
  have hR' : R.natDegree≤4 := by
    by_cases hr:R=0
    · simp [hr]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hr).mpr hR)
  let S := headFeatures c w
  have hm : S.card≤11 := by
    apply head_feature_bound S RKCert.OrderTwelve.dFivePoly (α • ghost8) (-Q) R
      RKCert.OrderTwelve.natDegree_dFivePoly
      ((natDegree_smul_le ..).trans ghost8_natDegree) hQ' hR' (ghost8_coprime_smul hα)
      (by simp [eval_smul,ghost8_zero])
    intro f hf
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    have hwj : w j≠0 := (Finset.mem_filter.mp hj).2
    have hUj : ¬Live U j := fun l=>hwj (hdis j l)
    have uj : u j=0 := by by_contra h;exact hUj ⟨u,hu,h⟩
    have vj : v j=0 := by by_contra h;exact hUj ⟨v,hv,h⟩
    have ji : j≠i := by rintro rfl;exact hwj hwi
    have ee := hx j
    change (Pi.single i (1:K):Vec K (s+1)) j-(mesh6:K[X]).eval (c j)=u j+Q.eval (c j)*w j at ee
    rw [Pi.single_eq_of_ne ji,uj,zero_sub,zero_add] at ee
    have ff := hy j
    change w j*w j-α*(ghost8:K[X]).eval (c j)=v j+R.eval (c j)*w j at ff
    rw [vj,zero_add] at ff
    refine ⟨hwj,?_,?_⟩
    · change (X*RKCert.OrderTwelve.dFivePoly).eval (c j)=w j*(-Q).eval (c j)
      rw [←mesh_factor,eval_neg];linear_combination -ee
    · change (w j)^2=(α • (ghost8:K[X])).eval (c j)+w j*R.eval (c j)
      rw [eval_smul];linear_combination ff
  have hf : (offFeatures U c w).card≤2 := by
    apply (Finset.card_le_card (t:=({0,1}:Finset K)) ?_).trans (by simp)
    intro x hx'
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx'
    obtain ⟨hUj,hwj⟩:=(Finset.mem_filter.mp hj).2
    by_cases eq:j=i
    · subst j
      have hci : c i=1 := hc
      simp [hci]
    have uj:u j=0 := by by_contra h;exact hUj ⟨u,hu,h⟩
    have vj:v j=0 := by by_contra h;exact hUj ⟨v,hv,h⟩
    have ee:=hx j
    change (Pi.single i (1:K):Vec K (s+1)) j-(mesh6:K[X]).eval (c j)=u j+Q.eval (c j)*w j at ee
    rw [Pi.single_eq_of_ne eq,uj,hwj,mul_zero,add_zero,zero_sub,neg_eq_zero] at ee
    have ff := hy j
    change w j*w j-α*(ghost8:K[X]).eval (c j)=v j+R.eval (c j)*w j at ff
    rw [vj,hwj,mul_zero,mul_zero,add_zero,zero_sub,neg_eq_zero] at ff
    have hh := mesh_ghost8_no_common (c j) ee ((mul_eq_zero.mp ff).resolve_left hα)
    simp [hh]
  have hb := count_by_features U w 7 hh.inv hU hdis htop
  change s+1≤finrank K U+S.card+(offFeatures U c w).card at hb
  have hd:=hs.size
  omega

end RKCert.Paired.OrderTwelve

