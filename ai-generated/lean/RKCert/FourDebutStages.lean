module
public import RKCert.FourDebutRank
public import RKCert.DIRKPivots

@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape Module Polynomial
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {c w : Vec K s}

noncomputable def outerSites (c : Vec K s) (U : Submodule K (Vec K s)) : Finset K := by
  classical exact (Finset.univ.filter fun i => ¬Live U i ∧ c i≠0).image c

/-- Each nonzero aggregate-weight abscissa occurs outside the actual invariant
grade-three algebra, even if copies also occur inside masks at the same clock. -/
theorem active_outside [CharZero K] (ho : HasTreeOrderAtLeast A b p) (hpay : 4≤p)
    (hT : U.map (diag (nodes A))≤U) (hm : MulClosed U) (hin : U≤zeroSpace A 3) :
    RKCert.Endpoint.activeNonzero (nodes A) b ⊆ outerSites (nodes A) U := by
  classical
  obtain ⟨e,he,eqn⟩ := core_indicator hm
  intro z hz
  have ⟨_,h0,hmass⟩ := Finset.mem_filter.mp hz
  by_contra h
  apply hmass
  have all (i : Fin s) (hi : nodes A i=z) : Live U i := by
    by_contra hn
    exact h (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn,hi ▸ h0⟩,hi⟩)
  have hprobe : probe A b 0 (fiber (nodes A) z e)=0 :=
    probe_zeroSpace ho (by omega : 0+3+1≤p) (hin (fiber_mem hT z he))
  have ee : probe A b 0 (fiber (nodes A) z e)=RKCert.Endpoint.combinedMass (nodes A) b z := by
    rw [probe,row_apply,RKCert.Endpoint.combinedMass,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases e : nodes A i=z
    · simp [fiber,e,eqn,all i e]
    · simp [fiber,e]
  rwa [←ee]

/-- In particular there really are four distinct nonzero physical outside sites at p=8. -/
theorem outer_count [CharZero K] (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (hT : U.map (diag (nodes A))≤U) (hm : MulClosed U) (hin : U≤zeroSpace A 3) :
    4≤(outerSites (nodes A) U).card := by
  have h := Finset.card_le_card (active_outside ho (by omega) hT hm hin)
  have h' := RKCert.Endpoint.activeNonzero_card_of_treeOrder ho
  omega

/-- Earliest actual outside nonzero stage whose clock is not in S. -/
structure Debut (c : Vec K s) (U : Submodule K (Vec K s)) (S : Finset K) (i : Fin s) : Prop where
  outsideU : ¬Live U i
  nz : c i≠0
  fresh : c i∉S
  old : ∀ l < i, ¬Live U l → c l≠0 → c l∈S

theorem next_debut (S : Finset K) (count : S.card < (outerSites c U).card) :
    ∃ i : Fin s, Debut c U S i := by
  classical
  have hn : ¬outerSites c U ⊆ S := fun h => (not_le_of_gt count) (Finset.card_le_card h)
  obtain ⟨z,hz,hs⟩ := Finset.not_subset.mp hn
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  let F := Finset.univ.filter fun l => ¬Live U l ∧ c l≠0 ∧ c l∉S
  have fi : i∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1,
    (Finset.mem_filter.mp hi).2.2,hs⟩
  have ne : F.Nonempty := ⟨i,fi⟩
  let l := F.min' ne
  have h := (Finset.mem_filter.mp (F.min'_mem ne)).2
  refine ⟨l,h.1,h.2.1,h.2.2,?_⟩
  intro k hk ho non
  by_contra no
  exact (not_le_of_gt hk) (F.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho,non,no⟩))

/-- Arbitrary nodewise scalar functions preserve a clock-invariant space
of physical stage columns; true even over finite fields. -/
theorem function_stable (hT : U.map (diag c)≤U) (F : K→K) {e : Vec K s} (he : e∈U) :
    (fun i => F (c i)*e i) ∈ U := by
  classical
  let P := Lagrange.interpolate (sites c) id F
  have h := poly_preserves hT P e he
  convert h using 1
  ext i
  rw [show P.eval (c i)=F (c i) from Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) (site_mem c i)]

/-- Match a polynomial exactly off U, zero on all live physical rows, at
the cost of subtracting just one genuine F3 element. -/
theorem masked_polynomial (hT : U.map (diag c)≤U) (hm : MulClosed U) (P : Polynomial K) :
    ∃ v : Vec K s, v-(fun i=>P.eval (c i))∈U ∧
      (∀i, Live U i→v i=0) ∧ (∀i, ¬Live U i→v i=P.eval (c i)) := by
  classical
  obtain ⟨e,he,eqn⟩ := core_indicator hm
  let F : Vec K s := fun i=>P.eval (c i)
  let M : Vec K s := fun i=>P.eval (c i)*e i
  refine ⟨F-M,?_,?_,?_⟩
  · have eqn : (F-M)-F = - M := by abel
    rw [eqn]
    exact U.neg_mem (poly_preserves hT P e he)
  · intro i hi
    simp [F,M,Pi.sub_apply,eqn,hi]
  · intro i hi
    simp [F,M,Pi.sub_apply,eqn,hi]


/-- Exact chronological lift. Compatibility is deliberately measured before
the debut on all physical stages, not only on representatives of clock sites.
The original tableau is not compressed, and w may vary inside a live class. -/
theorem fit_prefix {m : ℕ} {i : Fin s} (ix : Fin m→Fin s)
    (prior : ∀ k,ix k < i) (outs : ∀ k,¬Live U (ix k))
    (cover : ∀l < i, ¬Live U l → c l≠0 → ∃k,c l=c (ix k))
    (hT : U.map (diag c)≤U) (hm : MulClosed U)
    {P Q : Polynomial K} (p0 : P.eval 0=0) (hQ : Q∈compatible c w U i)
    (vals : ∀k,P.eval (c (ix k))=w (ix k)*Q.eval (c (ix k))) :
    ∃ u∈U, ∀l < i, P.eval (c l)-w l*Q.eval (c l) = u l := by
  classical
  obtain ⟨F,h0,u,hu,fit⟩ := hQ
  obtain ⟨e,he,eh⟩ := core_indicator hm
  let D : Vec K s := fun l=>(P.eval (c l)-F (c l))*e l
  have hd : D∈U := function_stable hT (fun z=>P.eval z-F z) he
  have uz (l : Fin s) (hl : ¬Live U l) : u l=0 := by by_contra h; exact hl ⟨u,hu,h⟩
  have fz (k : Fin m) : P.eval (c (ix k))=F (c (ix k)) := by
    rw [vals,fit (ix k) (prior k),uz _ (outs k),zero_add]
  refine ⟨D-u,U.sub_mem hd hu,?_⟩
  intro l hl
  change _=(P.eval (c l)-F (c l))*e l-u l
  rw [fit l hl]
  by_cases hv : Live U l
  · simp only [eh,hv,ite_true,mul_one]; ring
  · have f : P.eval (c l)=F (c l) := by
      by_cases z : c l=0
      · rw [z,p0,h0]
      · obtain ⟨k,hk⟩ := cover l hl hv z
        rw [hk,fz k]
    simp [eh,hv,f,uz l hv]

theorem zero_pure_at {U : Submodule K (Vec K s)} {w : Vec K s} {j n : ℕ} {i : Fin s}
    (outsideU : ¬Live U i) (wi : w i=0)
    (flag : zeroSpace A j ≤ chain (diag (nodes A)) U w n) : Clean A i j := by
  intro x hx
  obtain ⟨u,hu,P,_,eqn⟩ := exists_head_poly (flag hx)
  have zu : u i=0 := by by_contra h; exact outsideU ⟨u,hu,h⟩
  simpa [zu,wi] using eqn i

/-- Refund at a fourth debut does not require the current head to be zero.
Actual earlier nonzero heads force the entire commutator polynomial to be
zero; diagonal refund is a conclusion of the rooted-tree equations. -/
theorem refund_by_old {n j : ℕ} {i : Fin s} {v w : Vec K s} (ix : Fin n→Fin s)
    (ha : SDIRK.lower A) (ho : HasTreeOrderAtLeast A b p) (pay : j+2≤p)
    (hg : v∈treeSpace A j) (pfx : PrefixZero v i) (vi : v i≠0)
    (out : ¬Live U i) (early : ∀k, ix k < i)
    (outsideU : ∀k,¬Live U (ix k)) (nz : ∀k,w (ix k)≠0)
    (distinct : Function.Injective (fun k => nodes A (ix k)))
    (flag : zeroSpace A (j+2) ≤ chain (diag (nodes A)) U w n) : A i i=0 := by
  classical
  have hR := commutator_mem_zeroSpace ho j pay hg
  change SDIRK.R A v∈zeroSpace A (j+2) at hR
  obtain ⟨u,hu,P,deg,row⟩ := exists_head_poly (flag hR)
  have uz (l : Fin s) (hl : ¬Live U l) : u l=0 := by by_contra h; exact hl ⟨u,hu,h⟩
  have pv (k : Fin n) : P.eval (nodes A (ix k))=0 := by
    have hv := row (ix k)
    rw [SDIRK.commutator_lead ha (ix k) v (fun l hl => pfx l (hl.trans (early k))),
      pfx _ (early k),mul_zero,uz _ (outsideU k),zero_add] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_right (nz k)
  have z : P=0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
    distinct.injOn (by simpa only [Finset.card_univ,Fintype.card_fin] using deg) (fun k _=>pv k)
  have hv := row i
  rw [SDIRK.commutator_lead ha i v pfx,uz _ out,z,Polynomial.eval_zero,zero_mul,add_zero] at hv
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right vi))

/-- The second, output-side prefix compatibility is obtained from the SAME
actual hidden mask U. The target diagonal is previously refunded. -/
theorem primitive_output [CharZero K] {m j : ℕ} {i : Fin s} {v w : Vec K s}
    (ha : SDIRK.lower A) (flag : zeroSpace A (j+1) ≤ chain (diag (nodes A)) U w m)
    {P : Polynomial K} (hp : P.natDegree≤j) (hm : v-evalNodes A P∈zeroSpace A j)
    (pfx : PrefixZero v i) (ai : A i i=0) :
    ∃ Q : Polynomial K, Q.degree < (m:WithBot ℕ) ∧ Q∈compatible (nodes A) w U i ∧
      ∀ l ≤ i, ¬Live U l → (primitive P).eval (nodes A l)=w l*Q.eval (nodes A l) := by
  have h1 := mat_zeroSpace_charZero A j hm
  rw [Submodule.mem_comap,map_sub] at h1
  have h2 := primitive_defect A P hp
  have dif : evalNodes A (primitive P)-mat A v∈zeroSpace A (j+1) := by
    convert (zeroSpace A (j+1)).neg_mem ((zeroSpace A (j+1)).add_mem h1 h2) using 1
    abel
  obtain ⟨u,hu,Q,de,obs⟩ := exists_head_poly (flag dif)
  have hz (l : Fin s) (hl : l ≤ i) : mat A v l=0 := by
    rw [mat_at_prefix ha l v (fun k hk => pfx k (hk.trans_le hl))]
    rcases lt_or_eq_of_le hl with h|rfl
    · rw [pfx l h,mul_zero]
    · rw [ai,zero_mul]
  have val (l : Fin s) (hl : l ≤ i) :
      (primitive P).eval (nodes A l)=u l+Q.eval (nodes A l)*w l := by
    simpa only [Pi.sub_apply,evalNodes_apply,hz l hl,sub_zero] using obs l
  have hq : Q∈compatible (nodes A) w U i := by
    refine ⟨fun z=>(primitive P).eval z,?_, -u,U.neg_mem hu,?_⟩
    · change (primitive P).eval 0=0
      rw [←Polynomial.coeff_zero_eq_eval_zero,primitive_coeff_zero]
    · intro l hl
      change w l*Q.eval (nodes A l) = -u l +(primitive P).eval (nodes A l)
      rw [val l hl.le]; ring
  refine ⟨Q,de,hq,fun l hl out=>?_⟩
  have z : u l=0 := by by_contra h; exact out ⟨u,hu,h⟩
  rw [val l hl,z,zero_add,mul_comm]

end RKCert.FourDebut
