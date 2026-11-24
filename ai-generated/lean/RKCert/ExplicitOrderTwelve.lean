module

public import RKCert.OrderTwelveContrastGates
public import RKCert.OrderTwelveOffMask
public import RKCert.OrderTwelveReverseObstruction

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

omit [CharZero K] in
private theorem last_weight_tail {b:Vec K (s+1)} : ∀ j, Fin.last s<j→b j=0 :=
  fun j h=>False.elim ((not_lt_of_ge (Fin.le_last j)) h)

omit [CharZero K] in
private theorem head_paid (hh:HeadData A r U w) (k:ℕ) (hk:k<r) :
    (diag (nodes A)^k) w ∈zeroSpace A 5 := by
  rw [hh.f5]
  exact ((chain_le_iff r).mp le_rfl).2 k hk

private theorem grade_two_in_core (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0) (h:FullChart A r U w) :
    zeroSpace A 2≤U := by
  intro v hv
  by_contra hvo
  have no : ∀ j,Fin.last s<j→b j=0 := last_weight_tail
  have n : r+2<(headSites (nodes A) w).card := by have := h.sites;omega
  have core := core_grade7_multiplier ha ho hs hi no h.head n hv
  have band (k:ℕ) (hk:k<r) :
      v*((diag (nodes A)^k) w) ∈chain (diag (nodes A)) U w (r+2) := by
    rw [←h.head.f7tail,escape7_exact ha ho hs hi no]
    have hw := head_paid h.head k hk
    have he := f5_vanish_at_last_active ha ho hs hi no hw
    exact ⟨zeroSpace_mul hv hw,by change v (Fin.last s)*((diag (nodes A)^k) w (Fin.last s))=0;rw [he,mul_zero]⟩
  have v5 : v∈chain (diag (nodes A)) U w r := h.head.f5 ▸ zeroSpace_mono A (by decide : 2≤5) hv
  obtain ⟨P,hP,dP,fit⟩:=multiplier_profile h.head.inv core h.head.normalized n (by have := h.head.pos;omega)
    band v5 hvo
  exact low_contrast_exclusion ha ho hs hi h.head core P hP (by omega) hv fit

private theorem grade_three_in_core (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0) (h:FullChart A r U w) :
    zeroSpace A 3≤U := by
  intro v hv
  by_contra hvo
  have no : ∀ j,Fin.last s<j→b j=0 := last_weight_tail
  have n : r+3<(headSites (nodes A) w).card := by have := h.sites;omega
  have core : U.map (diag v)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have hm := core_grade8_multiplier ha ho hs hi no h.head h.e8 h.e9 h.e9r n
      h.head.low (by decide) hu hv
    have ee : diag v u=u*v := by ext j;simp [mul_comm]
    rwa [ee]
  let C:=diag (nodes A)
  let f (k:ℕ) := v*((C^k) w)
  have ff (k:ℕ) : C (f k)=f (k+1) := by
    ext j
    simp [f,C,pow_diag_apply,pow_succ]
    ring
  have f8 (k:ℕ) (hk:k<r) : f k∈endZero A 8 (Fin.last s) := by
    have hw := head_paid h.head k hk
    have he := f5_vanish_at_last_active ha ho hs hi no hw
    exact ⟨zeroSpace_mul hv hw,by change v (Fin.last s)*((C^k) w (Fin.last s))=0;rw [he,mul_zero]⟩
  have le (k:ℕ) (hk:k<r) : f k∈chain C U w (r+3) := by
    by_cases hnext:k+1<r
    · have hh : C (f k)∈endZero A 8 (Fin.last s) := by rw [ff];exact f8 (k+1) hnext
      exact (no_double_leak_both ha ho hs hi no h.head h.e8 h.e9 h.e9r (f8 k hk) hh).1
    · have hpos := h.head.pos
      have ek : k-1+1=k := by omega
      have hk1 : C (f (k-1))∈endZero A 8 (Fin.last s) := by
        rw [ff,ek];exact f8 k hk
      have hh := (no_double_leak_both ha ho hs hi no h.head h.e8 h.e9 h.e9r
        (f8 (k-1) (by omega)) hk1).2
      change C (f (k-1))∈chain C U w (r+3) at hh
      rwa [ff,ek] at hh
  have v5 : v∈chain C U w r := h.head.f5 ▸ zeroSpace_mono A (by decide : 3≤5) hv
  obtain ⟨P,hP,dP,fit⟩:=multiplier_profile h.head.inv core h.head.normalized n (by have := h.head.pos;omega)
    le v5 hvo
  have cheap (R:K[X]) (dR:R.natDegree≤2) : weightedEval (nodes A) v R∈zeroSpace A 5 :=
    zeroSpace_mono A (by omega : 3+R.natDegree≤5) (stage_weighted_grade ho R (by omega) hv)
  have high : weightedEval (nodes A) v (X^3)∈zeroSpace A 6 := by
    apply zeroSpace_mono A (show 3+((X:K[X])^3).natDegree≤6 by simp)
    exact stage_weighted_grade ho (X^3) (by simp) hv
  exact cubic_contrast_exclusion ha ho hs hi h.head core P hP (by omega) fit cheap high
  
set_option maxHeartbeats 7000000 in
private theorem exclude_three_four (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0) (h:FullChart A 3 U w)
    (hr:finrank K (zeroSpace A 4)=4) : False := by
  classical
  let c:=nodes A
  let C:=diag c
  have no : ∀ j,Fin.last s<j→b j=0 := last_weight_tail
  have h4 : zeroSpace A 4=chain C U w 2 := four_grade_exact hs h.head hr
  have pp := (chain_le_iff (T:=C) (U:=U) (w:=w) 2).mp le_rfl
  have le4 : U≤zeroSpace A 4 := by rw [h4];exact pp.1
  have hw4 : w∈zeroSpace A 4 := by rw [h4];simpa only [pow_zero,one_apply_eq_self] using pp.2 0 (by decide)
  have sit : 6<(headSites c w).card := by
    have H : 8≤(headSites c w).card := h.sites
    omega
  have mul (u v : Vec K (s+1)) (hu:u∈U) (hv:v∈zeroSpace A 4) : u*v∈U :=
    core_grade8_multiplier ha ho hs hi no h.head h.e8 h.e9 h.e9r sit le4 (by decide) hu hv
  have hU : MulClosed U := fun u hu v hv => mul u v hu (le4 hv)
  obtain ⟨z,_,hdis,hz⟩:=disjoint_full_chart hs h hU (fun u hu=>mul u w hu hw4)
  have hZ4 : zeroSpace A 4=chain C U z 2 := four_grade_exact hs hz.head hr
  have pz := (chain_le_iff (T:=C) (U:=U) (w:=z) 2).mp le_rfl
  have z4 : z∈zeroSpace A 4 := by rw [hZ4];simpa only [pow_zero,one_apply_eq_self] using pz.2 0 (by decide)
  have cz4 : C z∈zeroSpace A 4 := by rw [hZ4];simpa only [pow_one] using pz.2 1 (by decide)
  have zi := f5_vanish_at_last_active ha ho hs hi no (zeroSpace_mono A (by decide:4≤5) z4)
  have czi : C z (Fin.last s)=0 := by simp [C,zi]
  have z0 : z*z∈endZero A 8 (Fin.last s) := ⟨zeroSpace_mul z4 z4,by change z _*z _=0;rw [zi,zero_mul]⟩
  have z1 : C (z*z)∈endZero A 8 (Fin.last s) := by
    have eq:C (z*z)=(C z)*z := by ext j;simp [C,mul_assoc]
    rw [eq]
    exact ⟨zeroSpace_mul cz4 z4,by change C z _*z _=0;rw [zi,mul_zero]⟩
  have z2 : C (C (z*z))∈endZero A 8 (Fin.last s) := by
    have eq:C (C (z*z))=(C z)*(C z) := by ext j;simp [C];ring
    rw [eq]
    exact ⟨zeroSpace_mul cz4 cz4,by change C z _*C z _=0;rw [czi,zero_mul]⟩
  have hB0 := no_double_leak_both ha ho hs hi no hz.head hz.e8 hz.e9 hz.e9r z0 z1
  have hB1 := no_double_leak_both ha ho hs hi no hz.head hz.e8 hz.e9 hz.e9r z1 z2
  have bb (k:ℕ) (hk:k≤2) : (C^k) (z*z)∈chain C U z 6 := by
    interval_cases k
    · simpa only [pow_zero,one_apply_eq_self] using hB0.1
    · simpa only [pow_one] using hB0.2
    · simpa only [pow_two,mul_apply_eq_comp] using hB1.2
  have sitz : 6<(headSites c z).card := by
    have HH : 8≤(headSites c z).card := hz.sites
    omega
  obtain ⟨P,hD,fit⟩ := multiplier_degree (a:=z) (n:=6) (d:=2) hdis sitz bb
  have hp : P≠0 := by
    intro Pz
    have zZ:z=0 := by
      ext j
      by_contra h
      exact h (by simpa [Pz] using fit j h)
    simp [zZ,headSites] at sitz
  have dp : P.natDegree≤3 := by rcases hD with e|e;exact (hp e).elim;omega
  have wfit : z*z-weightedEval c z P∈U := by
    have e : z*z-weightedEval c z P=0 := by
      ext j
      by_cases h:z j=0
      · simp [h]
      · simp only [Pi.sub_apply,Pi.mul_apply,weightedEval_apply,Pi.zero_apply]
        rw [←fit j h,sub_self]
    rw [e];exact U.zero_mem
  have hV : U.map (diag z)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have em : diag z u=u*z := by ext j;simp [mul_comm]
    rw [em];exact mul u z hu z4
  have cheap (R:K[X]) (dR:R.natDegree≤2) : weightedEval c z R∈zeroSpace A 5 := by
    have hdeg : R.divX.natDegree≤1 := by rw [natDegree_divX_eq_natDegree_tsub_one];omega
    have hq : weightedEval c (C z) R.divX∈zeroSpace A 5 :=
      zeroSpace_mono A (by omega : 4+R.divX.natDegree≤5)
        (stage_weighted_grade ho R.divX (by omega) cz4)
    have hv : R.coeff 0 • z∈zeroSpace A 5 :=
      (zeroSpace A 5).smul_mem _ (zeroSpace_mono A (by decide :4≤5) z4)
    have e : weightedEval c z R=weightedEval c (C z) R.divX+R.coeff 0 • z := by
      ext j
      have ee := congrArg (fun P:K[X]=>P.eval (c j)) (X_mul_divX_add R)
      simp only [eval_add,eval_mul,eval_X,eval_C] at ee
      simp only [weightedEval_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      change R.eval (c j)*z j=R.divX.eval (c j)*(c j*z j)+R.coeff 0*z j
      rw [←ee];ring
    rw [e];exact (zeroSpace A 5).add_mem hq hv
  have high : weightedEval c z (X^3)∈zeroSpace A 6 := by
    have e : weightedEval c z (X^3)=weightedEval c (C z) (X^2) := by
      ext j
      simp [C]
      ring
    rw [e]
    apply zeroSpace_mono A (show 4+((X:K[X])^2).natDegree≤6 by simp)
    exact stage_weighted_grade ho (X^2) (by simp) cz4
  exact cubic_contrast_exclusion ha ho hs hi hz.head hV P hp dp wfit cheap high

/-- Exhaust the actual equality chart over a characteristic-zero field. -/
theorem no_full_order_twelve_chart (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0) (h:FullChart A r U w) : False := by
  have pos := h.head.pos
  have rd := h.head.rank
  have hF2 := Submodule.finrank_mono (grade_two_in_core ha ho hs hi h)
  have l2 := zeroSpace_finrank ha ho (n:=1) (by decide)
  change 1≤finrank K (zeroSpace A 2) at l2
  have r4 : r≤4 := by omega
  have sep := explicit_separated ha ho (q:=6) (by decide) (by omega)
  have l3 := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at l3
  have h3 := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha sep (j:=3) (by decide) (by decide))
  have h4 := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha sep (j:=4) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at h3
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at h4
  have h5 := hs.f5
  have no : ∀ j,Fin.last s<j→b j=0 := last_weight_tail
  by_cases rr:r=2
  · subst r
    by_cases hq:finrank K (zeroSpace A 4)=3
    · exact exclude_two_three ha ho hs hi no h hq
    · exact exclude_two_four ha ho hs hi no h (by omega)
  have F3:=grade_three_in_core ha ho hs hi h
  have hF3:=Submodule.finrank_mono F3
  have r3 : r=3 := by omega
  subst r
  have eq3 : zeroSpace A 3=U := Submodule.eq_of_le_of_finrank_le F3 (by omega)
  have gain := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=3) (by decide) U
    (le_of_eq eq3.symm) (fun _ hw=>h.head.inv (Submodule.mem_map_of_mem hw))
  change finrank K U+2≤finrank K (zeroSpace A 4) at gain
  exact exclude_three_four ha ho hs hi h (by omega)

end RKCert.Paired.OrderTwelve

namespace RKCert
open RKCert.Paired RKCert.Paired.OrderTwelve
/-- Explicit order 12 requires at least 18 stages over any field of
characteristic zero. No assumption on the signs or zeros of weights or on
distinctness of nodes is imposed. -/
theorem explicit_order12_ge18_field {K:Type*} [Field K] [CharZero K] {s:ℕ}
    {A:Fin s→Fin s→K} {b:Vec K s} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) :
    18≤s := by
  by_contra! hs
  cases s with
  | zero =>
    have hf := explicit_order_le_stages ha ho
    omega
  | succ s =>
    have H := saturation_at_most_seventeen ha ho (by omega)
    have L := actual_last_at_most_seventeen ha ho (by omega)
    have E := saturated_e9_escape ha ho H
    have no : ∀ j,Fin.last s<j→b j=0 := fun j h=>False.elim ((not_lt_of_ge (Fin.le_last j)) h)
    obtain ⟨r,U,w,h⟩:=full_chart_of_escape9 ha ho H L no E
    exact no_full_order_twelve_chart ha ho H L h

/-- The order-12 improvement extends to characteristic-zero commutative
rings, including rings with zero divisors. -/
theorem explicit_order12_ge18_charZero {R:Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) :
    18≤s :=
  explicit_of_charZero_fields (fun _ _ _ _ _ hA hO=>explicit_order12_ge18_field hA hO) ha ho

end RKCert

