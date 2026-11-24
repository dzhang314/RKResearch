module

public import RKCert.OrderTwelveCoreRanks

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {i:Fin (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

omit [CharZero K] in
theorem weighted_head_faithful {c:Vec K (s+1)}
    (hU:U.map (diag c)≤U)
    (norm:∀ x,fiber c x w∈U→fiber c x w=0)
    {P:K[X]} (deg:P.degree<((headSites c w).card:WithBot ℕ))
    (hp:weightedEval c w P∈U) : P=0 := by
  classical
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (headSites c w) deg
  intro a ha
  have e : fiber c a (weightedEval c w P) = P.eval a • fiber c a w := by
    ext j
    by_cases h:c j=a <;> simp [fiber,h,weightedEval_apply]
  have hm := fiber_mem hU a hp
  rw [e] at hm
  by_contra hz
  have hh := (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr hz)).mp hm
  exact nonzero_fiber ha (norm a hh)

omit [CharZero K] in
theorem multiplier_profile {c v:Vec K (s+1)}
    (hU:U.map (diag c)≤U) (hV:U.map (diag v)≤U)
    (norm:∀ x,fiber c x w∈U→fiber c x w=0)
    {n:ℕ} (count:n<(headSites c w).card) (hr:0<r)
    (band:∀ k<r, v*((diag c^k) w)∈chain (diag c) U w n)
    (hv:v∈chain (diag c) U w r) (out:v∉U) :
    ∃ P:K[X], P≠0 ∧ P.natDegree+r≤n ∧ v*w-weightedEval c w P∈U := by
  classical
  have fit (k:ℕ) (hk:k<r) :
    ∃ P:K[X], P.degree<(n:WithBot ℕ) ∧ v*((diag c^k) w)-weightedEval c w P∈U := by
    obtain ⟨u,hu,P,hP,eq⟩:=exists_head_poly (band k hk)
    refine ⟨P,hP,?_⟩
    have e : v*((diag c^k) w)-weightedEval c w P=u := by
      ext j
      have hh:=eq j
      change v j*((diag c^k) w j)=u j+P.eval (c j)*w j at hh
      rw [Pi.sub_apply,Pi.mul_apply,weightedEval_apply]
      rw [hh,add_sub_cancel_right]
    rwa [e]
  obtain ⟨P,hp,mem⟩:=fit 0 hr
  have mem' : v*w-weightedEval c w P∈U := by
    simpa only [pow_zero,one_apply_eq_self] using mem
  have hp0:P≠0 := by
    intro z
    have hw : v*w∈U := by simpa only [z,map_zero,sub_zero] using mem'
    obtain ⟨u,hu,Q,_,eq⟩:=exists_head_poly hv
    have vu : v*u∈U := hV (Submodule.mem_map_of_mem hu)
    have Pvw := poly_preserves hU Q (v*w) hw
    have vv : v*v∈U := by
      have h := U.add_mem vu Pvw
      have e : v*u+(fun j=>Q.eval (c j)*(v*w) j)=v*v := by
        ext j
        change v j*u j+Q.eval (c j)*(v j*w j)=v j*v j
        linear_combination -v j*(eq j)
      rwa [e] at h
    let F := Lagrange.interpolate (sites v) id (fun x:K=>x⁻¹)
    have h := poly_preserves hV F (v*v) vv
    have e : (fun j=>F.eval (v j)*(v*v) j)=v := by
      ext j
      have h' : F.eval (v j)=(v j)⁻¹ :=
        Lagrange.eval_interpolate_at_node (fun x:K=>x⁻¹) (Set.injOn_id _) (site_mem v j)
      rw [h',Pi.mul_apply,←mul_assoc]
      by_cases hz:v j=0 <;> simp [hz]
    exact out (e ▸ h)
  have hPow (k:ℕ) : v*((diag c^k) w)-weightedEval c w (X^k*P)∈U := by
    have he := pow_mem hU mem' k
    convert he using 1
    ext j
    simp [mul_sub,eval_mul,weightedEval_apply,pow_diag_apply]
    ring
  have dPow (k:ℕ) (hk:k<r) :
      (X^k*P).degree<(n:WithBot ℕ) := by
    induction k with
    | zero => simpa only [pow_zero,one_mul] using hp
    | succ k ih =>
      obtain ⟨Q,qd,hQ⟩ := fit (k+1) hk
      have dif : weightedEval c w (X^(k+1)*P-Q)∈U := by
        rw [map_sub]
        convert U.sub_mem hQ (hPow (k+1)) using 1
        abel
      have dX : (X^(k+1)*P).degree<((headSites c w).card:WithBot ℕ) := by
        have hP' := mul_ne_zero (pow_ne_zero k X_ne_zero) hp0
        have d := (natDegree_lt_iff_degree_lt hP').mpr (ih (by omega))
        have eq : X^(k+1)*P=X*(X^k*P) := by rw [pow_succ'];ring
        rw [eq]
        apply (natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero hP')).mp
        rw [natDegree_X_mul hP']
        omega
      have de := (degree_sub_le (X^(k+1)*P) Q).trans_lt
        (max_lt dX (qd.trans (by exact_mod_cast count)))
      have e := sub_eq_zero.mp (weighted_head_faithful hU norm de dif)
      rw [e]
      exact qd
  have dlast:= dPow (r-1) (by omega)
  have hlast := (natDegree_lt_iff_degree_lt (mul_ne_zero (pow_ne_zero (r-1) X_ne_zero) hp0)).mpr dlast
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp0,natDegree_X_pow] at hlast
  exact ⟨P,hp0,by omega,mem'⟩

omit [CharZero K] in
theorem profile_vanish_on_block {c v:Vec K (s+1)} {P:K[X]}
    (hU:U.map (diag c)≤U) (hV:U.map (diag v)≤U)
    (hm:v*w-weightedEval c w P∈U) {x τ:K} (hne:τ≠P.eval x) :
    fiber v τ (fiber c x w) ∈ U := by
  classical
  have hs := fiber_mem hV τ (fiber_mem hU x hm)
  have e : fiber v τ (fiber c x (v*w-weightedEval c w P)) =
     (τ-P.eval x) • fiber v τ (fiber c x w) := by
    ext j
    by_cases h:c j=x <;> by_cases h':v j=τ <;>
      simp [fiber,h,h',weightedEval_apply,sub_mul]
  rw [e] at hs
  exact (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))).mp hs

theorem core_grade7_multiplier (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    (hh:HeadData A r U w) (hcount:r+2<(headSites (nodes A) w).card)
    {v:Vec K (s+1)} (hv:v∈zeroSpace A 2) :
    U.map (diag v)≤U := by
  classical
  rintro _ ⟨u,hu,rfl⟩
  have e : diag v u=∑ z ∈ sites (nodes A), fiber (nodes A) z u*v := by
    rw [←Finset.sum_mul,sum_fibers]
    ext j
    simp [mul_comm]
  rw [e]
  apply U.sum_mem
  intro a _
  have hf := fiber_mem hh.inv a hu
  have hz := f5_vanish_at_last_active ha ho hs hi hl (hh.low hf)
  have h : fiber (nodes A) a u*v∈endZero A 7 i :=
    ⟨zeroSpace_mul (hh.low hf) hv,by change _*v i=0;rw [hz,zero_mul]⟩
  rw [←escape7_exact ha ho hs hi hl,hh.f7tail] at h
  apply localized_mem (z:=a) hh.inv hh.normalized hcount h
  intro j hn
  simp [fiber,hn]

end RKCert.Paired.OrderTwelve

