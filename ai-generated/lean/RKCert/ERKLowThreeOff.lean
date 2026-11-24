module

public import RKCert.ERKLowMoments

@[expose] public section

/-! # Three off nodes force at most two on nodes, by actual chronology -/
namespace RKCert.Paired
open Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

noncomputable def offTap (A : Fin s → Fin s → K) (i : Fin s) (x : K) : K :=
  ∑ j, if qdef A j≠0 ∧ nodes A j=x then A i j * qdef A j else 0

omit [CharZero K] in
theorem offTap_pair (A : Fin s → Fin s → K) (i : Fin s) (f : K → K) :
    (∑ x∈supportedNodes A (qdef A), offTap A i x * f x) =
      ∑ j, (A i j*qdef A j)*f (nodes A j) := by
  let T := supportedNodes A (qdef A)
  change (∑ x∈T, offTap A i x*f x)=_
  simp only [offTap,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : qdef A j=0
  · simp [hd]
  · have h : nodes A j∈T := mem_supportedNodes.mpr ⟨j,hd,rfl⟩
    rw [Finset.sum_eq_single (nodes A j)]
    · simp [hd]
    · intro x _ hx; simp [Ne.symm hx]
    · intro h'; exact False.elim (h' h)

omit [CharZero K] in
private theorem triple_zero {x f : Fin 3 → K} (hx : Function.Injective x)
    (hf0 : f 0=0) (h0 : (∑ j,f j)=0) (h1 : (∑ j,x j*f j)=0) : f=0 := by
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero] at h0 h1
  change f 0+(f 1+f 2)=0 at h0
  change x 0*f 0+(x 1*f 1+x 2*f 2)=0 at h1
  rw [hf0,zero_add] at h0
  rw [hf0,mul_zero,zero_add] at h1
  have hx' : x 1≠x 2 := fun h => (by decide : (1:Fin 3)≠2) (hx h)
  have h01 : f 1=0 := (mul_eq_zero.mp (show (x 1-x 2)*f 1=0 by
    linear_combination h1 - x 2*h0)).resolve_left (sub_ne_zero.mpr hx')
  have h02 : f 2=0 := by simpa [h01] using h0
  ext j
  have hh : ∀ k : Fin 3, k=0 ∨ k=1 ∨ k=2 := by decide
  rcases hh j with rfl|rfl|rfl
  · exact hf0
  · exact h01
  · exact h02

omit [CharZero K] in
/-- The two exact lower-grade defect tests leave a single direction for
all rows on a three-node off set. -/
theorem triple_off_proportional {x f g : Fin 3 → K} (hx : Function.Injective x)
    (hf0 : (∑ i,f i)=0) (hf1 : (∑ i,x i*f i)=0)
    (hg0 : (∑ i,g i)=0) (hg1 : (∑ i,x i*g i)=0) (hg : g≠0) :
    ∃ a : K, f=a • g := by
  have hg0n : g 0≠0 := fun h => hg (triple_zero hx h hg0 hg1)
  let a := f 0/g 0
  let u := f-a • g
  have hu0 : u 0=0 := by
    change f 0 - (f 0/g 0)*g 0=0
    rw [div_mul_cancel₀ _ hg0n,sub_self]
  have hu1 : (∑ i,u i)=0 := by
    simp only [u,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_sub_distrib,← Finset.mul_sum,
      hf0,hg0,mul_zero,sub_zero]
  have hu2 : (∑ i,x i*u i)=0 := by
    simp only [u,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
    have he : (∑ i,x i*(a*g i))=a*(∑ i,x i*g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hf1,he,hg1,mul_zero,sub_zero]
  exact ⟨a,sub_eq_zero.mp (triple_zero hx hu0 hu1 hu2)⟩

noncomputable def offPower (A : Fin s → Fin s → K) (P : Polynomial K)
    (i : Fin s) (n : ℕ) : K :=
  ∑ x∈supportedNodes A (qdef A), offTap A i x * (x^n/P.eval x)

noncomputable def onPower (A : Fin s → Fin s → K) (i : Fin s) (n : ℕ) : K :=
  ∑ j, if qdef A j=0 then A i j*nodes A j^n else 0

theorem matrix_power_split {A : Fin s → Fin s → K} {P : Polynomial K}
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) (i : Fin s) (n : ℕ) :
    mat A (fun j => nodes A j^n) i = offPower A P i n + onPower A i n := by
  rw [offPower,offTap_pair,mat_apply,onPower,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : qdef A j=0
  · simp [hd]
  · simp only [hP j hd,hd,ite_false,add_zero]
    calc
      _ = A i j * (nodes A j^n / qdef A j * qdef A j) := by rw [div_mul_cancel₀ _ hd]
      _ = _ := by ring

omit [CharZero K] in
/-- Physical prefix calculation for an on-power contribution: no
coefficient beyond the target is used. -/
theorem onPower_from_prefix {A : Fin s → Fin s → K} (ha : StrictLower A) (i : Fin s)
    (z : K) {n : ℕ} (hn : n≠0)
    (hp : ∀ j, j < i → qdef A j=0 → nodes A j=0 ∨ nodes A j=z) :
    onPower A i n = z^n*(∑ j, if qdef A j=0 ∧ nodes A j=z then A i j else 0) := by
  rw [onPower,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < i
  · by_cases hd : qdef A j=0
    · rcases hp j hj hd with h|h
      · by_cases hz : z=0
        · simp [hd,h,hz,zero_pow hn]
        · simp [hd,h,Ne.symm hz,zero_pow hn]
      · simp [hd,h,mul_comm]
    · simp [hd]
  · have hA := ha i j (le_of_not_gt hj)
    simp [hA]

/-- The case N=3 of the nine-order finite proof, formalized directly in
the physical two-curve chart. It also applies at order eight. -/
theorem three_off_forces_two_on {A : Fin s → Fin s → K} (ha : StrictLower A)
    {P : Polynomial K} (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (hT : (supportedNodes A (qdef A)).card=3) :
    (onNodes A).card ≤ 2 := by
  let T := supportedNodes A (qdef A)
  have hTc : Fintype.card T = 3 := (Fintype.card_coe T).trans hT
  let e : Fin 3 ≃ T := (Fintype.equivFinOfCardEq hTc).symm
  let x (j : Fin 3) : K := (e j).val
  have hx : Function.Injective x := fun _ _ h => e.injective (Subtype.ext h)
  have hsum (g : K → K) : (∑ j : Fin 3, g (x j)) = ∑ a∈T, g a := by
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  let U : Set (Fin s) := {i | qdef A i=0 ∧ nodes A i≠0}
  by_cases hU : U.Nonempty
  · obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
    have hdi : qdef A i=0 := hi.1
    have hc : nodes A i≠0 := hi.2
    let h := nodes A i
    have hirst (j : Fin s) (hj : j < i) (hd : qdef A j=0) : nodes A j=0 := by
      by_contra hnd
      exact hmin j ⟨hd,hnd⟩ hj
    have hone (n : ℕ) (hn : n≠0) : onPower A i n=0 := by
      rw [onPower_from_prefix ha i 0 hn (fun j hj hd => Or.inl (hirst j hj hd)),zero_pow hn,zero_mul]
    obtain ⟨hPr,_,_⟩ := on_row_quartic_conditions hF hdi
    have hm (n : ℕ) (hn : n≠0) (h3 : n ≤ 3) :
        offPower A P i n = h^(n+1)/((n+1:ℕ):K) := by
      have ho := hPr n h3
      rw [matrix_power_split hP,hone _ hn,add_zero] at ho
      exact ho
    let f (k : Fin s) (j : Fin 3) := offTap A k (x j)
    have hconds (k : Fin s) (hk : qdef A k=0) :
        (∑ j,f k j)=0 ∧ (∑ j,x j*f k j)=0 := by
      obtain ⟨_,h0,h1⟩ := on_row_quartic_conditions hF hk
      constructor
      · change (∑ j : Fin 3, offTap A k (x j))=0
        rw [hsum (offTap A k)]
        have he := offTap_pair A k (fun _ => 1)
        simp only [mul_one] at he
        rw [he]
        exact h0
      · change (∑ j : Fin 3, x j*offTap A k (x j))=0
        rw [hsum (fun a => a*offTap A k a)]
        calc
          _ = ∑ a∈T, offTap A k a * a := Finset.sum_congr rfl (fun _ _ => mul_comm ..)
          _ = _ := by
            rw [offTap_pair A k (fun a => a)]
            simpa [mat_apply,mul_comm,mul_left_comm,mul_assoc] using h1
    have hfn : f i≠0 := by
      intro hz
      have hz' : offPower A P i 1=0 := by
        unfold offPower
        rw [← hsum]
        simp only [show ∀ j : Fin 3, offTap A i (x j)=0 from fun j =>
          congrFun hz j,zero_mul,Finset.sum_const_zero]
      have h := hm 1 (by decide) (by decide)
      rw [hz'] at h
      exact div_ne_zero (pow_ne_zero _ hc) (by norm_num) h.symm
    have hprops (k : Fin s) (hd : qdef A k=0) : ∃ a : K,
        ∀ n : ℕ, offPower A P k n = a*offPower A P i n := by
      obtain ⟨a,ha'⟩ := triple_off_proportional hx
        (hconds k hd).1 (hconds k hd).2 (hconds i hdi).1 (hconds i hdi).2 hfn
      refine ⟨a,?_⟩
      intro n
      unfold offPower
      rw [← hsum,← hsum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := congrFun ha' j
      change offTap A k (x j)=a*offTap A i (x j) at hj
      rw [hj,mul_assoc]
    have hon (k : Fin s) : qdef A k=0 → nodes A k=0 ∨ nodes A k=h := by
      apply (wellFounded_lt (α:=Fin s)).induction k
      intro j ih hd
      let y := nodes A j
      let S : K := ∑ k, if qdef A k=0 ∧ nodes A k=h then A j k else 0
      obtain ⟨a,ha'⟩ := hprops j hd
      obtain ⟨hp,_,_⟩ := on_row_quartic_conditions hF hd
      have htest (n : ℕ) (hn : n≠0) (h3 : n ≤ 3) :
          a*(h^(n+1)/((n+1:ℕ):K))+h^n*S=y^(n+1)/((n+1:ℕ):K) := by
        have hEq := hp n h3
        rwa [matrix_power_split hP,ha',hm n hn h3,
          onPower_from_prefix ha j h hn (fun l hl hl' => ih l hl hl')] at hEq
      have h1 := htest 1 (by decide) (by decide)
      have h2 := htest 2 (by decide) (by decide)
      have h3 := htest 3 (by decide) (by decide)
      norm_num only [Nat.cast_ofNat,Nat.reduceAdd,pow_one] at h1 h2 h3
      have h0 : y^2*(y-h)^2=0 := by
        linear_combination -4*h3 - 2*h^2*h1 + 6*h*h2
      rcases mul_eq_zero.mp h0 with hy|hy
      · exact Or.inl (eq_zero_of_pow_eq_zero hy)
      · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hy))
    have hsub : onNodes A ⊆ ({0,h}:Finset K) := by
      intro z hz
      obtain ⟨k,hd,rfl⟩ := mem_onNodes.mp hz
      simpa using hon k hd
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_pair (Ne.symm hc)])
  · have hsub : onNodes A ⊆ ({0}:Finset K) := by
      intro z hz
      obtain ⟨k,hd,rfl⟩ := mem_onNodes.mp hz
      have hz' : nodes A k=0 := by
        by_contra hn
        exact hU ⟨k,hd,hn⟩
      simpa using hz'
    exact (Finset.card_le_card hsub).trans (by simp)

/-- Actual order eight or nine, with saturated midpoint grades:
exactly three distinct off nodes are impossible. -/
theorem no_three_off_nodes {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)} {p : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p)
    (h3 : Module.finrank K (zeroSpace A 3)=2) (h4 : Module.finrank K (zeroSpace A 4)=3) :
    (supportedNodes A (qdef A)).card≠3 := by
  intro hc
  obtain ⟨P,_,_,_,hF,hP⟩ := two_curve_head h3 h4 (by omega)
  have hhigh := five_on_of_aggregate_zero ha ho hp
    (fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx)
  have hlow := three_off_forces_two_on ha hP hF hc
  omega

end RKCert.Paired
