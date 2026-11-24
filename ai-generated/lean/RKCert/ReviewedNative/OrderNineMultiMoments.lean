module
public import RKCert.ReviewedNative.OrderNineMultiHead

@[expose] public section

/-! # The clean quadrature forced by up to seven defective clocks

The defective rows may have repeated clocks and signed individual weights.
The actual order only cancels their total weight separately at each off
clock. A clean row at the very same clock is *not* removed. -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Polynomial OneOff
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p q : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

noncomputable def cleanKnots (A : Matrix (Fin s) (Fin s) K) : Finset K :=
  (Finset.univ.filter fun i => g A i=0).image (nodes A)

theorem mem_cleanKnots {x : K} : x∈cleanKnots A ↔ ∃i,g A i=0 ∧ nodes A i=x := by
  simp [cleanKnots]

theorem clean_off_count (A : Matrix (Fin s) (Fin s) K) :
    (cleanKnots A).card + (offKnots A).card ≤ s := by
  unfold cleanKnots offKnots
  apply (add_le_add Finset.card_image_le Finset.card_image_le).trans
  simpa using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => g A i=0)).le

noncomputable def offMass (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (x : K) : K :=
  ∑ i, if g A i≠0 ∧ nodes A i=x then b i else 0

theorem offMass_zero_of_head (ho : HasOrder A b p) {P : K[X]}
    (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (pay : (offKnots A).card+2≤p) (x : K) (hx : x∈offKnots A) : offMass A b x=0 := by
  let S := offKnots A
  let f : K→K := fun y=>if y=x then 1 else 0
  let Q := Lagrange.interpolate S id f
  have ev (y : K) (hy : y∈S) : Q.eval y=f y := Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have dQ : Q.natDegree<S.card := by
    by_cases z : Q=0
    · rw [z,natDegree_zero]
      exact Finset.card_pos.mpr ⟨x,hx⟩
    · exact (natDegree_lt_iff_degree_lt z).mpr (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
  have inF := band_le A Q.natDegree (band_iff.mpr ⟨Q,le_rfl,rfl⟩)
  change S.card+2≤p at pay
  have eqn : probe A b 0 (diag (g A) (evalNodes A Q))=0 :=
    probe_zeroSpace ho (by omega) inF
  have prod : probe A b 0 (diag (g A) (evalNodes A Q))=P.eval x*offMass A b x := by
    simp only [probe,row_apply,dotProduct,diag_apply,evalNodes_apply,offMass,Finset.mul_sum,pow_zero,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    by_cases z : g A i=0
    · simp [z]
    · have mi : nodes A i∈S := mem_offKnots.mpr ⟨i,z,rfl⟩
      rw [ev _ mi]
      by_cases atx : nodes A i=x
      · have u := fit i z
        rw [atx] at u
        simp [f,z,atx,u,mul_comm]
      · simp [f,z,atx]
  obtain ⟨i,ng,atx⟩ := mem_offKnots.mp hx
  have nz : P.eval x≠0 := by rwa [←atx,fit _ ng]
  exact (mul_eq_zero.mp (prod.symm.trans eqn)).resolve_left nz

/-- Any test function vanishing at the clean knots is killed at every
monomial probe after aggregate cancellation. No polynomial degree enters here. -/
theorem probe_zero_of_clean_roots
    (cancel : ∀ x∈offKnots A, offMass A b x=0)
    (P : K[X]) (roots : ∀x∈cleanKnots A, P.eval x=0) (k : ℕ) :
    probe A b k (evalNodes A P)=0 := by
  let T := offKnots A
  have split (i : Fin s) : b i * nodes A i^k * P.eval (nodes A i) =
      ∑ x∈T, (if g A i≠0 ∧ nodes A i=x then b i else 0) * (x^k*P.eval x) := by
    by_cases hi : g A i=0
    · have z := roots _ (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)
      simp [hi,z]
    · have hm : nodes A i∈T := mem_offKnots.mpr ⟨i,hi,rfl⟩
      rw [Finset.sum_eq_single (nodes A i)]
      · simp [hi,mul_assoc]
      · intro x _ hx; simp [Ne.symm hx]
      · intro h; exact (h hm).elim
  simp only [probe,row_apply,dotProduct,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => split i),Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x hx
  rw [←Finset.sum_mul]
  change offMass A b x*(x^k*P.eval x)=0
  rw [cancel x hx,zero_mul]

/-- A full square Cauchy system detects ordinary quadrature on the clean
support: its distinct-clock count exceeds q when order 2q+1 is paid. -/
theorem many_clean_of_cancel (ho : HasOrder A b p) (pay : 2*q+1≤p)
    (cancel : ∀x∈offKnots A,offMass A b x=0) : q < (cleanKnots A).card := by
  by_contra! few
  let S := cleanKnots A
  let P := RKCert.Endpoint.nodalHull S
  have hd : P.natDegree≤q := (RKCert.Endpoint.natDegree_nodalHull S).le.trans few
  let a : Fin (q+1)→K := fun i=>P.coeff i.val
  have hzero (i : Fin (q+1)) : (∑j : Fin (q+1), a j / ((i.val+j.val+1:ℕ):K))=0 := by
    have t := probe_zero_of_clean_roots cancel P
      (fun _ hx=>RKCert.Endpoint.nodalHull_eval_of_mem (S:=S) hx) i.val
    rw [evalNodes_eq_coeffEval A P hd,probe_coeffEval ho (by have := i.isLt; omega)] at t
    exact t
  have za := moments_detect ho (n:=q+1) (d:=1) (by decide) (by omega)
    (fun i j=>by have := i.isLt; have := j.isLt; omega) a hzero
  apply (RKCert.Endpoint.monic_nodalHull S).ne_zero
  ext k
  rw [coeff_zero]
  by_cases hk : k≤q
  · exact za ⟨k,Nat.lt_succ_of_le hk⟩
  · exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt (Nat.lt_of_not_ge hk))

/-- The support and quadrature conclusions for every ordered or unordered
characteristic-zero candidate with between three and seven distinct off knots. -/
theorem order9_multi_quadrature [CharZero K] (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b 9) (cap : s≤12)
    (enough : 3≤(offKnots A).card) (few : (offKnots A).card≤7) :
    (∀x∈offKnots A,offMass A b x=0) ∧ 5≤(cleanKnots A).card := by
  obtain ⟨_,_,_,_,_,fit⟩ := order9_two_curve_head ha ho cap enough
  have cancel := offMass_zero_of_head ho fit (by omega)
  exact ⟨cancel,many_clean_of_cancel ho (q:=4) (by decide) cancel⟩

end RKResearch.Certified.Graded.MultiOff
