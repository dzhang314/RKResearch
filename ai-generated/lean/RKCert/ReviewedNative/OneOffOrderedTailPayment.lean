module
public import RKCert.ReviewedNative.OneOffTailCurve
public import RKCert.ReviewedNative.ReflectedPolynomialBudget
public import RKCert.ERKOrderNineOneOffTailCubic

@[expose] public section

/-! # Native reflected tail payment with scalar certificates reused

Only the ordered scalar mass/Hankel tests and the scalar collision from
the existing certificate are used here. No reviewed tableau is translated
to another tree or order predicate. -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Module Polynomial
open scoped Matrix Classical

variable {K : Type*} [Field K] {A : Matrix (Fin 12) (Fin 12) K} {b f : Fin 12 → K}

private theorem beta_primitive_eq_native (P : K[X]) :
    RKCert.Paired.primitive P = primitive P := by
  ext n
  cases n with
  | zero => rw [RKCert.Paired.primitive_coeff_zero,primitive_coeff_zero]
  | succ n =>
    rw [RKCert.Paired.primitive_coeff_succ, primitive_coeff_succ]

abbrev tailMoment (A : Matrix (Fin 12) (Fin 12) K) (b : Fin 12 → K) (k : ℕ)
    (v : Fin 12 → K) : K := reflectedProbe A b 0 k v

theorem tailMoment_clock (A : Matrix (Fin 12) (Fin 12) K) (b v : Fin 12 → K)
    (k : ℕ) (η : K) :
    tailMoment A b k (diag (nodes A) v-η • v) =
      (1-η)*tailMoment A b k v-tailMoment A b (k+1) v := by
  simp only [tailMoment,reflectedProbe,row_apply,dotProduct,pow_zero,mul_one,
    diag_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,←Finset.sum_sub_distrib,pow_succ,reflectedClock,Pi.one_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tailMoment_terminal (one : nodes A (Fin.last 11)=1) (k : ℕ) (pos : k≠0) :
    tailMoment A b k (Reverse.coordinate (Fin.last 11))=0 := by
  change row _ (Reverse.coordinate (Fin.last 11))=0
  rw [Reverse.row_coordinate]
  have hz : reflectedClock A (Fin.last 11)=0 := by
    change (1:K)-nodes A (Fin.last 11)=0
    rw [one,sub_self]
  change b (Fin.last 11) * (nodes A (Fin.last 11))^0 * (reflectedClock A (Fin.last 11))^k=0
  rw [hz,zero_pow pos,mul_zero]

/-- Reflected moments pay a physical shifted-clock action at its exact
grade budget. The live coordinate at clock one contributes zero. -/
theorem tail_paid_step (ho : HasOrder 9 A b) {v : Fin 12 → K} {q k : ℕ}
    (hv : v∈treeSpace A q) (one : nodes A (Fin.last 11)=1)
    (ord : q+k+2≤9) (pos : k≠0) {η κ τ : K}
    (act : mat A v=κ • (diag (nodes A) v-η • v)+τ • Reverse.coordinate (Fin.last 11)) :
    tailMoment A b (k+1) v=((k+1:ℕ):K)*κ*tailMoment A b k (diag (nodes A) v-η • v) := by
  have e := LinearMap.mem_ker.mp (reflectedStageRow_treeSpace ho q k ord hv)
  have term : reflectedProbe A b 0 k (Reverse.coordinate (Fin.last 11))=0 :=
    tailMoment_terminal (b:=b) one k pos
  rw [reflectedStageRow_pair,act,map_add,map_smul,map_smul,term,
    smul_zero,add_zero,smul_eq_mul,sub_eq_zero] at e
  simpa only [tailMoment,mul_assoc] using e.symm

theorem tail_paid_recurrence (ho : HasOrder 9 A b) {v : Fin 12 → K} {q k : ℕ}
    (hv : v∈treeSpace A q) (one : nodes A (Fin.last 11)=1)
    (ord : q+k+2≤9) (pos : k≠0) {η κ τ : K}
    (act : mat A v=κ • (diag (nodes A) v-η • v)+τ • Reverse.coordinate (Fin.last 11)) :
    (1+((k+1:ℕ):K)*κ)*tailMoment A b (k+1) v =
      ((k+1:ℕ):K)*κ*(1-η)*tailMoment A b k v := by
  have e := tail_paid_step ho hv one ord pos act
  rw [tailMoment_clock] at e
  linear_combination e

theorem tail_hankel_collision [CharZero K] (ho : HasOrder 9 A b)
    (hf : f∈treeSpace A 4) (one : nodes A (Fin.last 11)=1) {η u κ lam τ τ' : K}
    (hu : u≠η)
    (fA : mat A f=κ • (diag (nodes A) f-η • f)+τ • Reverse.coordinate (Fin.last 11))
    (wA : let w := diag (nodes A) f-η • f
      mat A w=lam • (diag (nodes A) w-u • w)+τ' • Reverse.coordinate (Fin.last 11)) :
    tailMoment A b 2 f*tailMoment A b 4 f-(tailMoment A b 3 f)^2=0 := by
  let w := diag (nodes A) f-η • f
  let μ (k : ℕ) := tailMoment A b k f
  let ν (k : ℕ) := tailMoment A b k w
  have hw : w∈treeSpace A 5 := (treeSpace A 5).sub_mem (diag_treeSpace A 4 hf)
    ((treeSpace A 5).smul_mem _ (treeSpace_mono A (by decide) hf))
  have f1 : μ 2=2*κ*ν 1 := by
    simpa only [w,μ,ν,Nat.reduceAdd,Nat.cast_ofNat] using
      tail_paid_step ho hf one (k:=1) (by decide) (by decide) fA
  have f2 : μ 3=3*κ*ν 2 := by
    simpa only [w,μ,ν,Nat.reduceAdd,Nat.cast_ofNat] using
      tail_paid_step ho hf one (k:=2) (by decide) (by decide) fA
  have f3 : μ 4=4*κ*ν 3 := by
    simpa only [w,μ,ν,Nat.reduceAdd,Nat.cast_ofNat] using
      tail_paid_step ho hf one (k:=3) (by decide) (by decide) fA
  have g1 : (1+2*lam)*ν 2=2*lam*(1-u)*ν 1 := by
    simpa only [ν,Nat.reduceAdd,Nat.cast_ofNat] using
      tail_paid_recurrence ho hw one (k:=1) (by decide) (by decide) wA
  have g2 : (1+3*lam)*ν 3=3*lam*(1-u)*ν 2 := by
    simpa only [ν,Nat.reduceAdd,Nat.cast_ofNat] using
      tail_paid_recurrence ho hw one (k:=2) (by decide) (by decide) wA
  have f2' : (1+3*κ)*μ 3=3*κ*(1-η)*μ 2 := by
    simpa only [μ,Nat.reduceAdd,Nat.cast_ofNat] using tail_paid_recurrence ho hf one (k:=2) (by decide) (by decide) fA
  have f3' : (1+4*κ)*μ 4=4*κ*(1-η)*μ 3 := by
    simpa only [μ,Nat.reduceAdd,Nat.cast_ofNat] using tail_paid_recurrence ho hf one (k:=3) (by decide) (by decide) fA
  have g1' : (1+2*lam)*μ 3=3*lam*(1-u)*μ 2 := by
    linear_combination (1+2*lam)*f2-3*lam*(1-u)*f1+3*κ*g1
  have g2' : (1+3*lam)*μ 4=4*lam*(1-u)*μ 3 := by
    linear_combination (1+3*lam)*f3-4*lam*(1-u)*f2+4*κ*g2
  exact RKCert.Paired.reflected_collision_scalar κ lam η u (μ 2) (μ 3) (μ 4) f2' f3' g1' g2' hu

theorem one_off_reflected_beta (ho : HasOrder 9 A b) {d t z : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (j : ℕ) (budget : j≤3) :
    tailMoment A b (j+1) f =
      RKCert.OrderedGram.betaIntegral ((1-X)^j*((X-C d)*fibrePoly t z)) := by
  have h := reflectedProbe_primitive_of_defect ho 0 (j+1) (by omega)
    (tailPolynomial_degree d t z).le hf
  rw [pow_zero,one_mul] at h
  rw [tailMoment,h,RKCert.OrderedGram.betaIntegral_apply,beta_primitive_eq_native]
  congr 2
  rw [tailPolynomial,pow_succ]
  ring

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem tail_cubic_impossible (ho : HasOrder 9 A b) {d t z η κ τ : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (one : nodes A (Fin.last 11)=1) (zt : z≠t)
    (ht : (lobattoCubic : K[X]).eval t=0) (hz : (lobattoCubic : K[X]).eval z=0)
    (hd : (lobattoCubic : K[X]).eval d≠0) (h1 : (lobattoCubic : K[X]).eval 1≠0)
    (fA : mat A f=κ • (diag (nodes A) f-η • f)+τ • Reverse.coordinate (Fin.last 11)) :
    False := by
  have fm : f∈treeSpace A 4 := by
    simpa only [sub_add_cancel] using (treeSpace A 4).add_mem (zeroSpace_le_treeSpace A 4 hf)
      (evalNodes_mem_treeSpace A _ (tailPolynomial_degree d t z).le)
  obtain ⟨r,m,rn,mn,mass⟩ := RKCert.Paired.OneOff.cubic_tail_mass zt ht hz hd h1
  have moments (j : ℕ) (h : j≤2) : tailMoment A b (j+1) f=(1-r)^j*m := by
    rw [one_off_reflected_beta ho hf j (by omega)]
    exact mass j h
  have e1 := tail_paid_recurrence ho fm one (k:=1) (by decide) (by decide) fA
  have e2 := tail_paid_recurrence ho fm one (k:=2) (by decide) (by decide) fA
  rw [moments 0 (by decide),moments 1 (by decide)] at e1
  rw [moments 1 (by decide),moments 2 (by decide)] at e2
  norm_num at e1 e2
  have s1 : (1+2*κ)*(1-r)=2*κ*(1-η) := by
    apply mul_right_cancel₀ mn
    linear_combination e1
  have s2 : (1+3*κ)*(1-r)=3*κ*(1-η) := by
    apply mul_right_cancel₀ (mul_ne_zero (sub_ne_zero.mpr rn.symm) mn)
    linear_combination e2
  exact rn (by linear_combination -3*s1+2*s2)

theorem tail_quartic_impossible (ho : HasOrder 9 A b) {d t z l η u κ lam τ τ' : K}
    (hf : f-evalNodes A (tailPolynomial d t z)∈zeroSpace A 4)
    (one : nodes A (Fin.last 11)=1) (un : u≠η) (zt : z≠t)
    (ht : (lobattoPencil l).eval t=0) (hz : (lobattoPencil l).eval z=0)
    (hd : (lobattoPencil l).eval d≠0) (h1 : (lobattoPencil l).eval 1≠0)
    (fA : mat A f=κ • (diag (nodes A) f-η • f)+τ • Reverse.coordinate (Fin.last 11))
    (wA : let w := diag (nodes A) f-η • f
      mat A w=lam • (diag (nodes A) w-u • w)+τ' • Reverse.coordinate (Fin.last 11)) :
    False := by
  have fm : f∈treeSpace A 4 := by
    simpa only [sub_add_cancel] using (treeSpace A 4).add_mem (zeroSpace_le_treeSpace A 4 hf)
      (evalNodes_mem_treeSpace A _ (tailPolynomial_degree d t z).le)
  have C := tail_hankel_collision ho fm one un fA wA
  rw [one_off_reflected_beta ho hf 1 (by decide),one_off_reflected_beta ho hf 2 (by decide),
    one_off_reflected_beta ho hf 3 (by decide)] at C
  exact (RKCert.Paired.OneOff.four_root_tail_hankel zt ht hz hd h1) C

end RKResearch.Certified.Graded.OneOff.Seven
