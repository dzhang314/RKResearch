module
public import RKCert.Research.SDIRKSevenTailCollisionMoments
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-! The exact one-collision obstruction for a six-stage active tail.
The only geometric head hypothesis is that its three coordinate
columns are contained in the paid grade-four defect space. -/

namespace RKResearch.Certified.SDIRKSevenTailCollision
open RKResearch Graded
open scoped Matrix BigOperators Classical
noncomputable section

abbrev F := Fin 9
def tail : Finset F := Finset.univ.filter (fun i : F => 3 ≤ i.val)

theorem mem_tail {i : F} : i ∈ tail ↔ 3 ≤ i.val := by simp [tail]

structure SingleTwin (c : F → ℚ) where
  lo : F
  hi : F
  ht : lo ∈ tail
  lt : lo < hi
  same : c lo = c hi
  only : ∀ i j, i ∈ tail → j ∈ tail → c i = c j →
    i = j ∨ (i = lo ∧ j = hi) ∨ (i = hi ∧ j = lo)

namespace SingleTwin
variable {c : F → ℚ} (t : SingleTwin c)

theorem hi_mem : t.hi ∈ tail := by
  have h1 := mem_tail.mp t.ht
  have h2 : t.lo.val < t.hi.val := t.lt
  exact mem_tail.mpr (by omega)

theorem lo_ne_hi : t.lo ≠ t.hi := ne_of_lt t.lt

def sites : Finset ℚ := (tail.erase t.hi).image c

theorem card_sites : t.sites.card ≤ 5 := by
  have h6 : tail.card = 6 := by decide +kernel
  have er := Finset.card_erase_of_mem t.hi_mem
  have im : t.sites.card ≤ (tail.erase t.hi).card := Finset.card_image_le
  omega

theorem covers {i : F} (hi : i ∈ tail) : c i ∈ t.sites := by
  by_cases e : i = t.hi
  · exact Finset.mem_image.mpr ⟨t.lo, Finset.mem_erase.mpr ⟨t.lo_ne_hi,t.ht⟩,
      t.same.trans (congrArg c e).symm⟩
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨e,hi⟩,rfl⟩

theorem filtered_single {i : F} (hi : i ∈ tail) (hlo : i ≠ t.lo) (hhi : i ≠ t.hi) :
    tail.filter (fun j => c j = c i) = {i} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hj,e⟩
    rcases t.only j i hj hi e with h | h | h
    · exact h
    · exact False.elim (hhi h.2)
    · exact False.elim (hlo h.2)
  · rintro rfl
    exact ⟨hi,rfl⟩

theorem filtered_pair :
    tail.filter (fun j => c j = c t.lo) = {t.lo,t.hi} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hj,e⟩
    rcases t.only j t.lo hj t.ht e with h | h | h
    · exact Or.inl h
    · exact False.elim (t.lo_ne_hi h.2)
    · exact Or.inr h.1
  · rintro (rfl | rfl)
    · exact ⟨t.ht,rfl⟩
    · exact ⟨t.hi_mem,t.same.symm⟩

include t in
theorem row_zero {w : F → ℚ} {p : ℕ} (hp : 4 ≤ p)
    (hm : ∀ j ≤ p, (∑ i,w i*(c i)^j)=0) (hs : ∀ i, i ∉ tail → w i=0) (a : ℚ) :
    (∑ i ∈ tail.filter (fun i => c i=a), w i) = 0 := by
  have hsize : t.sites.card ≤ p+1 := t.card_sites.trans (by omega)
  have support (i) (h : w i ≠ 0) : c i ∈ t.sites := t.covers (by
    by_contra e
    exact h (hs i e))
  have e := fiber_zero hm t.sites hsize support a
  rw [← e]
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact hi.2
  · intro i hi hnot
    apply hs
    intro ih
    apply hnot
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact ⟨ih,hi⟩

theorem singleton_zero {w : F → ℚ} {p : ℕ} (hp : 4 ≤ p)
    (hm : ∀ j ≤ p, (∑ i,w i*(c i)^j)=0) (hs : ∀ i, i ∉ tail → w i=0) {i : F}
    (hi : i ∈ tail) (hlo : i ≠ t.lo) (hhi : i ≠ t.hi) : w i = 0 := by
  simpa only [t.filtered_single hi hlo hhi,Finset.sum_singleton] using t.row_zero hp hm hs (c i)

theorem pair_zero {w : F → ℚ} {p : ℕ} (hp : 4 ≤ p)
    (hm : ∀ j ≤ p, (∑ i,w i*(c i)^j)=0) (hs : ∀ i, i ∉ tail → w i=0) :
    w t.lo + w t.hi = 0 := by
  simpa only [t.filtered_pair,Finset.sum_pair t.lo_ne_hi] using t.row_zero hp hm hs (c t.lo)

end SingleTwin

def HeadPaid (A : Matrix F F ℚ) : Prop :=
  ∀ i, i ∉ tail → Pi.single i (1:ℚ) ∈ zeroSpace A 4

theorem head_rows {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) {i : F} (hi : i ∉ tail) :
      b i = 0 ∧ firstRow A b i = 0 ∧ secondRow A b i = 0 := by
  have e := head i hi
  have ae := mat_zeroSpace_charZero A 4 e
  have b0 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) e)
  have a0 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) ae)
  have a1 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 1) (by decide) ae)
  simp only [row_apply,pow_zero,mul_one] at b0 a0
  simp only [row_apply,pow_one] at a1
  change (b ⬝ᵥ (A *ᵥ Pi.single i 1)) = 0 at a0
  change ((b*x A) ⬝ᵥ (A *ᵥ Pi.single i 1)) = 0 at a1
  rw [Matrix.dotProduct_mulVec] at a0 a1
  refine ⟨?_,?_,?_⟩
  · simpa [dotProduct,Pi.single_apply] using b0
  · simpa [dotProduct,Pi.single_apply] using a0
  · simpa [dotProduct,Pi.single_apply] using a1

private theorem first_head {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) (i : F) (hi : i ∉ tail) :
    firstError A b i = 0 := by
  obtain ⟨h,hh,_⟩ := head_rows ho head hi
  change firstRow A b i - b i * (1-x A i)=0
  rw [h,hh,zero_mul,sub_zero]

private theorem second_head {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) (i : F) (hi : i ∉ tail) :
    secondError A b i = 0 := by
  obtain ⟨h,_,hh⟩ := head_rows ho head hi
  change secondRow A b i - b i * ((1-(x A i)^2)/2)=0
  rw [h,hh,zero_mul,sub_zero]

private theorem contrast_row {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) (t : SingleTwin (x A)) :
    firstError A b = Pi.single t.lo (firstError A b t.lo) +
      Pi.single t.hi (-firstError A b t.lo) := by
  have hHi := t.pair_zero (p := 5) (by decide) (firstError_moments ho) (first_head ho head)
  funext i
  by_cases il : i = t.lo
  · subst i
    simp [t.lo_ne_hi]
  · by_cases ih : i = t.hi
    · subst i
      simp only [Pi.add_apply, Pi.single_eq_of_ne il, Pi.single_eq_same, zero_add]
      linear_combination hHi
    · simp [il,ih]
      by_cases it : i ∈ tail
      · exact t.singleton_zero (p := 5) (by decide) (firstError_moments ho) (first_head ho head) it il ih
      · exact first_head ho head i it

private theorem pure_twins {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) (t : SingleTwin (x A))
    (hW : firstError A b t.lo ≠ 0) {v : F → ℚ} (hv : v ∈ zeroSpace A 5) :
    v t.lo = v t.hi := by
  have h := firstError_annihilates ho hv
  rw [contrast_row ho head t,add_dotProduct] at h
  simp only [dotProduct,Pi.single_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  have e : (firstError A b t.lo)*(v t.lo-v t.hi)=0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hW)

private theorem twin_difference_row_moments {A : Matrix F F ℚ} {b : F → ℚ}
    (ho : HasOrder 7 A b) (head : HeadPaid A) (t : SingleTwin (x A))
    (hW : firstError A b t.lo ≠ 0) :
    (∀ i, i ∉ tail → A t.hi i-A t.lo i=0) ∧
      ∀ j ≤ 4, (∑ i, (A t.hi i-A t.lo i)*(x A i)^j)=0 := by
  constructor
  · intro i hi
    have h := pure_twins ho head t hW (mat_zeroSpace_charZero A 4 (head i hi))
    simpa [mat_apply,Matrix.mulVec,dotProduct,Pi.single_apply,sub_eq_zero] using h.symm
  · intro j hj
    have m := pure_twins ho head t hW
      (zeroSpace_mono A (by omega : j+1≤5) (monomialStageDefect_mem A j))
    change ((j+1 : ℕ):ℚ)*((A *ᵥ fun i => (x A i)^j) t.lo) -
      (x A t.lo)^(j+1) =
      ((j+1 : ℕ):ℚ)*((A *ᵥ fun i => (x A i)^j) t.hi) -
      (x A t.hi)^(j+1) at m
    rw [t.same] at m
    change ((j+1 : ℕ):ℚ)*(∑ i,A t.lo i*(x A i)^j) - (x A t.hi)^(j+1) =
      ((j+1 : ℕ):ℚ)*(∑ i,A t.hi i*(x A i)^j) - (x A t.hi)^(j+1) at m
    simp only [sub_mul,Finset.sum_sub_distrib]
    have neq : ((j+1 : ℕ):ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply mul_left_cancel₀ neq
    rw [mul_zero]
    linear_combination -m

private theorem column8 {A : Matrix F F ℚ} {γ : ℚ} (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i=γ) (w : F → ℚ) : (w ᵥ* A) 8 = w 8*γ := by
  change (∑ i,w i*A i 8)=_
  rw [Finset.sum_eq_single (8:F),he]
  · intro i hi hne
    have non : i.val ≠ 8 := fun h => hne (Fin.ext h)
    have iLt := i.isLt
    have i8 : i < (8 : F) := by change i.val < 8; omega
    have vz : A i 8 = 0 := ha i8
    rw [vz,mul_zero]
  · simp

private theorem column7 {A : Matrix F F ℚ} {γ : ℚ} (ha : A.IsLowerTriangular)
    (he : ∀ i, A i i=γ) (w : F → ℚ) : (w ᵥ* A) 7 = w 7*γ + w 8*A 8 7 := by
  change (∑ i,w i*A i 7)=_
  calc
    _ = ∑ i ∈ ({7,8}:Finset F),w i*A i 7 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hin
      have h7 : i.val ≠ 7 := fun e => hin (by have e7 : i = (7:F) := Fin.ext e; simp [e7])
      have h8 : i.val ≠ 8 := fun e => hin (by have e8 : i = (8:F) := Fin.ext e; simp [e8])
      have hn := i.isLt
      have i7 : i < (7 : F) := by change i.val<7; omega
      have vz : A i 7 = 0 := ha i7
      rw [vz,mul_zero]
    _ = _ := by rw [Finset.sum_pair (by decide : (7:F)≠8),he]

private theorem no_one_output {γ c w : ℚ} (hg : γ ≠ 0) (hw : w ≠ 0)
    (h₀ : w*γ = w*(1-c)) (h₁ : w*c*γ = w*((1-c^2)/2)) : False := by
  have e₀ := mul_left_cancel₀ hw h₀
  have e₁ : c*γ=(1-c^2)/2 := mul_left_cancel₀ hw (by simpa only [mul_assoc] using h₁)
  have ez : γ^2=0 := by linear_combination -2*e₁ + (γ+1+c)*e₀
  exact (pow_ne_zero 2 hg) ez

private theorem sqrt2_absent : ¬ IsSquare (2:ℚ) := by
  rw [← Nat.cast_ofNat (R:=ℚ),Rat.isSquare_natCast_iff]
  rintro ⟨v,hv⟩
  have h := congrArg Nat.sqrt hv
  rw [Nat.sqrt_eq,show Nat.sqrt 2=1 by decide +kernel] at h
  rw [← h] at hv
  omega

private theorem no_penultimate_clock {γ c d w s a : ℚ} (hg : γ≠0) (hw : w≠0)
    (edge : γ=1-d) (h₀ : w*γ+s*a=w*(1-c))
    (h₁ : w*c*γ+s*d*a=w*((1-c^2)/2)) : False := by
  have e : (1-c-2*γ)^2 = 2*γ^2 := by
    have tap : c*γ+d*(1-c-γ)=(1-c^2)/2 := by
      apply mul_left_cancel₀ hw
      linear_combination h₁ - d*h₀
    linear_combination 2*tap - 2*(1-c-γ)*edge
  apply sqrt2_absent
  refine ⟨(1-c-2*γ)/γ,?_⟩
  field_simp
  linear_combination -e

private theorem row_pair_no_tap {A : Matrix F F ℚ} {b : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (hA : A.IsLowerTriangular) (hd : ∀ i,A i i=γ)
    (head : HeadPaid A) (t : SingleTwin (x A)) (tl : t.hi=8)
    (hW : firstError A b t.lo≠0) : A 8 7 = 0 := by
  obtain ⟨hh,hm⟩ := twin_difference_row_moments ho head t hW
  let w : F → ℚ := fun i => A t.hi i-A t.lo i
  by_cases e : t.lo=7
  · have q := t.pair_zero (w := w) (p := 4) (by decide) hm hh
    change (A t.hi t.lo-A t.lo t.lo)+(A t.hi t.hi-A t.lo t.hi)=0 at q
    have a78 : A 7 8=0 := hA (by decide : (7:F)<8)
    rw [tl,e,hd,hd,a78,sub_zero] at q
    linear_combination q
  · have q := t.singleton_zero (w := w) (p := 4) (by decide) hm hh
      (i := 7) (by decide) (Ne.symm e) (by rw [tl]; decide)
    change A t.hi 7-A t.lo 7=0 at q
    have lhi := show t.lo.val < t.hi.val from t.lt
    rw [tl] at lhi
    change t.lo.val < 8 at lhi
    have bne : t.lo.val ≠ 7 := fun eq => e (Fin.ext eq)
    have l7 : t.lo < (7 : F) := by change t.lo.val<7; omega
    have a07 : A t.lo 7=0 := hA l7
    rwa [tl,a07,sub_zero] at q

/-- Exact exclusion of a single active-tail collision for a nine-stage
strict order-seven method with its head paid by grade four. This is not
a global exclusion of rational nine-stage tableaux. The nonzero terminal
masses are automatic in the all-active chart once the five-site floor
has been applied. -/
theorem no_single_twin {A : Matrix F F ℚ} {b : F → ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hg : γ≠0)
    (head : HeadPaid A) (h7 : b 7≠0) (h8 : b 8≠0)
    (t : SingleTwin (x A)) (hab : t.lo=7 → t.hi=8 → b 7+b 8≠0) : False := by
  have g₀ (i) (hi : i ∈ tail) (h1 : i≠t.lo) (h2 : i≠t.hi) :
      firstRow A b i=firstTarget A b i := sub_eq_zero.mp
    (t.singleton_zero (p := 5) (by decide) (firstError_moments ho) (first_head ho head) hi h1 h2)
  have g₁ (i) (hi : i ∈ tail) (h1 : i≠t.lo) (h2 : i≠t.hi) :
      secondRow A b i=secondTarget A b i := sub_eq_zero.mp
    (t.singleton_zero (p := 4) (by decide) (secondError_moments ho) (second_head ho head) hi h1 h2)
  have eq8 : firstRow A b 8=b 8*γ := column8 ha he b
  have er8 := column8 ha he (b*x A)
  have eq7 : firstRow A b 7=b 7*γ+b 8*A 8 7 := column7 ha he b
  have er7 := column7 ha he (b*x A)
  change secondRow A b 8 = b 8*x A 8*γ at er8
  change secondRow A b 7 = b 7*x A 7*γ+b 8*x A 8*A 8 7 at er7
  by_cases ht : t.hi = 8
  · have post_tap (tap : A 8 7=0) : False := by
      by_cases ht' : t.lo=7
      · have xs : x A 7=x A 8 := by simpa only [ht,ht'] using t.same
        have p0 := t.pair_zero (p := 5) (by decide) (firstError_moments ho) (first_head ho head)
        have p1 := t.pair_zero (p := 4) (by decide) (secondError_moments ho) (second_head ho head)
        rw [ht,ht'] at p0 p1
        change (firstRow A b 7-b 7*(1-x A 7))+(firstRow A b 8-b 8*(1-x A 8))=0 at p0
        change (secondRow A b 7-b 7*((1-(x A 7)^2)/2))+(secondRow A b 8-b 8*((1-(x A 8)^2)/2))=0 at p1
        simp only [eq7,eq8,tap,mul_zero,add_zero,xs] at p0
        simp only [er7,er8,tap,mul_zero,add_zero,xs] at p1
        exact no_one_output (c:=x A 8) hg (hab ht' ht) (by linear_combination p0) (by linear_combination p1)
      · have p0 := g₀ 7 (by decide) (Ne.symm ht') (by rw [ht]; decide)
        have p1 := g₁ 7 (by decide) (Ne.symm ht') (by rw [ht]; decide)
        rw [eq7,tap,mul_zero,add_zero] at p0
        rw [er7,tap,mul_zero,add_zero] at p1
        exact no_one_output hg h7 p0 p1
    by_cases hW : firstError A b t.lo=0
    · have hz (i : F) : firstRow A b i = firstTarget A b i := by
        have zz := congrFun (contrast_row ho head t) i
        rw [hW,neg_zero,Pi.single_zero,Pi.single_zero,add_zero] at zz
        exact sub_eq_zero.mp zz
      have last := hz 8
      rw [eq8] at last
      have l : γ=1-x A 8 := mul_left_cancel₀ h8 last
      by_cases ht' : t.lo=7
      · have xs : x A 7=x A 8 := by simpa only [ht,ht'] using t.same
        have p := hz 7
        rw [eq7] at p
        change b 7*γ+b 8*A 8 7=b 7*(1-x A 7) at p
        rw [xs,← l] at p
        apply post_tap
        apply mul_left_cancel₀ h8
        linear_combination p
      · have h₀ := hz 7
        have h₁ := g₁ 7 (by decide) (Ne.symm ht') (by rw [ht]; decide)
        rw [eq7] at h₀
        rw [er7] at h₁
        exact no_penultimate_clock hg h7 l h₀ h₁
    · exact post_tap (row_pair_no_tap ho ha he head t ht hW)
  · have h0 : (8:F)≠t.lo := by
      intro e
      have l : (8:F)<t.hi := e ▸ t.lt
      have hlt := t.hi.isLt
      change 8<t.hi.val at l
      omega
    have p0 := g₀ 8 (by decide) h0 (Ne.symm ht)
    have p1 := g₁ 8 (by decide) h0 (Ne.symm ht)
    rw [eq8] at p0
    rw [er8] at p1
    exact no_one_output hg h8 p0 p1

end
end RKResearch.Certified.SDIRKSevenTailCollision
