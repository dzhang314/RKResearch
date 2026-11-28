module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderSlots

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

def rawMoment (y h v : Site→R) (n : ℕ) : R :=
  ∑ i : Site,h i*(y i)^n*v i

theorem rawMoment_zero (y h : Site→R) (n : ℕ) : rawMoment y h 0 n=0 := by
  simp [rawMoment]

theorem rawMoment_add (y h v z : Site→R) (n : ℕ) :
    rawMoment y h (v+z) n=rawMoment y h v n+rawMoment y h z n := by
  simp [rawMoment, mul_add, Finset.sum_add_distrib]

theorem rawMoment_scale (y h v : Site→R) (s : R) (n : ℕ) :
    rawMoment y h (fun i=>s*v i) n=s*rawMoment y h v n := by
  unfold rawMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rawMoment_one_minus (y h v : Site→R) (n : ℕ) :
    rawMoment y h (fun i=>(1-y i)*v i) n=rawMoment y h v n-rawMoment y h v (n+1) := by
  unfold rawMoment
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- The literal two primitive moment groups, avoiding natural subtraction
in the low grades. No independence hypothesis is part of this definition. -/
def rawAnn (c a b : R) (j : ℕ) (v : Site→R) : Prop :=
  (∀ n ≤ j, rawMoment (rawY c a b) (rawW c a b) v n=0) ∧
  (∀ n, n+2 ≤ j → rawMoment (rawY c a b) (rawU c a b) v n=0)

def rawLine (c a b : R) (v : Site→R) : Prop :=
  ∃ μ : R, v=fun i=> μ*rawEta c a b i

theorem rawAnn_mono (c a b : R) {j k : ℕ} {v : Site→R} (hj : j≤k)
    (h : rawAnn c a b k v) : rawAnn c a b j v :=
  ⟨fun n hn => h.1 n (hn.trans hj),fun n hn => h.2 n (hn.trans hj)⟩

theorem rawAnn_zero (c a b : R) (j : ℕ) : rawAnn c a b j 0 :=
  ⟨fun n _ => rawMoment_zero _ _ n,fun n _ => rawMoment_zero _ _ n⟩

theorem rawAnn_add (c a b : R) {j : ℕ} {v z : Site→R}
    (hv : rawAnn c a b j v) (hz : rawAnn c a b j z) : rawAnn c a b j (v+z) := by
  constructor
  · intro n hn
    rw [rawMoment_add,hv.1 n hn,hz.1 n hn,zero_add]
  · intro n hn
    rw [rawMoment_add,hv.2 n hn,hz.2 n hn,zero_add]

theorem rawAnn_scale (c a b : R) {j : ℕ} {v : Site→R}
    (s : R) (hv : rawAnn c a b j v) : rawAnn c a b j (fun i=>s*v i) := by
  constructor
  · intro n hn
    rw [rawMoment_scale,hv.1 n hn,mul_zero]
  · intro n hn
    rw [rawMoment_scale,hv.2 n hn,mul_zero]

theorem rawAnn_mark (c a b : R) {j : ℕ} {v : Site→R}
    (h : rawAnn c a b (j+1) v) : rawAnn c a b j (fun i=>rawClock c a b i*v i) := by
  constructor
  · intro n hn
    have h0 := h.1 n (by omega)
    have h1 := h.1 (n+1) (by omega)
    simp only [rawClock,rawMoment_one_minus]
    rw [h0,h1,sub_self]
  · intro n hn
    have h0 := h.2 n (by omega)
    have h1 := h.2 (n+1) (by omega)
    simp only [rawClock,rawMoment_one_minus]
    rw [h0,h1,sub_self]

theorem rawAnn_markPow (c a b : R) (j n : ℕ) (v : Site→R)
    (h : rawAnn c a b (j+n) v) : rawAnn c a b j (fun i=> (rawClock c a b i)^n*v i) := by
  induction n generalizing v with
  | zero => simpa only [Nat.add_zero,pow_zero,one_mul] using h
  | succ n ih =>
    have hs : rawAnn c a b (j+n+1) v := h
    have hm := rawAnn_mark c a b hs
    have hh := ih (fun i=>rawClock c a b i*v i) hm
    simpa only [pow_succ,mul_assoc] using hh

theorem rawMoment_contact (y w u eta v : Site→R) (A B C : R)
    (H : ∀ i, w i*eta i=(A*(y i)^2+B*y i+C)*u i) (n : ℕ) :
    rawMoment y w (fun i=>eta i*v i) n =
      A*rawMoment y u v (n+2)+B*rawMoment y u v (n+1)+C*rawMoment y u v n := by
  unfold rawMoment
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ((w i*eta i)*v i)*(y i)^n := by ring
    _ = _ := by rw [H i,pow_add,pow_add,pow_one];ring

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actual_etaAnn5 : rawAnn c a b 5 (rawEta c a b) := by
  constructor
  · intro n hn
    calc
      _ = ∑ i : Site,(rawY c a b i)^n*(rawW c a b i*rawEta c a b i) := by
        apply Finset.sum_congr rfl;intro i _;ring
      _ = _ := raw_weighted_eta ρ c a b hp hc ha hb hRoot hOther n hn
  · intro n hn
    calc
      _ = ∑ i : Site,(rawY c a b i)^n*(rawEta c a b i*rawU c a b i) := by
        apply Finset.sum_congr rfl;intro i _;ring
      _ = _ := raw_mixed_eta_u ρ c a b hp hc ha hb n (by omega)

theorem actual_contact_degree2 :
    ∃ A B C : R,∀ i : Site,rawW c a b i*rawEta c a b i =
      (A*(rawY c a b i)^2+B*rawY c a b i+C)*rawU c a b i := by
  let S := (actualScale (nodal c a b))⁻¹ʳ
  refine ⟨S*phaseSlope c,S*(phaseIntercept c-15*phaseSlope c),-S*15*phaseIntercept c,?_⟩
  intro i
  rw [raw_contact ρ c a b hp hc ha hb hRoot hOther]
  simp only [actualQ,normQuad,eval_mul,eval_C,eval_sub,eval_X,actualQ1_eval]
  unfold S
  ring

theorem actual_lineAnn5 {v : Site→R} (h : rawLine c a b v) : rawAnn c a b 5 v := by
  obtain ⟨μ,rfl⟩ := h
  exact rawAnn_scale c a b μ (actual_etaAnn5 ρ c a b hp hc ha hb hRoot hOther)

/-- The nonlinear size-nine product. Both nominal marks (degrees 0 and 1)
are paid by actual quadratic contact and actual mixed eta-u moments. -/
theorem actual_line_product {v z : Site→R}
    (hv : rawLine c a b v) (hz : rawLine c a b z) :
    rawAnn c a b 1 (v*z) := by
  obtain ⟨μ,rfl⟩ := hv
  obtain ⟨ν,rfl⟩ := hz
  have hE : rawAnn c a b 1 (fun i=>rawEta c a b i*rawEta c a b i) := by
    constructor
    · intro n hn
      obtain ⟨A,B,C,H⟩ := actual_contact_degree2 ρ c a b hp hc ha hb hRoot hOther
      have h := (actual_etaAnn5 ρ c a b hp hc ha hb hRoot hOther).2
      rw [rawMoment_contact _ _ _ _ _ A B C H n,
        h (n+2) (by omega),h (n+1) (by omega),h n (by omega)]
      ring
    · intro n hn
      omega
  have hV := rawAnn_scale c a b (μ*ν) hE
  have he : (fun i=>μ*rawEta c a b i)*(fun i=>ν*rawEta c a b i) =
      fun i=> (μ*ν)*(rawEta c a b i*rawEta c a b i) := by
    funext i
    simp only [Pi.mul_apply]
    ring
  rw [he]
  exact hV

/-- The nonlinear size-ten product. The source annulator uses the three
actual u-marks and does not invert the score at any stage. -/
theorem actual_line_ann_product {v z : Site→R}
    (hv : rawLine c a b v) (hz : rawAnn c a b 4 z) :
    rawAnn c a b 0 (v*z) := by
  obtain ⟨μ,rfl⟩ := hv
  have hE : rawAnn c a b 0 (fun i=>rawEta c a b i*z i) := by
    constructor
    · intro n hn
      obtain ⟨A,B,C,H⟩ := actual_contact_degree2 ρ c a b hp hc ha hb hRoot hOther
      rw [rawMoment_contact _ _ _ _ _ A B C H n,
        hz.2 (n+2) (by omega),hz.2 (n+1) (by omega),hz.2 n (by omega)]
      ring
    · intro n hn
      omega
  have hV := rawAnn_scale c a b μ hE
  have he : (fun i=>μ*rawEta c a b i)*z=fun i=>μ*(rawEta c a b i*z i) := by
    funext i
    simp only [Pi.mul_apply,mul_assoc]
  rw [he]
  exact hV

theorem actual_ann_line_product {v z : Site→R}
    (hv : rawAnn c a b 4 v) (hz : rawLine c a b z) :
    rawAnn c a b 0 (v*z) := by
  rw [mul_comm]
  exact actual_line_ann_product ρ c a b hp hc ha hb hRoot hOther hz hv

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.rawAnn_markPow
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_lineAnn5
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_line_product
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_line_ann_product
