module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHost

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear
open scoped BigOperators Ring

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

/-- Polynomial readout on quadratic model coordinates, with denominator
units supplied by the actual host certificate. -/
structure Quad (R : Type*) where
  c0 : R
  c1 : R
  c2 : R

def Quad.eval (q : Quad R) (x : R) : R := q.c0+q.c1*x+q.c2*x^2
def Quad.primitive (q : Quad R) (x : R) : R :=
  q.c0*x+q.c1*x^2*(2:R)⁻¹ʳ+q.c2*x^3*(3:R)⁻¹ʳ

def HostInput.decode (p : HostInput R) (v0 d vr : R) : Quad R :=
  let A:=p.q-p.α*p.s
  let B:=p.q^2-p.α*p.s^2
  let γ:=d-(1-p.α)*v0
  let ε:=vr-v0
  ⟨v0,(γ*p.r^2-B*ε)*p.decodeDen⁻¹ʳ,(A*ε-p.r*γ)*p.decodeDen⁻¹ʳ⟩

theorem HostInput.decode_reads (p : HostInput R) (hu : IsUnit p.decodeDen) (v0 d vr : R) :
    (p.decode v0 d vr).eval 0=v0 ∧
    (p.decode v0 d vr).eval p.q-p.α*(p.decode v0 d vr).eval p.s=d ∧
    (p.decode v0 d vr).eval p.r=vr := by
  let A:=p.q-p.α*p.s
  let B:=p.q^2-p.α*p.s^2
  let γ:=d-(1-p.α)*v0
  let ε:=vr-v0
  let Q:=p.decode v0 d vr
  have hD : A*p.r^2-B*p.r=p.decodeDen := rfl
  have h0 : Q.c0=v0 := rfl
  have h1 : A*Q.c1+B*Q.c2=γ := by
    calc
      _ = (A*p.r^2-B*p.r)*p.decodeDen⁻¹ʳ*γ := by dsimp [Q,HostInput.decode];ring
      _ = _ := by rw [hD,Ring.mul_inverse_cancel _ hu,one_mul]
  have h2 : p.r*Q.c1+p.r^2*Q.c2=ε := by
    calc
      _ = (A*p.r^2-B*p.r)*p.decodeDen⁻¹ʳ*ε := by dsimp [Q,HostInput.decode];ring
      _ = _ := by rw [hD,Ring.mul_inverse_cancel _ hu,one_mul]
  refine ⟨?_,?_,?_⟩
  · change Q.eval 0=v0
    simp [Quad.eval,h0]
  · change Q.eval p.q-p.α*Q.eval p.s=d
    unfold Quad.eval
    dsimp [A,B,γ] at h1
    linear_combination h1+(1-p.α)*h0
  · change Q.eval p.r=vr
    unfold Quad.eval
    dsimp [ε] at h2
    linear_combination h2+h0

abbrev Old := Fin 4
abbrev PhysicalStage := Sum Old Site

def physicalIndex : PhysicalStage → ℕ
  | .inl j => j.val
  | .inr j => 4+j.val

def HostInput.retainedPoly (p : HostInput R) (g : Old→R) : Quad R :=
  p.decode (g 0) (g 3-p.α*g 2) 0

/-- At the true host the retained decoder contributes zero model value;
therefore adding the host column later cannot count an old coordinate twice. -/
theorem HostInput.retained_reads (p : HostInput R) (hu : IsUnit p.decodeDen) (g : Old→R) :
    (p.retainedPoly g).eval 0=g 0 ∧
    (p.retainedPoly g).eval p.q-p.α*(p.retainedPoly g).eval p.s=g 3-p.α*g 2 ∧
    (p.retainedPoly g).eval p.r=0 :=
  p.decode_reads hu _ _ _

def HostInput.moment1 (p : HostInput R) : R := p.r^2*(2:R)⁻¹ʳ
def HostInput.moment2 (p : HostInput R) : R := p.r^3*(3:R)⁻¹ʳ
def HostInput.qs (p : HostInput R) : R :=
  (p.moment1*p.q^2-p.q*p.moment2)*p.momentDen⁻¹ʳ
def HostInput.qq (p : HostInput R) : R :=
  (p.s*p.moment2-p.moment1*p.s^2)*p.momentDen⁻¹ʳ

theorem HostInput.early_moments (p : HostInput R) (h : IsUnit p.momentDen) :
    p.qs*p.s+p.qq*p.q=p.moment1 ∧ p.qs*p.s^2+p.qq*p.q^2=p.moment2 := by
  constructor
  · calc
      _ = (p.momentDen*p.momentDen⁻¹ʳ)*p.moment1 := by unfold HostInput.qs HostInput.qq HostInput.momentDen;ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h,one_mul]
  · calc
      _ = (p.momentDen*p.momentDen⁻¹ʳ)*p.moment2 := by unfold HostInput.qs HostInput.qq HostInput.momentDen;ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h,one_mul]

theorem HostInput.early_invariance (p : HostInput R)
    (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hs : IsUnit p.s) (ht : IsUnit p.t) :
    p.qs+p.α*p.qq=0 := by
  obtain ⟨_,_,hgeom⟩ := p.geometry h3 ht
  have hS : p.s^3*(p.s^3)⁻¹ʳ=1 := Ring.mul_inverse_cancel _ (hs.pow 3)
  have hI : p.α*p.s^3=p.q^2*(3*p.s-2*p.q) := by
    unfold HostInput.α;rw [mul_assoc,mul_comm ((p.s^3)⁻¹ʳ),hS,mul_one]
  have h6 := (show (6:R)=2*3 by ring) ▸ h2.mul h3
  have hsix := h6.mul (hs.pow 3)
  have h21 : (6:R)*p.moment1=3*p.r^2 := by
    unfold HostInput.moment1
    calc
      _ = (2*(2:R)⁻¹ʳ)*(3*p.r^2) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h2,one_mul]
  have h31 : (6:R)*p.moment2=2*p.r^3 := by
    unfold HostInput.moment2
    calc
      _ = (3*(3:R)⁻¹ʳ)*(2*p.r^3) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ h3,one_mul]
  apply hsix.mul_left_cancel
  rw [mul_zero]
  calc
    _ = (-2*p.q*p.r^2*p.s*(p.q-p.s)*
          (2*p.q*p.r-3*p.q*p.s-p.r*p.s))*p.momentDen⁻¹ʳ := by
      unfold HostInput.qs HostInput.qq
      linear_combination
        ((p.s^3*p.q^2-p.q^2*(3*p.s-2*p.q)*p.s^2)*p.momentDen⁻¹ʳ)*h21 +
        ((-p.s^3*p.q+p.q^2*(3*p.s-2*p.q)*p.s)*p.momentDen⁻¹ʳ)*h31 +
        (6*(p.s*p.moment2-p.moment1*p.s^2)*p.momentDen⁻¹ʳ)*hI
    _ = 0 := by rw [hgeom,mul_zero,zero_mul]

def HostInput.retainedOpening (p : HostInput R) (ε : R) : Old→Old→R :=
  let x:=p.s^2*(2*ε)⁻¹ʳ
  let y:=p.α*x
  let z:=(p.q^2*(2:R)⁻¹ʳ-ε*y)*p.s⁻¹ʳ
  ![![0,0,0,0],![ε,0,0,0],![p.s-x,x,0,0],![p.q-y-z,y,z,0]]

theorem HostInput.retained_strict (p : HostInput R) (ε : R) :
    ∀ i j : Old, i≤j → p.retainedOpening ε i j=0 := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (exfalso; revert h; decide +kernel)

def HostInput.retainedAtHost (p : HostInput R) : Old→R :=
  ![p.r-p.qs-p.qq,0,p.qs,p.qq]

/-- The true fifth opening row is the integral of the decoded retained
vector. This earns the old-row compatibility, not merely a determinant. -/
theorem HostInput.actual_retained_integral (p : HostInput R)
    (HD : IsUnit p.decodeDen) (HM : IsUnit p.momentDen)
    (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hs : IsUnit p.s) (ht : IsUnit p.t)
    (g : Old→R) :
    (p.retainedPoly g).primitive p.r=∑ j : Old, p.retainedAtHost j*g j := by
  let f := p.retainedPoly g
  obtain ⟨h0,h1,_⟩ := p.retained_reads HD g
  obtain ⟨hm1,hm2⟩ := p.early_moments HM
  have ha := p.early_invariance h2 h3 hs ht
  have hrow : (∑ j : Old, p.retainedAtHost j*g j)=(p.r-p.qs-p.qq)*g 0+p.qs*g 2+p.qq*g 3 := by
    simp [HostInput.retainedAtHost,Fin.sum_univ_four,add_assoc]
  rw [hrow]
  calc
    _ = (p.r-p.qs-p.qq)*f.eval 0+p.qs*f.eval p.s+p.qq*f.eval p.q := by
      unfold Quad.primitive Quad.eval
      unfold HostInput.moment1 at hm1
      unfold HostInput.moment2 at hm2
      linear_combination -f.c1*hm1-f.c2*hm2
    _ = _ := by
      change f.eval 0=g 0 at h0
      change f.eval p.q-p.α*f.eval p.s=g 3-p.α*g 2 at h1
      linear_combination (p.r-p.qs-p.qq)*h0+p.qq*h1+(f.eval p.s-g 2)*ha

def strictlyLower {n : ℕ} (A : Fin n→Fin n→R) : Prop :=
  ∀ i j, i≤j → A i j=0

def reverseTranspose (K : Site→Site→R) : Site→Site→R := fun i j => K j.rev i.rev

theorem reverseTranspose_strict {K : Site→Site→R} (hK : strictlyLower K) :
    strictlyLower (reverseTranspose K) := by
  intro i j hij
  exact hK _ _ (Fin.rev_le_rev.mpr hij)

def physicalDecoder (p : HostInput R) (B : Site→Site→R) (x : Site→R) (ε : R) :
    PhysicalStage→PhysicalStage→R
  | .inl i,.inl j => p.retainedOpening ε i j
  | .inl _,.inr _ => 0
  | .inr i,.inr j => B i j
  | .inr i,.inl j =>
      let f:=p.retainedPoly (fun l => if l=j then 1 else 0)
      f.primitive (x i) - ∑ k : Site, B i k*f.eval (x k)

/-- The actual decoder layout is four retained opening rows plus eleven
raw rows. Strictness is inherited from the real causal raw matrix; a
checker of the eight raw word equations must still supply that matrix. -/
theorem physicalDecoder_strict (p : HostInput R) (B : Site→Site→R) (x : Site→R) (ε : R)
    (hB : strictlyLower B) :
    ∀ i j : PhysicalStage, physicalIndex i≤physicalIndex j → physicalDecoder p B x ε i j=0 := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact p.retained_strict ε i j h
      | inr j => rfl
  | inr i =>
      cases j with
      | inl j =>
        change 4+i.val≤j.val at h
        have hj := j.isLt
        omega
      | inr j =>
        change 4+i.val≤4+j.val at h
        apply hB
        change i.val≤j.val
        omega

def HostInput.hostBasis (p : HostInput R) (x : R) : R :=
  p.eval2 x*(p.eval2 p.r)⁻¹ʳ

def HostInput.hostIntegral (p : HostInput R) (x : R) : R :=
  p.int2 x*(p.eval2 p.r)⁻¹ʳ

/-- A true raw F2 model receipt implies the host-column decoder gives
the already-present raw physical tap, so the shared row is not duplicated. -/
theorem HostInput.shared_column (p : HostInput R) (B : Site→Site→R) (x : Site→R)
    (hF : IsUnit (p.eval2 p.r)) (hx : x 0=p.r) (i : Site)
    (hModel : ∑ k : Site, B i k*p.eval2 (x k)=p.int2 (x i)) :
    p.hostIntegral (x i) - ∑ k∈Finset.univ.erase 0, B i k*p.hostBasis (x k) = B i 0 := by
  unfold HostInput.hostIntegral HostInput.hostBasis
  simp only [←mul_assoc,←Finset.sum_mul,←sub_mul]
  have hSum : (∑ k∈(Finset.univ : Finset Site).erase 0, B i k*p.eval2 (x k))+
      B i 0*p.eval2 (x 0)=∑ k : Site, B i k*p.eval2 (x k) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  calc
    _ = (B i 0*p.eval2 (x 0))*(p.eval2 p.r)⁻¹ʳ := by rw [←hModel,←hSum,add_sub_cancel_left]
    _ = _ := by rw [hx,mul_assoc,Ring.mul_inverse_cancel _ hF,mul_one]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actual_host_retained (g : Old→R) :
    let p:=actualHost c a b
    (p.retainedPoly g).primitive p.r=∑ j : Old,p.retainedAtHost j*g j := by
  have h2 : IsUnit (2:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h3 : IsUnit (3:R) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  exact (actualHost c a b).actual_retained_integral
    (actual_host_guards ρ c a b hp hc ha hb 13) (actual_host_guards ρ c a b hp hc ha hb 12)
    h2 h3 (actual_host_guards ρ c a b hp hc ha hb 3) (actual_host_guards ρ c a b hp hc ha hb 2) g

theorem actual_physical_fifth (B : Site→Site→R) (x : Site→R) (ε : R)
    (hB : strictlyLower B) (hx : x 0=(actualHost c a b).r) (j : Old) :
    physicalDecoder (actualHost c a b) B x ε (.inr 0) (.inl j)=
      (actualHost c a b).retainedAtHost j := by
  have hB0 (k : Site) : B 0 k=0 := hB _ _ (Fin.zero_le _)
  simp only [physicalDecoder,hB0,zero_mul,Finset.sum_const_zero,sub_zero,hx]
  rw [actual_host_retained ρ c a b hp hc ha hb]
  simp

end Actual

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HostInput.decode_reads
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HostInput.actual_retained_integral
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.physicalDecoder_strict
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HostInput.shared_column
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_physical_fifth
