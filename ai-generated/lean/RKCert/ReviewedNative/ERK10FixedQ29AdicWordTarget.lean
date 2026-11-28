module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordSolve

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

variable {R : Type*} [CommRing R]

def modelP (c a b y : R) : R :=
  2*y*(3:R)⁻¹ʳ+headK c b*(4*bOverA a b*(3:R)⁻¹ʳ-2)*(y-1)

def modelQ (c a b y : R) : R :=
  headK c b*(y-1)+bOverA a b*headK c b*(y-1)*(y-bOverA a b)*(headDelta c a b)⁻¹ʳ

def modelR (c a b y : R) : R :=
  y^2*(2:R)⁻¹ʳ+headK c b*((bOverA a b)^2-2)*(y-1)-
  bOverA a b*headK c b*(bOverA a b*headK c b-cOverA c a*headK c b-cOverA c a+2)*
    (y-1)*(y-bOverA a b)*(headDelta c a b)⁻¹ʳ

def antiderivativeM (c y : R) : R :=
  y^5*(5:R)⁻¹ʳ-c*y^4*(2:R)⁻¹ʳ+c^2*y^3*(3:R)⁻¹ʳ

def jacobiJ (y : R) : R := y-14*y^2+56*y^3-84*y^4+42*y^5

def casePZ (c y : R) : R :=
  antiderivativeM c y-antiderivativeM c c*(jacobiJ c)⁻¹ʳ*jacobiJ y

def basisQZ (c z t u y : R) : R :=
  (y-c)*(y-t)*(y-u)*((z-c)*(z-t)*(z-u))⁻¹ʳ

def datumQZ (c a b z : R) : R := -headN c a b z*casePZ c z*(z^2*(z-c))⁻¹ʳ

def caseQZ (c a b y : R) : R :=
  datumQZ c a b a*basisQZ c a b 26 y+
  datumQZ c a b b*basisQZ c b a 26 y+
  datumQZ c a b 26*basisQZ c 26 a b y

def targetZ (c a b y w u : R) : R := w*casePZ c y+u*caseQZ c a b y
def targetG (c a b y w u : R) : R :=
  ((y-26)*observerZ c a b y w u-targetZ c a b y w u)*(4:R)⁻¹ʳ

def targetLine (c a b y w u : R) : Word→R :=
  let v:=y*a⁻¹ʳ
  ![w*y,w*y^2*(2:R)⁻¹ʳ+u,w*y^3*(3:R)⁻¹ʳ+u*a*modelP c a b v,
    w*y^4*(4:R)⁻¹ʳ+u*a^2*modelR c a b v,u*headK c b*(y-a),u*a^2*modelQ c a b v,
    targetG c a b y w u,targetZ c a b y w u]

def wordTarget (c a b : R) : Site→Word→R :=
  fun i => targetLine c a b (rawY c a b i) (rawW c a b i) (rawU c a b i)

def actualK (c a b : R) : Site→Site→R :=
  chronologicalK (wordInput c a b) (wordTarget c a b) (actualHost c a b).chronologicalPorts

theorem actualK_strict (c a b : R) : strictlyLower (actualK c a b) :=
  chronologicalK_strict _ _ (chronological_ports_strict _)

theorem actualK_ports (c a b : R) :
    actualK c a b 9 8=(actualHost c a b).zb ∧
    actualK c a b 10 8=(actualHost c a b).za ∧
    actualK c a b 10 9=(actualHost c a b).va :=
  chronologicalK_actualPorts _ _ _

theorem target_at_endpoint (c a b w : R) (j : Word) :
    targetLine c a b 0 w 0 j=0 := by
  fin_cases j <;> simp [targetLine,targetG,observerZ,scalarM,targetZ,casePZ,antiderivativeM,jacobiJ]

theorem input_at_endpoint (c a b w : R) {j : Word} (hj : j≠0) :
    wordLine c a b 0 w 0 j=0 := by
  fin_cases j
  · exact (hj rfl).elim
  all_goals simp [wordLine,observerG,observerZ,scalarM,scalarL]

theorem actualK_first (c a b : R) (k : Word) :
    ∑ j : Site, actualK c a b 0 j*wordInput c a b j k=wordTarget c a b 0 k := by
  have h0 : ∀ j : Site, actualK c a b 0 j=0 := fun j => actualK_strict c a b 0 j (Fin.zero_le _)
  simp only [h0,zero_mul,Finset.sum_const_zero]
  exact (target_at_endpoint c a b _ k).symm

theorem headN_at_a (c a b : R) (ha : IsUnit a) (hD : IsUnit (2*b-c)) :
    headN c a b a= -2*(a-c) := by
  have h1 : (2*b-c)*(2*b-c)⁻¹ʳ=1 := Ring.mul_inverse_cancel _ hD
  have h2 : (a*(2*b-c))*(a*(2*b-c))⁻¹ʳ=1 := Ring.mul_inverse_cancel _ (ha.mul hD)
  apply (ha.mul hD).mul_left_cancel
  calc
    _ = (2*a*b*c)*((2*b-c)*(2*b-c)⁻¹ʳ) +
        (2*(-2*a*b+a*c+b*c-c^2)*a)*((a*(2*b-c))*(a*(2*b-c))⁻¹ʳ) := by
      unfold headN
      ring
    _ = _ := by rw [h1,h2,mul_one,mul_one];ring

theorem caseQZ_at_a (c a b : R) (haC : IsUnit (a-c))
    (haB : IsUnit (a-b)) (haD : IsUnit (a-26)) :
    caseQZ c a b a=datumQZ c a b a := by
  unfold caseQZ basisQZ
  rw [Ring.mul_inverse_cancel _ ((haC.mul haB).mul haD)]
  simp

theorem targets_after_first (c a b w u : R)
    (h2 : IsUnit (2:R)) (h4 : IsUnit (4:R))
    (ha : IsUnit a) (hB : IsUnit (2*b-c))
    (haC : IsUnit (a-c)) (haB : IsUnit (a-b)) (haD : IsUnit (a-26))
    (hu : w*a^2+2*u=0) {j : Word} (hj : j≠0) :
    targetLine c a b a w u j=0 := by
  have hD : IsUnit (a^2*(a-c)) := (ha.pow 2).mul haC
  have hN := headN_at_a c a b ha hB
  have hz : observerZ c a b a w u=0 := by
    unfold observerZ scalarM
    rw [hN]
    linear_combination (a-c)^2*hu
  have hT : targetZ c a b a w u=0 := by
    apply hD.mul_left_cancel
    rw [mul_zero,targetZ,caseQZ_at_a c a b haC haB haD,datumQZ,hN]
    have hd := Ring.mul_inverse_cancel _ hD
    linear_combination (a-c)*casePZ c a*hu+2*u*(a-c)*casePZ c a*hd
  have hr : a*a⁻¹ʳ=1 := Ring.mul_inverse_cancel _ ha
  have hi : (2:R)⁻¹ʳ=2*(4:R)⁻¹ʳ := by
    apply h2.mul_left_cancel
    calc
      _ = 1 := Ring.mul_inverse_cancel _ h2
      _ = 4*(4:R)⁻¹ʳ := (Ring.mul_inverse_cancel _ h4).symm
      _ = _ := by ring
  have htwo : (2:R)*((w*a^2)*(2:R)⁻¹ʳ+u)=0 := by
    rw [mul_add,mul_left_comm (2:R) (w*a^2),Ring.mul_inverse_cancel _ h2,mul_one,hu]
  fin_cases j
  · exact (hj rfl).elim
  · change w*a^2*(2:R)⁻¹ʳ+u=0
    exact h2.mul_left_cancel (by simpa only [mul_zero] using htwo)
  · simp only [targetLine,Matrix.cons_val_succ',Matrix.cons_val_zero',hr,modelP,
      sub_self,mul_zero,add_zero]
    linear_combination a*(3:R)⁻¹ʳ*hu
  · simp only [targetLine,Matrix.cons_val_succ',Matrix.cons_val_zero',hr,modelR,
      sub_self,mul_zero,add_zero,one_mul,one_pow,hi]
    linear_combination a^2*(4:R)⁻¹ʳ*hu
  · simp [targetLine]
  · simp [targetLine,hr,modelQ]
  · simp [targetLine,targetG,hz,hT]
  · exact hT

theorem actual_first_u (x : Site→R) (hD : IsUnit (Den ordinary x headA))
    (h2 : IsUnit (2:R)) :
    score x headA*(x headA)^2+2*uAggregate x (actualScale x) headA=0 := by
  have H : Den ordinary x headA*(Den ordinary x headA)⁻¹ʳ=1 :=
    Ring.mul_inverse_cancel _ hD
  have h : uAggregate x (actualScale x) headA =
    -(score x headA*(x headA)^2)*(2:R)⁻¹ʳ := by
    unfold uAggregate actualScale ordInv
    calc
      _ = -(score x headA*(x headA)^2)*(2:R)⁻¹ʳ*
          (Den ordinary x headA*(Den ordinary x headA)⁻¹ʳ) := by ring
      _ = _ := by rw [H,mul_one]
  rw [h]
  have hh := Ring.mul_inverse_cancel _ h2
  linear_combination -(score x headA*(x headA)^2)*hh

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actualK_leading (i : Site) (k : Fin (leadingLength i)) :
    ∑ j : Site, actualK c a b i j * wordInput c a b j (Fin.castLE (leading_le i) k) =
      wordTarget c a b i (Fin.castLE (leading_le i) k) :=
  chronologicalK_selected _ _ _ i (actual_lead_paid ρ c a b hp hc ha hb _ _) k

/-- In the final three reverse rows every one of the eight actual word
columns is solved, and the three forward seed taps stay fixed. -/
theorem actualK_late (i : Site) (hi : 8 ≤ i.val) (k : Word) :
    ∑ j : Site, actualK c a b i j * wordInput c a b j k=wordTarget c a b i k :=
  chronologicalK_late _ _ _ i hi (actual_lead_paid ρ c a b hp hc ha hb _ _) k

/-- The first positive reverse row at the actual node a pays all seven
overdetermined columns, not just its solved first column. -/
theorem actualK_second (k : Word) :
    ∑ j : Site, actualK c a b 1 j*wordInput c a b j k=wordTarget c a b 1 k := by
  by_cases hk : k=0
  · subst k
    exact actualK_leading ρ c a b hp hc ha hb 1 ⟨0,by decide +kernel⟩
  let x:=nodal c a b
  have hw : rawW c a b 1=score x headA := rfl
  have hu : rawU c a b 1=uAggregate x (actualScale x) headA := rfl
  have h2 : IsUnit (2:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h4 : IsUnit (4:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have ha0 : IsUnit a := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [ha];decide +kernel))
  have hb0 : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hpAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have haC : IsUnit (a-c) := hpAll headA (Finset.mem_univ _) center (Finset.mem_univ _) (by decide +kernel)
  have haB : IsUnit (a-b) := hpAll headA (Finset.mem_univ _) headB (Finset.mem_univ _) (by decide +kernel)
  have haD : IsUnit (a-26) := hpAll headA (Finset.mem_univ _) nodeD (Finset.mem_univ _) (by decide +kernel)
  have hDen : IsUnit (Den ordinary x headA) :=
    den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) (by decide +kernel)
  have hsum : ∑ j : Site, actualK c a b 1 j*wordInput c a b j k=0 := by
    rw [Finset.sum_eq_single 0]
    · have hz : wordInput c a b 0 k=0 := input_at_endpoint c a b _ hk
      rw [hz,mul_zero]
    · intro j _ hj
      have hn : 1 ≤ j := by change 1 ≤ j.val; have h := j.val_ne_of_ne hj; simp at h; omega
      rw [actualK_strict c a b 1 j hn,zero_mul]
    · simp
  rw [hsum]
  symm
  change targetLine c a b a (rawW c a b 1) (rawU c a b 1) k=0
  rw [hw,hu]
  exact targets_after_first c a b _ _ h2 h4 ha0 hb0 haC haB haD (actual_first_u x hDen h2) hk

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_first
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_second
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_late
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_ports
