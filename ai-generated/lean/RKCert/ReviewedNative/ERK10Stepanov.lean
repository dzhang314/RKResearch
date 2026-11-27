module

public import RKCert.ReviewedNative.ERK10StepanovClassChecks

@[expose] public section

/-! # An exactly order-ten 15-stage explicit tableau

The data are the authenticated Stepanov Zenodo coefficient file. Its
normal forms and every required rooted-tree moment are proved in Lean
over the nested radical relations; no order premise is imposed on the
parameters or the target ring. The order-eleven bush has residual
+1/52920, in the reviewed factorial normalization. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay FiniteRootedTree

variable {R : Type*} [CommRing R]

theorem order_ten {x y z d : R} (h : Roots x y z) (hd : (D:R)*d=1) :
    HasOrder 10 (A x y z d) (b x y z d) :=
  class_order classReceipts h hd

theorem not_order_eleven [Nontrivial R] {x y z d : R}
    (h : Roots x y z) (hd : (D:R)*d=1) :
    ¬ HasOrder 11 (A x y z d) (b x y z d) := by
  intro h11
  have ht : ((bushyTree 11).order:ℕ) ≤ 11 := by decide
  have hh := class_bush_defect classReceipts h hd
  rw [h11 (bushyTree 11) ht, sub_self, mul_zero] at hh
  exact zero_ne_one (show (0:R)=1 by simpa only [bushResid,Int.cast_one] using hh)

theorem exact_with_roots [Nontrivial R] {x y z : R}
    (h : Roots x y z) (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨e,he⟩ := hD
  let d : R := ↑(e⁻¹)
  have hd : (D:R)*d=1 := by rw [← he]; exact e.mul_inv
  exact ⟨A x y z d,b x y z d,explicit x y z d,order_ten h hd,not_order_eleven h hd⟩

end RKResearch.Certified.ERK10Stepanov

#print axioms RKResearch.Certified.ERK10Stepanov.order_ten
#print axioms RKResearch.Certified.ERK10Stepanov.exact_with_roots
