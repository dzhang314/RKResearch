module
public import RKCert.ReviewedNative.OrderNineSixOnFG

@[expose] public section

/-! # Native physical order-nine five-six chart satisfies the degree-eight atlas input -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] 

variable [LinearOrder K] [IsStrictOrderedRing K]
theorem ActualSixOnFG.compatibility_zero {A : Fin 12→Fin 12→K} {P : K[X]}
    (d : ActualSixOnFG A P) :
    let h := nodes A (lowPrefix10 d.first)
    let r := nodes A (lowPrefix10 d.middle)
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let v := nodes A (lowPrefix10 (Fin.last 9))
    r=2-d.pencil_parameter-h-u-v ∧ RKCert.Paired.sixOnK8 h u v d.pencil_parameter=0 := by
  dsimp only
  let h := nodes A (lowPrefix10 d.first)
  let r := nodes A (lowPrefix10 d.middle)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let l := d.pencil_parameter
  let W : Fin 4→K := ![h,r,u,v]
  have iW : Function.Injective W := d.root_set_injective
  have wr := RKCert.Paired.lobattoPencil_four_root_sum l W iW d.pencil_roots
  have wr' : h+r+u+v=2-l := by
    simpa [Fin.sum_univ_succ,W,add_assoc] using wr
  have eq : r=2-l-h-u-v := by linear_combination wr'
  have nuv : u≠v := fun e => (by decide : (2:Fin 4)≠3) (iW e)
  have nvr : v≠r := fun e => (by decide : (3:Fin 4)≠1) (iW e)
  have nur : u≠r := fun e => (by decide : (2:Fin 4)≠1) (iW e)
  have zero := RKCert.Paired.sixOnK8Raw_zero_of_FG d.first_nonzero nuv nvr nur d.D_nonzero d.cubic_v_nonzero
    d.F_zero d.G_zero
  change r=2-l-h-u-v ∧ RKCert.Paired.sixOnK8 h u v l=0
  refine ⟨eq,?_⟩
  unfold RKCert.Paired.sixOnK8
  rw [←eq]
  exact zero
end RKResearch.Certified.Graded.MultiOff
