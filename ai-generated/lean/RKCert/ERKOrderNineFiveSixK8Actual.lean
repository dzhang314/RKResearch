module

public import RKCert.ERKOrderNineFiveSixK8

@[expose] public section

/-! # Actual ordered-root compatibility, with the true Vieta root sum -/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem lobattoPencil_natDegree (l : K) : (lobattoPencil l).natDegree=4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have e0 : 0≠k := by omega
    have e1 : 1≠k := by omega
    have e2 : 2≠k := by omega
    have e3 : 3≠k := by omega
    have e4 : 4≠k := by omega
    simp [lobattoPencil,coeff_monomial,coeff_C,Ne.symm e0,e1,e2,e3,e4]
  · simp [lobattoPencil,coeff_monomial]

omit [CharZero K] in
/-- The four genuine distinct pencil roots sum to 2−l, as a
consequence of exact finite polynomial identity, not a real-root theorem. -/
theorem lobattoPencil_four_root_sum (l : K) (W : Fin 4 → K)
    (inj : Function.Injective W) (roots : ∀ i,(lobattoPencil l).eval (W i)=0) :
    (∑ i,W i)=2-l := by
  let S := Finset.univ.image W
  have card : S.card=4 := by simp only [S,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin]
  have deg : (nodalHull S).natDegree=4 := (natDegree_nodalHull _).trans card
  obtain ⟨a,eq⟩ := polynomial_scalar_hull S (lobattoPencil l)
    (by rw [lobattoPencil_natDegree,card]) (fun x hx=>by
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact roots i)
  have r4 : (nodalHull S).coeff 4=1 := by
    rw [←deg]
    exact (monic_nodalHull S).coeff_natDegree
  have aa : a=1 := by
    have h := congrArg (fun Q : K[X]=>Q.coeff 4) eq
    simpa [lobattoPencil,coeff_monomial,coeff_C_mul,r4] using h.symm
  have eh : lobattoPencil l=nodalHull S := by simpa [aa] using eq
  have h1 : (lobattoPencil l).nextCoeff=l-2 := by
    unfold nextCoeff
    rw [lobattoPencil_natDegree]
    norm_num [lobattoPencil,coeff_monomial]
  have h2 : (nodalHull S).nextCoeff=-(∑ x∈S,x) := by
    simpa only [nodalHull,id_eq] using (prod_X_sub_C_nextCoeff (s:=S) id)
  have h3 : (∑ x∈S,x)=(∑ i,W i) := by
    dsimp only [S]
    rw [Finset.sum_image (fun _ _ _ _ h=>inj h)]
  rw [eh,h2,h3] at h1
  linear_combination -h1

section Ordered
variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- The exact degree-eight compatibility input, with the third
chronological clean node expressed by the Vieta root sum. -/
theorem ActualSixOnFG.compatibility_zero {A : Fin 12→Fin 12→L} {P : L[X]}
    (d : ActualSixOnFG A P) :
    let h := nodes A (lowPrefix10 d.first)
    let r := nodes A (lowPrefix10 d.middle)
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let v := nodes A (lowPrefix10 (Fin.last 9))
    r=2-d.pencil_parameter-h-u-v ∧ sixOnK8 h u v d.pencil_parameter=0 := by
  dsimp only
  let h := nodes A (lowPrefix10 d.first)
  let r := nodes A (lowPrefix10 d.middle)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let l := d.pencil_parameter
  let W : Fin 4→L := ![h,r,u,v]
  have iW : Function.Injective W := d.root_set_injective
  have wr := lobattoPencil_four_root_sum l W iW d.pencil_roots
  have wr' : h+r+u+v=2-l := by
    simpa [Fin.sum_univ_succ,W,add_assoc] using wr
  have eq : r=2-l-h-u-v := by linear_combination wr'
  have nuv : u≠v := fun e => (by decide : (2:Fin 4)≠3) (iW e)
  have nvr : v≠r := fun e => (by decide : (3:Fin 4)≠1) (iW e)
  have nur : u≠r := fun e => (by decide : (2:Fin 4)≠1) (iW e)
  have zero := sixOnK8Raw_zero_of_FG d.first_nonzero nuv nvr nur d.D_nonzero d.cubic_v_nonzero
    d.F_zero d.G_zero
  change r=2-l-h-u-v ∧ sixOnK8 h u v l=0
  refine ⟨eq,?_⟩
  unfold sixOnK8
  rw [←eq]
  exact zero

end Ordered
end RKCert.Paired
