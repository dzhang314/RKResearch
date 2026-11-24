module
public import RKCert.HeadChart
public import RKCert.NodalHermiteRank

@[expose] public section

/-! # Distinct-site rank and mass of a true nodal orbit

The evaluation map factors through the numerical (not physical) support of
its head. This layer works over any field: signs, ordering, and a restriction
on the characteristic are not part of its rank statements. -/
namespace RKCert.Endpoint
open RKCert.Paired Polynomial Module
open scoped Classical

noncomputable section
variable {K:Type*} [Field K] {s:ℕ}
variable (c d:Vec K s)

abbrev orbitSites := Clock.headSites c d

/-- Evaluate one independent coefficient per actual nonzero numerical fiber. -/
def orbitColumns : (orbitSites c d → K) →ₗ[K] Vec K s :=
  LinearMap.pi fun i => if h:d i≠0 then
    d i • LinearMap.proj (⟨c i,Clock.headSites_mem i h⟩ : orbitSites c d)
  else 0

theorem orbitColumns_apply (f:orbitSites c d→K) (i:Fin s) :
    orbitColumns c d f i = if h:d i≠0 then f ⟨c i,Clock.headSites_mem i h⟩*d i else 0 := by
  classical
  by_cases h:d i≠0
  · simp [orbitColumns,h,mul_comm]
  · have z:d i=0:=not_ne_iff.mp h
    simp [orbitColumns,z]

theorem orbitColumns_injective : Function.Injective (orbitColumns c d) := by
  intro f g eq
  funext a
  obtain ⟨i,hi,e⟩ := Finset.mem_image.mp a.property
  have hn := (Finset.mem_filter.mp hi).2
  have he : (⟨c i,Clock.headSites_mem i hn⟩:orbitSites c d)=a := Subtype.ext e
  have h := congrFun eq i
  rw [orbitColumns_apply,orbitColumns_apply,dite_eq_left hn,dite_eq_left hn,he] at h
  exact mul_right_cancel₀ hn h

/-- The finite-dimensional diagonal-invariant hull, with exact site rank. -/
def nodalOrbit := LinearMap.range (orbitColumns c d)

theorem nodalOrbit_rank : finrank K (nodalOrbit c d)=(orbitSites c d).card := by
  rw [nodalOrbit,LinearMap.finrank_range_of_inj (orbitColumns_injective c d)]
  simp only [Module.finrank_pi,Fintype.card_coe]

theorem weightedEval_eq_orbitColumns (P:K[X]) :
    weightedEval c d P = orbitColumns c d (fun a=>P.eval a.val) := by
  ext i
  rw [weightedEval_apply,orbitColumns_apply]
  by_cases h:d i≠0
  · rw [dite_eq_left h]
  · have z:d i=0:=not_ne_iff.mp h
    simp [z]

theorem nodalOrbit_eq_weightedEval : nodalOrbit c d=LinearMap.range (weightedEval c d) := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    let P:K[X] := Lagrange.interpolate (orbitSites c d) id (fun a=>
      if h:a∈orbitSites c d then f ⟨a,h⟩ else 0)
    refine ⟨P,?_⟩
    rw [weightedEval_eq_orbitColumns]
    congr 1
    funext a
    rw [show P.eval a.val=(if h:a.val∈orbitSites c d then f ⟨a.val,h⟩ else 0) from
      Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) a.property, dite_eq_left a.property]
  · rintro _ ⟨P,rfl⟩
    exact ⟨_,(weightedEval_eq_orbitColumns c d P).symm⟩

theorem nodalOrbit_mask : MaskInvariant c (nodalOrbit c d) := by
  intro a _ h
  obtain ⟨f,rfl⟩:=h
  refine ⟨fun z=>if z.val=a then f z else 0,?_⟩
  ext i
  rw [orbitColumns_apply]
  by_cases dn:d i≠0
  · rw [dite_eq_left dn]
    simp only [blockMask,orbitColumns_apply,dite_eq_left dn]
    by_cases e:c i=a <;> simp [e]
  · simp [dn,blockMask,orbitColumns_apply]

/-- Powers of the head through degree strictly below (k), in the actual
physical stage vector space. -/
def orbitBand (k:ℕ) := LinearMap.range ((weightedEval c d).comp (ofFn k))

theorem orbitBand_le (k:ℕ) : orbitBand c d k≤nodalOrbit c d := by
  rw [nodalOrbit_eq_weightedEval]
  rintro _ ⟨v,rfl⟩
  exact ⟨_,rfl⟩

theorem orbitBand_rank (k:ℕ) (enough:k≤(orbitSites c d).card) :
    finrank K (orbitBand c d k)=k := by
  apply Eq.trans (LinearMap.finrank_range_of_inj
    (f:=(weightedEval c d).comp (ofFn k)) ?_) (Module.finrank_fin_fun K)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f h
  apply injective_ofFn k
  rw [map_zero]
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (orbitSites c d)
  · exact (ofFn_degree_lt f).trans_le (by exact_mod_cast enough)
  · intro a ha
    obtain ⟨i,hi,e⟩:=Finset.mem_image.mp ha
    have hn := (Finset.mem_filter.mp hi).2
    have hi := congrFun h i
    change weightedEval c d (ofFn k f) i=0 at hi
    rw [weightedEval_apply,e] at hi
    exact (mul_eq_zero.mp hi).resolve_right hn

/-- A finite number of zero scalar moments forces zero mass of every vector
in the whole nodal orbit. In particular this does not sum cancelling physical
coordinates after a hypothetical stage deletion. -/
theorem nodalOrbit_mass
    (m:∀ j<(orbitSites c d).card, ∑ i,(c i)^j*d i=0) :
    ∀ w∈nodalOrbit c d, ∑ i,w i=0 := by
  intro _ h
  obtain ⟨f,rfl⟩:=h
  let P:K[X] := Lagrange.interpolate (orbitSites c d) id (fun a=>
    if hz:a∈orbitSites c d then f ⟨a,hz⟩ else 0)
  have eq : orbitColumns c d f=weightedEval c d P := by
    rw [weightedEval_eq_orbitColumns]
    congr 1
    funext a
    rw [show P.eval a.val=(if h:a.val∈orbitSites c d then f ⟨a,h⟩ else 0) from
      Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) a.property,dite_eq_left a.property]
  rw [eq]
  by_cases pn:P=0
  · simp [pn]
  have dp : P.natDegree < (orbitSites c d).card :=
    (natDegree_lt_iff_degree_lt pn).mpr (Lagrange.degree_interpolate_lt _ (Set.injOn_id _))
  have ee:weightedEval c d P=∑ j∈Finset.range (orbitSites c d).card,
        P.coeff j • fun i => (c i)^j*d i := by
    ext i
    rw [weightedEval_apply,Finset.sum_apply,eval_eq_sum_range' dp,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [ee]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  exact Finset.sum_eq_zero (fun j hj=>by rw [m j (Finset.mem_range.mp hj),mul_zero])

end
end RKCert.Endpoint
