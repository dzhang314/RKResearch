module
public import RKCert.ERKOddMacroLabels
public import RKCert.ERKOddClockMassTools

@[expose] public section
/-! # The short τ orbit pays a second physical dimension at each clock -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Endpoint
open Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h W:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem LocalHeadContrast.orbit_macro_kernel_of_zero_masses
    (T:LocalHeadContrast A b τ h W U Q)
    (sum:∀a∈headSites (mirror A) τ,clockMass (mirror A) τ a=0):
    nodalOrbit (mirror A) τ≤(blockTotal (localMacroTag A b τ h U)).ker:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let : DecidableEq (maskTag b τ U):=Classical.decEq _
  let y:=mirror A
  let c:=localMacroTag A b τ h U
  have tag (i:Fin 26)(nz:τ i≠0):c i=(y i,Q.eval (y i),0,0):=by
    obtain ⟨eq,g⟩:=T.headValue i nz
    change (y i,h i,0,forwardValueTag (reverseHidden b τ U) i)=(y i,Q.eval (y i),0,0)
    rw [eq,forwardValueTag_zero.mpr g]
  rw [nodalOrbit_eq_weightedEval]
  rintro _ ⟨P,rfl⟩
  change blockTotal c (weightedEval y τ P)=0
  funext a
  rw [blockTotal_apply,Pi.zero_apply]
  by_cases active:∃i:Fin 26,c i=a.val∧τ i≠0
  · obtain ⟨i,eq,nz⟩:=active
    have related(j:Fin 26)(jt:τ j≠0):c j=a.val↔y j=y i:=by
      rw [←eq,tag j jt,tag i nz]
      constructor
      · exact fun h=>congrArg Prod.fst h
      · intro e;rw [e]
    have e:(∑ j ∈ Finset.univ.filter (fun i=>c i=a.val),weightedEval y τ P j)=
        P.eval (y i)*(∑ j ∈ (activeRows τ).filter (fun j=>y j=y i),τ j):=by
      simp only [Finset.mul_sum,Finset.sum_filter,activeRows]
      apply Finset.sum_congr rfl
      intro j _
      by_cases n:τ j=0
      · simp [n]
      by_cases same:y j=y i
      · have a:(c j=a.val):=(related j n).mpr same
        simp [a,same,n]
      · have w:c j≠a.val:=fun c=>same ((related j n).mp c)
        simp [w,same,n]
    have z:(∑ j ∈ (activeRows τ).filter (fun j=>y j=y i),τ j)=0:=sum (y i) (headSites_mem i nz)
    rw [e,z,mul_zero]
  · apply Finset.sum_eq_zero
    intro j hj
    have q:τ j=0:=not_ne_iff.mp (fun h=>active ⟨j,(Finset.mem_filter.mp hj).2,h⟩)
    simp [q]

theorem LocalLinearBand.short_orbit_macro_kernel (B:LocalLinearBand A b r U τ)
    (T:LocalHeadContrast A b τ h W U Q)
    (small:(headSites (mirror A) τ).card≤16-r):
    nodalOrbit (mirror A) τ≤(blockTotal (localMacroTag A b τ h U)).ker:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let : DecidableEq (maskTag b τ U):=Classical.decEq _
  let y:=mirror A
  let c:=localMacroTag A b τ h U
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  have sum(a:K)(ay:a∈headSites y τ):
      (∑j ∈ (activeRows τ).filter (fun i=>y i=a),τ j)=0:=by
    apply local_mass_zero_of_short_support y τ (l:=15-r) (by
      change (headSites y τ).card≤16-r at small
      omega) _ ay
    intro P dP
    have e:=mem_annih.mp B.paid _ (mirror_eval_in_tree (A:=A) P dP)
    simpa only [row_apply] using e
  exact T.orbit_macro_kernel_of_zero_masses (fun a ha=>sum a ha)

theorem LocalLinearBand.long_macro_sites (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (T:LocalHeadContrast A b τ h W U Q)
    (six:7≤finrank K (zeroSpace A 6)) (masks:finrank K (reverseHidden b τ U)=5):
    17-r≤(headSites (mirror A) τ).card:=by
  let y:=mirror A
  let c:=localMacroTag A b τ h U
  let V:=nodalOrbit y τ
  let n:=(headSites y τ).card
  have rr:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have big:10-r≤n:=B.extra_site_if_six_rich ha ho S six
  have ww:4≤(headSites y W).card:=four_sites_of_unit_contrast _ _ _ T.degree T.nonzero T.moments
  have rank:finrank K V=n:=nodalOrbit_rank _ _
  have M:=B.local_macro_audit ho T
  have ln:5+n+(headSites y W).card≤(physicalBlocks c).card:=by
    have h:=M.lower
    rw [masks] at h
    exact h
  by_contra! short
  have sh:(headSites (mirror A) τ).card≤16-r:=by change n<17-r at short;change n≤16-r;omega
  have vo:V≤annih U:=by
    rw [show V=nodalOrbit y τ from rfl,nodalOrbit_eq_weightedEval]
    rintro _ ⟨P,rfl⟩
    exact weightedEval_orthogonal B.clock B.orthogonal P
  have pay:=rank_with_physical_blocks c U V M.baseZero (B.short_orbit_macro_kernel T sh) vo
  rw [B.dimension,rank] at pay
  omega
end
end RKCert.Paired.ReverseHull

