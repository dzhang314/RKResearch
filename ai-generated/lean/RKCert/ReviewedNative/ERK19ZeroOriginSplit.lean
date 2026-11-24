module

public import RKCert.ReviewedNative.ERK19ZeroForwardPorts

public section

/-! # A genuine zero-seed origin split at width 29

The only possible spare carrying a forward correction is the original
origin. A missing origin value would make the two earliest distinct
forward ports a paid quartic contradiction. The exact endpoint Cauchy
kernel then distinguishes the four- and five-site alternatives.
-/
namespace RKResearch.Certified.Graded.NativeMoments

open Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- A factor from a numerical site at one converts an X-moment column
into a two-endpoint column of the same total degree; no positivity or
root-splitting hypothesis is used. -/
theorem x_nodal_paid_moments_exclude_one {P : K[X]} {T : Finset K} {n : ℕ}
    (pn : P≠0) (budget : P.natDegree+T.card≤n)
    (paid : ∀ k : Fin n, (primitive (X^k.val*(X*(P*nodalHull T)))).eval 1=0) :
    (1:K)∉T := by
  intro atOne
  let N := nodalHull T
  have root : N.eval 1=0 := nodalHull_eval_of_mem atOne
  obtain ⟨G,e⟩ := dvd_iff_isRoot.mpr root
  have gn : G≠0 := by
    intro z
    have non : N≠0 := (monic_nodalHull T).ne_zero
    exact non (by rw [e,z,mul_zero])
  have nd : N.natDegree=T.card := natDegree_nodalHull T
  rw [e,natDegree_mul (X_sub_C_ne_zero _) gn,natDegree_X_sub_C] at nd
  let F := X*(P*G)
  have dn : F.natDegree≤n := by
    change (X*(P*G)).natDegree≤n
    rw [natDegree_mul X_ne_zero (mul_ne_zero pn gn),natDegree_X,natDegree_mul pn gn]
    omega
  have eq : X*(P*N)=-((1-X)*F) := by
    dsimp only [F]
    rw [e,map_one]
    ring
  have fz : F=0 := endpoint_moments_detect dn (by simp [F]) (by
    intro k
    have h := paid k
    change (primitive (X^k.val*(X*(P*N)))).eval 1=0 at h
    rwa [eq,mul_neg,map_neg,eval_neg,neg_eq_zero] at h)
  exact mul_ne_zero X_ne_zero (mul_ne_zero pn gn) fz

end RKResearch.Certified.Graded.NativeMoments

namespace RKResearch.Certified.ERK19

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKResearch.Certified.Graded.Reverse.Hidden
open RKResearch.Certified.Graded.NativeMoments
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem origin_clock_zero (ha : ∀ i j,i≤j → A i j=0) : nodes A 0=0 := by
  change (∑ j,A 0 j * (1:K))=0
  exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j),zero_mul]

set_option maxHeartbeats 750000 in
/-- The reflected quintic cannot vanish at the original forward clock
zero. Removing its X factor would leave a quartic killed by the actual
first two distinct forward primitive windows. -/
theorem Width29ForwardPorts.origin_nonzero (ha : ∀ i j,i≤j → A i j=0)
    {h θ : Fin 29 → K} {Q E P : K[X]} {spare : Finset (Fin 29)}
    (H : Width29ZeroHead A b h Q E) (F : Width29ForwardPorts A b θ Q E P spare) :
    P.eval 0≠0 := by
  classical
  intro p0
  let c := nodes A
  let W := reverseContrast A b Q E
  let t := Fin.last 28
  let I := Finset.univ.filter (fun i : Fin 29 => W i≠0)
  let D := P.divX
  have pz : P.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
  have xf : X*D=P := by simpa [D,pz] using X_mul_divX_add P
  have dd : D.natDegree≤4 := by
    dsimp [D]
    rw [natDegree_divX_eq_natDegree_tsub_one,F.quintic]
  have opposite (a : K) : ∃ i, W i≠0 ∧ c i≠a := by
    by_contra! no
    have sub : zeroContrastSites A b Q E⊆({1-a}:Finset K) := by
      intro x hx
      obtain ⟨i,wi,rfl⟩ := mem_weightedSites.mp hx
      apply Finset.mem_singleton.mpr
      change 1-c i=1-a
      rw [no i wi]
    have bound := Finset.card_le_card sub
    rw [Finset.card_singleton] at bound
    have f := H.fourSites
    omega
  have some : I.Nonempty := by
    obtain ⟨i,wi,_⟩ := opposite 0
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,wi⟩⟩
  obtain ⟨i,ii,first⟩ := Finset.exists_min_image I id some
  have wi : W i≠0 := (Finset.mem_filter.mp ii).2
  let u := c i
  let J := I.filter (fun j => c j≠u)
  have other : J.Nonempty := by
    obtain ⟨j,wj,cj⟩ := opposite u
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,wj⟩,cj⟩⟩
  obtain ⟨j,jj,second⟩ := Finset.exists_min_image J id other
  have wj : W j≠0 := (Finset.mem_filter.mp (Finset.mem_filter.mp jj).1).2
  have dist : c j≠u := (Finset.mem_filter.mp jj).2
  have live (k : Fin 29) (wk : W k≠0) : c k≠0 := by
    intro cz
    obtain ⟨v,nz⟩ := F.on k wk
    change θ k=P.eval (c k) at v
    rw [cz,p0] at v
    exact nz v
  have off (k : Fin 29) (kt : k≠t) (kw : W k=0) : θ k=0 := by
    by_cases origin : k=0
    · subst k
      exact F.atOrigin.trans p0
    · exact F.supportAway k kw kt origin
  have tail (k l : Fin 29) (kl : k < l) : k≠t := by
    intro e
    subst k
    exact (not_lt_of_ge (Fin.le_last l)) kl
  have tests : RKCert.EndpointPhysical.primitiveTests D u (c j) := by
    refine ⟨?_,?_⟩
    · intro R dr
      have z : mat A (weightedEval c θ R) i=0 := by
        apply causal_mat ha
        intro l lt
        have no : W l=0 := by
          by_contra n
          exact (not_le_of_gt lt) (first l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,n⟩))
        simp only [weightedEval_apply,off l (tail l i lt) no,mul_zero]
      have p := F.port i wi R (by omega)
      change mat A (weightedEval c θ R) i=(primitive (R*P)).eval u at p
      rw [z] at p
      rw [formalPrimitive_eq_native,xf]
      exact p.symm
    · intro R dr
      let M : K[X] := R*(X-C u)
      have md : M.natDegree≤2 := natDegree_mul_le_of_le dr (natDegree_X_sub_C u).le
      have z : mat A (weightedEval c θ M) j=0 := by
        apply causal_mat ha
        intro l lt
        rw [weightedEval_apply]
        by_cases no : W l=0
        · rw [off l (tail l j lt) no,mul_zero]
        have here : c l=u := by
          by_contra d
          exact (not_le_of_gt lt) (second l (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩,d⟩))
        simp [M,here]
      have p := F.port j wj M (by omega)
      change mat A (weightedEval c θ M) j=(primitive (M*P)).eval (c j) at p
      rw [z] at p
      rw [formalPrimitive_eq_native,show R*(X*(X-C u)*D)=M*P by
        dsimp only [M]
        rw [←xf]
        ring]
      exact p.symm
  have d0 := RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives dd
    (live i wi) (live j wj) dist tests
  have impossible := F.quintic
  rw [←xf,d0,mul_zero,natDegree_zero] at impossible
  omega

/-- An active original origin has reflected clock one, so a
four-site contrast would contradict endpoint Cauchy directly. -/
theorem Width29ZeroHead.five_sites_of_origin (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 19 A b) {h : Fin 29 → K} {Q E : K[X]}
    (H : Width29ZeroHead A b h Q E) (origin : reverseContrast A b Q E 0≠0) :
    (zeroContrastSites A b Q E).card=5 := by
  classical
  let : DecidableEq K := Classical.decEq K
  have cap : (zeroContrastSites A b Q E).card≤5 :=
    (Finset.card_image_le : (zeroContrastSites A b Q E).card≤
      (activeRows (reverseContrast A b Q E)).card).trans H.fiveRows
  have low := H.fourSites
  by_contra! out
  have four : (zeroContrastSites A b Q E).card=4 := by omega
  have qn : Q≠0 := by intro z; have d := H.quintic; simp [z] at d
  have bd : Q.natDegree+(zeroContrastSites A b Q E).card≤9 := by rw [H.quintic,four]
  have y1 : reflectedClock A 0=1 := by change 1-nodes A 0=1; rw [origin_clock_zero ha,sub_zero]
  exact x_nodal_paid_moments_exclude_one qn bd (H.four_site_orthogonal ho four).2
    (mem_weightedSites.mpr ⟨0,origin,y1⟩)

/-- The original first and terminal weights are retained. Four contrast
sites leave exactly the blind physical origin; five leave no spare. -/
structure Width29OriginSplit (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K)
    (Q E P : K[X]) (spare : Finset (Fin 29)) : Prop where
  originPoly : P.eval 0≠0
  reflectedOne : Q.eval 1≠0
  firstQuadratic : quadraticSeed A b 0=0
  firstContrast : reverseContrast A b Q E 0=Q.eval 1*b 0
  terminalWeight : b (Fin.last 28)≠0
  terminalClock : nodes A (Fin.last 28)=1
  terminalQuadratic : quadraticSeed A b (Fin.last 28)=0
  terminalContrast : reverseContrast A b Q E (Fin.last 28)=0
  quadraticRows : (activeRows (quadraticSeed A b)).card=18
  layout :
    (b 0≠0 ∧ reverseContrast A b Q E 0≠0 ∧ spare=∅ ∧
      (activeRows (reverseContrast A b Q E)).card=5 ∧ (zeroContrastSites A b Q E).card=5) ∨
    (b 0=0 ∧ reverseContrast A b Q E 0=0 ∧ spare={0} ∧
      (activeRows (reverseContrast A b Q E)).card=4 ∧ (zeroContrastSites A b Q E).card=4)

theorem Width29ForwardPorts.origin_split (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    {h θ : Fin 29 → K} {Q E P : K[X]} {spare : Finset (Fin 29)}
    (H : Width29ZeroHead A b h Q E) (F : Width29ForwardPorts A b θ Q E P spare)
    (Z : Width29ZeroCover A b) : Width29OriginSplit A b Q E P spare := by
  classical
  let : DecidableEq K := Classical.decEq K
  let W := reverseContrast A b Q E
  let d := quadraticSeed A b
  let T := zeroContrastSites A b Q E
  let t := Fin.last 28
  have p0 := F.origin_nonzero ha H
  have q0 : Q.eval 1≠0 := by
    intro e
    apply p0
    rw [F.reflected,eval_comp,eval_sub,eval_one,eval_X,sub_zero,e]
  have y1 : reflectedClock A 0=1 := by change 1-nodes A 0=1; rw [origin_clock_zero ha,sub_zero]
  have h0 : h 0=0 := origin_zeroSpace ha 5 H.staircase.headGrade
  have d0 : d 0=0 := by
    have h := H.traceQ 0
    rw [h0,mul_zero,y1] at h
    exact (mul_eq_zero.mp h.symm).resolve_left q0
  have w0 : W 0=Q.eval 1*b 0 := by
    simp only [W,reverseContrast,Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,y1,
      show quadraticSeed A b 0=0 from d0,one_mul,mul_zero,sub_zero]
  have wt : W t=0 := by
    by_contra e
    have y0 : reflectedClock A t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
    exact (H.active e).2.1 y0
  have rows := F.footprint
  have dLo : 18≤(activeRows d).card := H.quadraticRows
  have sLo : 4≤T.card := H.fourSites
  have sHi : T.card≤(activeRows W).card := Finset.card_image_le
  have wHi : (activeRows W).card≤5 := H.fiveRows
  change spare.card+(activeRows d).card+(activeRows W).card=23 at rows
  refine ⟨p0,q0,d0,w0,Z.lastLive,Z.lastClock,Z.lastSeed,wt,?_,?_⟩
  · change (activeRows d).card=18
    by_cases a : W 0=0
    · have mem := (F.exceptionalOrigin a p0).1
      have lo := Finset.card_pos.mpr ⟨_,mem⟩
      omega
    · have g : T.card=5 := H.five_sites_of_origin ha ho a
      omega
  · by_cases a : W 0=0
    · right
      have z := F.exceptionalOrigin a p0
      have lo : 0<spare.card := Finset.card_pos.mpr ⟨_,z.1⟩
      have one : spare.card=1 := by omega
      have eq : spare={0} := by
        apply Finset.Subset.antisymm
        · intro i hi
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp one.le i hi 0 z.1)
        · intro i hi
          obtain rfl := Finset.mem_singleton.mp hi
          exact z.1
      have wr : (activeRows W).card=4 := by omega
      have tr : T.card=4 := by omega
      exact ⟨z.2.2,a,eq,wr,tr⟩
    · left
      have g : T.card=5 := H.five_sites_of_origin ha ho a
      have b0 : b 0≠0 := fun z => a (by rw [w0,z,mul_zero])
      have wr : (activeRows W).card=5 := by omega
      exact ⟨b0,a,Finset.card_eq_zero.mp (by omega),wr,g⟩

/-- Actual origin split from exact strict reviewed order 19, the
original width 29 tableau, and zero first adjoint seed. -/
theorem width29_zero_origin_split (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ h Q E i j k θ P spare, Width29ZeroHead A b h Q E ∧
      Width29ReversePortSequence A b Q E i j k ∧ Width29ForwardPorts A b θ Q E P spare ∧
      Width29OriginSplit A b Q E P spare := by
  obtain ⟨h,Q,E,i,j,k,θ,P,spare,H,R,F⟩ := width29_zero_physical_ports ha ho zero
  exact ⟨h,Q,E,i,j,k,θ,P,spare,H,R,F,F.origin_split ha ho H (width29_zero_cover_data ha ho zero)⟩

end
end RKResearch.Certified.ERK19

