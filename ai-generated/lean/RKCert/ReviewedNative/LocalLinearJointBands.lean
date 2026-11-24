module

public import RKCert.ReviewedNative.LocalLinearCompensatedContrast
public import RKCert.ReviewedNative.ERK19SeedFibers

@[expose] public section

/-! Source-only draft. Counts actual weighted ranges and joint indicators,
not selected representatives or the number of weighted physical rows. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- Sitewise signed cancellation of a paid reflected row. This is the
reflected, non-first-seed form of the existing Lagrange grouping. -/
theorem reflected_clockMass_zero_of_paid_band (ho : HasOrder p A b)
    {n : ℕ} {v : Fin s→K} (hv : v∈primitiveBack A b n)
    (pay : (weightedSites (reflectedClock A) v).card+n+1≤p) :
    ∀ a,clockMass (reflectedClock A) v a=0 := by
  let y := reflectedClock A
  let S := weightedSites y v
  change S.card+n+1≤p at pay
  intro a
  by_cases an : a∈S
  · let P := Lagrange.basis S id a
    have d := Lagrange.natDegree_basis (Set.injOn_id _) an
    change P.natDegree=S.card-1 at d
    let C : K[X] := 1-X
    let R := P.comp C
    have cd : C.natDegree≤1 := by
      change (1-X : K[X]).natDegree≤1
      exact (natDegree_sub_le _ _).trans (by simp)
    have rd : R.natDegree≤P.natDegree :=
      natDegree_comp_le.trans ((Nat.mul_le_mul (le_refl _) cd).trans_eq (Nat.mul_one _))
    have cardpos : 0<S.card := Finset.card_pos.mpr ⟨a,an⟩
    have z := mem_annih.mp (primitiveBack_annih ho R.natDegree n (by omega) hv) _
      (evalNodes_mem_treeSpace A R le_rfl)
    have test : (∑ i,v i*P.eval (y i))=0 := by
      simpa only [row_apply,dotProduct,evalNodes_apply,R,C,y,eval_comp,eval_sub,eval_one,
        eval_X,reflectedClock,Pi.sub_apply,Pi.one_apply] using z
    rw [weighted_sum_by_clock y v (fun x=>P.eval x)] at test
    have inImage : a∈Finset.univ.image y := by
      obtain ⟨i,_,eq⟩ := mem_weightedSites.mp an
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq⟩
    rw [Finset.sum_eq_single_of_mem a inImage] at test
    · rwa [show P.eval a=1 from Lagrange.eval_basis_self (Set.injOn_id _) an,mul_one] at test
    · intro q _ qne
      by_cases qT : q∈S
      · rw [show P.eval q=0 from Lagrange.eval_basis_of_ne (v:=id) qne.symm qT,mul_zero]
      · rw [clockMass_zero_of_not_site qT,zero_mul]
  · exact clockMass_zero_of_not_site an

def completeOrbit (y v : Fin s→K) := (weightedEval y v).range

theorem completeOrbit_rank (y v : Fin s→K) :
    finrank K (completeOrbit y v)=(weightedSites y v).card := by
  rw [completeOrbit,←weightedBand_eq_range y v (weightedSites y v).card le_rfl]
  exact weightedBand_rank y v _ le_rfl

theorem completeOrbit_annih {y v : Fin s→K} {U : Submodule K (Fin s→K)}
    (stable : U.map (diag y)≤U) (hv : v∈annih U) : completeOrbit y v≤annih U := by
  rintro _ ⟨P,rfl⟩
  apply mem_annih.mpr
  intro w hw
  have z := mem_annih.mp hv _ (reflected_clock_weighted_core stable hw P)
  rw [row_apply,dotProduct] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply]
  ring

def coreLabels : Set (K×K×K) := {a | a.2.2=1}

def tauLabels (Q : K[X]) (sites : Finset K) : Set (K×K×K) :=
  {a | a.2.2=0 ∧ a.2.1=Q.eval a.1 ∧ a.1∈sites}

def contrastLabels (Q : K[X]) (sites : Finset K) : Set (K×K×K) :=
  {a | a.2.2=0 ∧ a.2.1=0 ∧ Q.eval a.1≠0 ∧ a.1∈sites}

private theorem label_separations (Q : K[X]) (T S : Finset K) :
    Disjoint coreLabels (tauLabels Q T) ∧ Disjoint coreLabels (contrastLabels Q S) ∧
      Disjoint (tauLabels Q T) (contrastLabels Q S) := by
  refine ⟨Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_⟩
  · intro x hx ha
    change x.2.2=1 at hx
    exact one_ne_zero (hx.symm.trans ha.1)
  · intro x hx ha
    change x.2.2=1 at hx
    exact one_ne_zero (hx.symm.trans ha.1)
  · intro x ht hs
    exact hs.2.2.1 (ht.2.1.symm.trans hs.2.1)

structure JointBandCensus (y f e τ W : Fin s→K) (Q : K[X])
    (U J : Submodule K (Fin s→K)) : Prop where
  binary : ∀ i,e i=0 ∨ e i=1
  offCore : ∀ v∈J,∀ i,e i=0 → v i=0
  tauRows : ∀ i,τ i≠0 → e i=0 ∧ f i=Q.eval (y i)
  contrastRows : ∀ i,W i≠0 → e i=0 ∧ f i=0 ∧ Q.eval (y i)≠0
  coreOrth : J≤annih U
  tauOrth : τ∈annih U
  contrastOrth : W∈annih U
  clockStable : U.map (diag y)≤U
  indicator : ∀ a,labelIndicator (tripleLabel y f e) a∈annih U

variable {y f e τ W : Fin s→K} {Q : K[X]} {U J : Submodule K (Fin s→K)}

namespace JointBandCensus

theorem core_on (C : JointBandCensus y f e τ W Q U J) :
    OnLabels (tripleLabel y f e) coreLabels J := by
  intro v hv i off
  rcases C.binary i with zero|one
  · exact C.offCore v hv i zero
  · exact (off one).elim

theorem tau_on (C : JointBandCensus y f e τ W Q U J) :
    OnLabels (tripleLabel y f e) (tauLabels Q (weightedSites y τ)) (completeOrbit y τ) := by
  rintro _ ⟨P,rfl⟩ i off
  rw [weightedEval_apply]
  by_cases z : τ i=0
  · rw [z,mul_zero]
  · exact (off ⟨(C.tauRows i z).1,(C.tauRows i z).2,mem_weightedSites.mpr ⟨i,z,rfl⟩⟩).elim

theorem contrast_on (C : JointBandCensus y f e τ W Q U J) :
    OnLabels (tripleLabel y f e) (contrastLabels Q (weightedSites y W)) (completeOrbit y W) := by
  rintro _ ⟨P,rfl⟩ i off
  rw [weightedEval_apply]
  by_cases z : W i=0
  · rw [z,mul_zero]
  · obtain ⟨ez,fz,ne⟩ := C.contrastRows i z
    exact (off ⟨ez,fz,ne,mem_weightedSites.mpr ⟨i,z,rfl⟩⟩).elim

theorem ordinary_rank (C : JointBandCensus y f e τ W Q U J) :
    finrank K U+finrank K J+(weightedSites y τ).card+(weightedSites y W).card≤s := by
  obtain ⟨st,sr,tr⟩ := label_separations Q (weightedSites y τ) (weightedSites y W)
  have dims := finrank_supported_triple C.core_on C.tau_on C.contrast_on st sr tr
  have le := Submodule.finrank_mono (sup_le
    (sup_le C.coreOrth (completeOrbit_annih C.clockStable C.tauOrth))
    (completeOrbit_annih C.clockStable C.contrastOrth))
  rw [dims,completeOrbit_rank,completeOrbit_rank] at le
  have all := finrank_annih U
  rw [Fintype.card_fin] at all
  omega

theorem physical_cover (C : JointBandCensus y f e τ W Q U J)
    (fill : s≤finrank K U+finrank K J+(weightedSites y τ).card+(weightedSites y W).card) :
    ∀ i, e i=0 → f i=Q.eval (y i) ∨ f i=0 := by
  obtain ⟨st,sr,tr⟩ := label_separations Q (weightedSites y τ) (weightedSites y W)
  have rank : finrank K (annih U)≤finrank K J+finrank K (completeOrbit y τ)+finrank K (completeOrbit y W) := by
    rw [completeOrbit_rank,completeOrbit_rank]
    have all := finrank_annih U
    rw [Fintype.card_fin] at all
    omega
  have take := cover_of_supported_rank_equality C.core_on C.tau_on C.contrast_on st sr tr
    (sup_le (sup_le C.coreOrth (completeOrbit_annih C.clockStable C.tauOrth))
      (completeOrbit_annih C.clockStable C.contrastOrth)) rank (fun i=>C.indicator _)
  intro i iz
  rcases take i with core|tt|ww
  · have e1 : e i=1 := core
    exact (zero_ne_one (iz.symm.trans e1)).elim
  · exact Or.inl tt.2.1
  · exact Or.inr ww.2.1

end JointBandCensus

def tauSelector (y f e : Fin s→K) (Q : K[X]) (T : Finset K) : Fin s→K :=
  fun i=>if tripleLabel y f e i∈tauLabels Q T then 1 else 0

private theorem tauSelector_one (C : JointBandCensus y f e τ W Q U J) {i : Fin s}
    (live : τ i≠0) :
    tauSelector y f e Q (weightedSites y τ) i=1 := by
  have w : tripleLabel y f e i∈tauLabels Q (weightedSites y τ) :=
    ⟨(C.tauRows i live).1,(C.tauRows i live).2,mem_weightedSites.mpr ⟨i,live,rfl⟩⟩
  simp [tauSelector,w]

private theorem tauSelector_sites (C : JointBandCensus y f e τ W Q U J) :
    weightedSites y (tauSelector y f e Q (weightedSites y τ))=weightedSites y τ := by
  ext a
  constructor
  · intro ina
    obtain ⟨i,vi,rfl⟩ := mem_weightedSites.mp ina
    have w : tripleLabel y f e i∈tauLabels Q (weightedSites y τ) := by
      by_contra h
      exact vi (by simp [tauSelector,h])
    exact w.2.2
  · intro ina
    obtain ⟨i,ti,e⟩ := mem_weightedSites.mp ina
    exact mem_weightedSites.mpr ⟨i,by rw [tauSelector_one C ti];exact one_ne_zero,e⟩

private theorem tauSelector_on (T : Finset K) :
    OnLabels (tripleLabel y f e) (tauLabels Q T) (completeOrbit y (tauSelector y f e Q T)) := by
  rintro _ ⟨P,rfl⟩ i off
  simp [weightedEval_apply,tauSelector,off]

private theorem tauSelector_as_blocks (T : Finset K) (P : K[X]) :
    weightedEval y (tauSelector y f e Q T) P =
      ∑ a∈T, P.eval a • (labelIndicator (tripleLabel y f e) (a,Q.eval a,0) : Fin s→K) := by
  ext i
  rw [weightedEval_apply,Finset.sum_apply]
  by_cases on : tripleLabel y f e i∈tauLabels Q T
  · have ey : y i∈T := on.2.2
    have ef : f i=Q.eval (y i) := on.2.1
    have ez : e i=0 := on.1
    rw [show tauSelector y f e Q T i=1 by simp [tauSelector,on],mul_one,
      Finset.sum_eq_single_of_mem (y i) ey]
    · simp [labelIndicator,tripleLabel,ef,ez]
    · intro a _ h
      have no : tripleLabel y f e i≠(a,Q.eval a,0) :=
        fun eq=>h (congrArg Prod.fst eq).symm
      simp [labelIndicator,no]
  · rw [show tauSelector y f e Q T i=0 by simp [tauSelector,on],mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have no : tripleLabel y f e i≠(a,Q.eval a,0) := by
      intro eq
      exact on (eq.symm ▸ (show (a,Q.eval a,0)∈tauLabels Q T from ⟨rfl,rfl,ha⟩))
    simp [labelIndicator,no]

private theorem tauSelector_orbit_annih (C : JointBandCensus y f e τ W Q U J) (T : Finset K) :
    completeOrbit y (tauSelector y f e Q T)≤annih U := by
  rintro _ ⟨P,rfl⟩
  rw [tauSelector_as_blocks]
  exact (annih U).sum_mem (fun a _=>(annih U).smul_mem _ (C.indicator _))

private theorem tau_orbit_annih_selector (C : JointBandCensus y f e τ W Q U J)
    (mass : ∀ a,clockMass y τ a=0) :
    completeOrbit y τ≤annih (completeOrbit y (tauSelector y f e Q (weightedSites y τ))) := by
  rintro _ ⟨P,rfl⟩
  apply mem_annih.mpr
  rintro _ ⟨R,rfl⟩
  have point : row (weightedEval y τ P) (weightedEval y (tauSelector y f e Q (weightedSites y τ)) R)
      =∑ i,τ i*(P.eval (y i)*R.eval (y i)) := by
    rw [row_apply,dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp only [weightedEval_apply]
    by_cases zero : τ i=0
    · simp [zero]
    · rw [tauSelector_one C zero,mul_one]
      ring
  rw [point,weighted_sum_by_clock y τ (fun a=>P.eval a*R.eval a)]
  exact Finset.sum_eq_zero (fun a _=>by rw [mass a,zero_mul])

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Every vanished site sum buys a *second* independent block direction.
Individual signed entries may still be nonzero. -/
theorem JointBandCensus.cancelled_rank (C : JointBandCensus y f e τ W Q U J)
    (mass : ∀ a,clockMass y τ a=0) :
    finrank K U+finrank K J+2*(weightedSites y τ).card+(weightedSites y W).card≤s := by
  let T := weightedSites y τ
  let V := completeOrbit y τ
  let I := completeOrbit y (tauSelector y f e Q T)
  have orth : V≤annih I := tau_orbit_annih_selector C mass
  have dis : V⊓I=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    rw [eq_zero_of_self_row_zero (mem_annih.mp (orth hv.1) _ hv.2)]
    exact (⊥ : Submodule K (Fin s→K)).zero_mem
  have dv := Submodule.finrank_sup_add_finrank_inf_eq V I
  have vRank : finrank K V=T.card := completeOrbit_rank y τ
  have iRank : finrank K I=T.card := by
    change finrank K (completeOrbit y (tauSelector y f e Q T))=T.card
    rw [completeOrbit_rank,tauSelector_sites C]
  rw [dis,finrank_bot,add_zero,vRank,iRank] at dv
  obtain ⟨st,sr,tr⟩ := label_separations Q T (weightedSites y W)
  have support : OnLabels (tripleLabel y f e) (tauLabels Q T) (V⊔I) :=
    onLabels_same_sup C.tau_on (tauSelector_on T)
  have dims := finrank_supported_triple C.core_on support C.contrast_on st sr tr
  have vk : V⊔I≤annih U := sup_le (completeOrbit_annih C.clockStable C.tauOrth)
    (tauSelector_orbit_annih C T)
  have le := Submodule.finrank_mono
    (sup_le (sup_le C.coreOrth vk) (completeOrbit_annih C.clockStable C.contrastOrth))
  rw [dims,dv,completeOrbit_rank] at le
  have all := finrank_annih U
  rw [Fintype.card_fin] at all
  change finrank K U+finrank K J+2*T.card+(weightedSites y W).card≤s
  omega

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
