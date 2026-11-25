module

public import RKCert.ReviewedNative.FirstSeedWidePhysical

@[expose] public section

/-! # The full first-seed and output-invisible forward carrier

This is the simultaneous physical support kernel. Unlike the marked
quadratic cover, no last coordinate is compensated or removed. The
inclusion in the actual forward defect space uses exact Cauchy moments. -/
namespace RKResearch.Certified.Graded.Reverse.FirstWide
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p m h : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

def visible (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (i : Fin s) : Prop :=
  firstSeed A b i≠0∨b i≠0

abbrev carrier (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) :
    Submodule K (Fin s→K) := (diag (firstSeed A b)).ker ⊓ (diag b).ker

theorem mem_carrier_iff {v : Fin s→K} :
    v∈carrier A b ↔ ∀i,visible A b i→v i=0 := by
  rw [Submodule.mem_inf,LinearMap.mem_ker,LinearMap.mem_ker]
  constructor
  · rintro ⟨d,e⟩ i (nz|nz)
    · exact (mul_eq_zero.mp (show firstSeed A b i*v i=0 from congrFun d i)).resolve_left nz
    · exact (mul_eq_zero.mp (show b i*v i=0 from congrFun e i)).resolve_left nz
  · intro f
    refine ⟨funext fun i => ?_,funext fun i => ?_⟩
    · change firstSeed A b i*v i=0
      by_cases off : firstSeed A b i=0
      · rw [off,zero_mul]
      · rw [f i (Or.inl off),mul_zero]
    · change b i*v i=0
      by_cases off : b i=0
      · rw [off,zero_mul]
      · rw [f i (Or.inr off),mul_zero]

theorem carrier_clock : (carrier A b).map (diag (nodes A))≤carrier A b := by
  rintro _ ⟨v,hv,rfl⟩
  exact mem_carrier_iff.mpr (fun i hi => by rw [diag_apply,mem_carrier_iff.mp hv i hi,mul_zero])

set_option maxRecDepth 3500 in
set_option maxHeartbeats 600000 in
theorem Cover.carrier_pure (B : Cover A b m h) (ho : HasOrder p A b)
    (pay : 2*m+1≤p) : carrier A b≤zeroSpace A m := by
  intro v hv
  have vanish := mem_carrier_iff.mp hv
  have inTree : v∈treeSpace A m := by
    rw [←annih_annih (treeSpace A m)]
    apply mem_annih.mpr
    intro u hu
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases z : firstSeed A b i=0
    · rw [B.support hu z,mul_zero]
    · rw [vanish i (Or.inl z),zero_mul]
  rw [treeSpace_coeff_sup ho (by omega : m+1≤p)] at inTree
  obtain ⟨ev,hev,w,hw,e⟩ := Submodule.mem_sup.mp inTree
  obtain ⟨a,rfl⟩ := hev
  have probes (i : Fin (m+1)) : probe A b i.val v=0 := by
    simp only [probe,row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases z : b j=0
    · rw [z,zero_mul,zero_mul]
    · rw [vanish j (Or.inr z),mul_zero]
  have tests (i : Fin (m+1)) : ∑ j : Fin (m+1), a j/((i.val+j.val+1:ℕ):K)=0 := by
    have P := probes i
    have q : probe A b i.val w=0 := probe_zeroSpace ho (by have := i.isLt; omega) hw
    rw [←e,map_add,probe_coeffEval ho (by have := i.isLt; omega),q,add_zero] at P
    exact P
  have za := moments_detect ho (d:=1) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a tests
  rw [←e,show a=0 from funext za,map_zero,zero_add]
  exact hw

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem Cover.grade_four_in_carrier (B : Cover A b m h)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b) (wide : 4≤h)
    (pay : m+h+2≤p) (portPay : m+9≤p) (meanPay : 12≤p) :
    zeroSpace A 4≤carrier A b := by
  intro f hf
  obtain ⟨Q,P,qd,pd,fit⟩ := two_traces ho B hf (by decide) pay wide
  have van := ordered_invisible_given_reps ha ho B Q P qd (by omega) (by omega)
    (by omega) (by omega) fit
  refine mem_carrier_iff.mpr fun i vis => ?_
  rcases vis with nz|nz
  · exact (mul_eq_zero.mp (van i).1).resolve_left nz
  · exact (mul_eq_zero.mp (van i).2).resolve_left nz

end Ordered
end
end RKResearch.Certified.Graded.Reverse.FirstWide
