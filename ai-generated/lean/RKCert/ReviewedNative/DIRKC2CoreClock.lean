module

public import RKCert.ReviewedNative.ClockSignatureFold
public import RKCert.ReviewedNative.C2CubicFlag
public import RKCert.ReviewedNative.DIRKGradeSixHeads
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # A genuine single physical core mask in the invariant C(2) band -/
namespace RKResearch.Certified.Graded.OuterHead

open Polynomial RKCert.OneEscape RKCert.Endpoint HeadFiber.Signature
open scoped Matrix Classical

variable {K : Type*} [Field K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
variable {b : Fin s → K} {U : Submodule K (Fin s → K)}

/-- The exact C(2) cubic core: one nonunital indicator supported at one
numerical clock, preserving the actual stage rows of the reviewed tableau. -/
structure CoreMask (A : Matrix (Fin s) (Fin s) K) (U : Submodule K (Fin s → K)) where
  clock : K
  mask : Fin s → K
  span_eq : U = K ∙ mask
  binary : ∀ i, mask i=0 ∨ mask i=1
  clock_on_mask : ∀ i, mask i≠0 → nodes A i=clock

theorem CoreMask.mem (C : CoreMask A U) : C.mask∈U :=
  C.span_eq.ge (Submodule.mem_span_singleton_self _)

theorem CoreMask.outside_zero (C : CoreMask A U) {i : Fin s} (outside : C.mask i=0)
    {v : Fin s → K} (hv : v∈U) : v i=0 := by
  rw [C.span_eq] at hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp [outside]

/-- A rank-one multiplicatively closed C(2) F3, invariant under the
true clock, is exactly one physical 0/1 mask at a single clock. -/
theorem c2_core_mask (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 3≤p)
    (c₂ : monomialStageDefect A 1=0)
    (closed : ∀ u∈zeroSpace A 3, ∀ v∈zeroSpace A 3, u*v∈zeroSpace A 3)
    (stable : (zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3) :
    Nonempty (CoreMask A (zeroSpace A 3)) := by
  let g := monomialStageDefect A 2
  have gmem : g∈zeroSpace A 3 := monomialStageDefect_mem A 2
  have nz : g≠0 := (dirk_grade_three_of_C2 ha ho pay c₂).1
  have gg := closed _ gmem _ gmem
  have cg := stable (Submodule.mem_map_of_mem gmem)
  have sp : zeroSpace A 3=K ∙ g := zeroSpace_three_of_C2 A c₂
  rw [sp] at gg cg
  obtain ⟨t,et⟩ := Submodule.mem_span_singleton.mp gg
  obtain ⟨u,eu⟩ := Submodule.mem_span_singleton.mp cg
  have ve (i : Fin s) (ni : g i≠0) : t=g i := by
    apply mul_right_cancel₀ ni
    exact congrFun et i
  have ec (i : Fin s) (ni : g i≠0) : u=nodes A i := by
    apply mul_right_cancel₀ ni
    exact congrFun eu i
  have tn : t≠0 := by
    intro zero
    apply nz
    ext i
    by_cases e : g i=0
    · exact e
    · exact (ve i e).symm.trans zero
  let e := t⁻¹ • g
  refine ⟨⟨u,e,?_,?_,?_⟩⟩
  · rw [sp,show e=t⁻¹•g from rfl,Submodule.span_singleton_smul_eq (inv_ne_zero tn).isUnit]
  · intro i
    by_cases z : g i=0
    · exact Or.inl (by simp [e,z])
    · right
      exact (by change t⁻¹*g i=1; rw [←ve i z,inv_mul_cancel₀ tn])
  · intro i eno
    have gne : g i≠0 := by intro h; exact eno (by simp [e,h])
    exact (ec i gne).symm

/-- Mask the scalar by one genuine cubic-core vector, without ever
changing the tableau. The single-clock fact makes the masking constant
the literal evaluation at the core clock. -/
noncomputable def CoreMask.scalar (C : CoreMask A U) (P : K[X]) : Fin s → K :=
  evalNodes A P - P.eval C.clock • C.mask

theorem CoreMask.scalar_defect (C : CoreMask A U) (P : K[X]) :
    C.scalar P-evalNodes A P∈U := by
  unfold CoreMask.scalar
  convert U.neg_mem (U.smul_mem (P.eval C.clock) C.mem) using 1
  abel

theorem CoreMask.scalar_inside (C : CoreMask A U) (P : K[X]) {i : Fin s} (ni : C.mask i≠0) :
    C.scalar P i=0 := by
  have h := (C.binary i).resolve_left ni
  simp [CoreMask.scalar,C.clock_on_mask i ni,h]

theorem CoreMask.scalar_outside (C : CoreMask A U) (P : K[X]) {i : Fin s}
    (outside : C.mask i=0) : C.scalar P i=P.eval (nodes A i) := by
  simp [CoreMask.scalar,outside]

/-- The real nonzero numerical clocks occurring outside the cubic core. -/
noncomputable def outsideSites (A : Matrix (Fin s) (Fin s) K) (e : Fin s → K) : Finset K :=
  (Finset.univ.filter (fun i => e i=0 ∧ nodes A i≠0)).image (nodes A)

/-- The shifted paid Cauchy test already counts four exterior clock
sites. A failed block cannot be wholly covered by the single true mask. -/
theorem outsideSites_card (ho : HasOrder p A b) (pay : 8≤p)
    (C : CoreMask A U) (inside : U≤zeroSpace A 3)
    (stable : U.map (diag (nodes A))≤U) :
    4≤(outsideSites A C.mask).card := by
  have m := clock_mask_invariant (fun v (hv : v∈U) => stable (Submodule.mem_map_of_mem hv))
  have n := paid_failed_clock_blocks ho (by omega : 3+1≤p) inside m (r:=4) (by omega)
  refine n.trans (Finset.card_le_card ?_)
  intro a ha
  obtain ⟨an,fail⟩ := mem_failedNodes.mp ha
  by_contra no
  apply fail
  refine ⟨C.mask,C.mem,fun i _ ci => ?_⟩
  apply (C.binary i).resolve_left
  intro im
  apply no
  exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,im,ci.symm ▸ an⟩,ci⟩

/-- One first-occurrence list of exterior stage clocks. The prefix coverage
is over all physical rows, not just positions with a particular head value. -/
structure ClockDebuts (A : Matrix (Fin s) (Fin s) K) (e : Fin s → K) (n : ℕ) where
  row : Fin n → Fin s
  inc : StrictMono row
  clock_inj : Function.Injective (nodes A ∘ row)
  outside : ∀ k, e (row k)=0
  nonzero : ∀ k, nodes A (row k)≠0
  cover : ∀ k j, j < row k → e j=0 → nodes A j≠0 →
    ∃ l : Fin n, l < k ∧ nodes A (row l)=nodes A j

theorem clockDebuts_of_card {e : Fin s → K} {n : ℕ} (N : n≤(outsideSites A e).card) :
    Nonempty (ClockDebuts A e n) := by
  classical
  let c := nodes A
  let S := (Finset.univ : Finset (Fin s)).filter (fun i => first c e i=i ∧ e i=0 ∧ c i≠0)
  have sub : outsideSites A e ⊆ S.image c := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨z,nz⟩ := (Finset.mem_filter.mp hi).2
    have ec : c (first c e i)=c i := congrArg Prod.fst (first_signature c e i)
    have ee : e (first c e i)=e i := congrArg Prod.snd (first_signature c e i)
    exact Finset.mem_image.mpr ⟨first c e i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,first_idempotent c e i,ee.trans z,ec.symm ▸ nz⟩,ec⟩
  have hN : n≤S.card := N.trans ((Finset.card_le_card sub).trans Finset.card_image_le)
  let emb := S.orderEmbOfFin rfl
  let d (k : Fin n) := emb (Fin.castLE hN k)
  have mono : StrictMono d := emb.strictMono.comp (Fin.strictMono_castLE hN)
  have spec (k : Fin n) : first c e (d k)=d k ∧ e (d k)=0 ∧ c (d k)≠0 :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl (Fin.castLE hN k))).2
  refine ⟨⟨d,mono,?_,fun k => (spec k).2.1,fun k => (spec k).2.2,?_⟩⟩
  · intro i j eq
    change c (d i)=c (d j) at eq
    apply mono.injective
    have h : (c (d i),e (d i))=(c (d j),e (d j)) :=
      Prod.ext eq ((spec i).2.1.trans (spec j).2.1.symm)
    exact (spec i).1.symm.trans ((first_congr h).trans (spec j).1)
  · intro k j jd ej nj
    let l := first c e j
    have lc : c l=c j := congrArg Prod.fst (first_signature c e j)
    have le : e l=e j := congrArg Prod.snd (first_signature c e j)
    have pos : l < d k := (first_le c e j).trans_lt jd
    have ls : l∈S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,first_idempotent c e j,le.trans ej,lc.symm ▸ nj⟩
    have lm : l∈Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact ls
    obtain ⟨t,et⟩ := lm
    have tl : t < Fin.castLE hN k := emb.lt_iff_lt.mp (et.symm ▸ pos)
    have tn : t.val<n := lt_trans (show t.val<k.val from tl) k.isLt
    exact ⟨⟨t.val,tn⟩,tl, (congrArg c et).trans lc⟩

end RKResearch.Certified.Graded.OuterHead
