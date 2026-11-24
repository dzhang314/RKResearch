module

public import RKCert.TableauHermiteGain
public import RKCert.UniformERK
public import RKCert.HeadChart

@[expose] public section

/-! # Actual order-twelve forward and reverse saturation

The single `5 ≤ finrank (F 5)` input isolates the grade-five surplus from
the finite order-twelve equality analysis. All flags here are actual
stage/row spaces of the original tableau, including its zero weights. -/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired Module
variable {K : Type*} [Field K] [CharZero K]

def trim (A : Fin (s+1) → Fin (s+1) → K) (i j : Fin s) : K :=
  A i.castSucc j.castSucc

omit [CharZero K] in
theorem trim_strict {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) : StrictLower (trim A) := by
  intro i j h
  exact ha i.castSucc j.castSucc h

omit [CharZero K] in
theorem stageWeight_trim {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) (t : Tree) (i : Fin s) :
    stageWeight (trim A) t i = stageWeight A t i.castSucc := by
  induction t generalizing i with
  | leaf => rfl
  | attach t r ht hr =>
    simp only [stageWeight]
    rw [hr,Fin.sum_univ_castSucc,ha i.castSucc (Fin.last s) (by simp),zero_mul,add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ht]
    rfl

omit [CharZero K] in
theorem order_trim {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)} {p:ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hb : b (Fin.last s)=0) :
    HasTreeOrderAtLeast (trim A) (fun i => b i.castSucc) p := by
  intro t ht
  have h := ho t ht
  unfold weight at h ⊢
  rw [Fin.sum_univ_castSucc,hb,zero_mul,add_zero] at h
  simpa only [stageWeight_trim ha] using h

omit [CharZero K] in
theorem backward_exact_dim (U : Submodule K (Vec K s)) :
    finrank K U + finrank K (annih U)=s := by
  let f : Vec K s ≃ₗ[K] Module.Dual K (Vec K s) :=
    LinearEquiv.ofBijective rowL ⟨rowL_inj,rowL_surj⟩
  let g : annih U ≃ₗ[K] U.dualAnnihilator :=
    f.submoduleMap (annih U) |>.trans (LinearEquiv.ofEq _ _ (by
      change (annih U).map rowL=U.dualAnnihilator
      exact Submodule.map_comap_eq_of_surjective rowL_surj _))
  rw [g.finrank_eq]
  simpa only [Vec,Module.finrank_fin_fun] using Subspace.finrank_add_finrank_dualAnnihilator_eq U

omit [CharZero K] in
theorem backward_exact_of_ranks {A : Fin s → Fin s → K} {b : Vec K s} {j n : ℕ}
    (ho : HasTreeOrderAtLeast A b 12) (hj : j+n+2≤12)
    (he : finrank K (treeSpace A j)+finrank K (back A b n)=s) :
    back A b n=annih (treeSpace A j) := by
  have h := backward_exact_dim (treeSpace A j)
  exact Submodule.eq_of_le_of_finrank_le (back_annih ho j n hj) (by omega)

theorem seventeen_of_five {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (h5 : 5≤finrank K (zeroSpace A 5)) :
    17≤s := by
  have hp : 0<s := by have h := explicit_order_le_stages ha ho; omega
  have hF := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha (explicit_separated ha ho (q:=6) (by decide) hp)
      (j:=5) (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at hF
  have hE := explicit_treeSpace_rank ha ho (q:=6) (by decide) hp
  have hB := backward_count ha ho 6 4 (by decide)
  omega

/-- This is used to prevent the argument from accidentally treating a zero
weight at the final physical stage as a nonzero terminal functional. -/
theorem last_weight_of_five_surplus
    (surplus : ∀ {s : ℕ} {A : Fin s → Fin s → K} {b : Vec K s},
      StrictLower A → HasTreeOrderAtLeast A b 12 → 5≤finrank K (zeroSpace A 5))
    {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : s+1≤17) :
    b (Fin.last s)≠0 := by
  intro hz
  have ht := trim_strict ha
  have hh := order_trim ha ho hz
  have h17 := seventeen_of_five ht hh (surplus ht hh)
  omega

structure Saturation (A : Fin (s+1) → Fin (s+1) → K) (b : Vec K (s+1)) : Prop where
  size : s+1=17
  f5 : finrank K (zeroSpace A 5)=5
  f6 : finrank K (zeroSpace A 6)=6
  e6 : finrank K (treeSpace A 6)=13
  backZero : backSeed1 A b=0
  backRank : ∀ n≤4, finrank K (back A b n)=n
  back4 : back A b 4=annih (treeSpace A 6)
  caps : ∀ j≤10, finrank K (treeSpace A j)≤j+7

theorem saturation {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12)
    (hf : 5≤finrank K (zeroSpace A 5)) (hs : s+1≤17) : Saturation A b := by
  have hp : 0<s+1 := by omega
  have hF := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha (explicit_separated ha ho (q:=6) (by decide) hp)
      (j:=5) (by decide) (by decide))
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at hF
  have hE := explicit_treeSpace_rank ha ho (q:=6) (by decide) hp
  have hB := backward_count ha ho 6 4 (by decide)
  have hsize : s+1=17 := by omega
  have hf5 : finrank K (zeroSpace A 5)=5 := by omega
  have hf6 : finrank K (zeroSpace A 6)=6 := by omega
  have he6 : finrank K (treeSpace A 6)=13 := by omega
  have hb0 : finrank K (back A b 0)=0 := by omega
  have hb0' : back A b 0=⊥ := Submodule.finrank_eq_zero.mp hb0
  have hz : backSeed1 A b=0 := by
    have hh : backSeed1 A b ∈ back A b 0 := Submodule.subset_span (Set.mem_singleton _)
    rwa [hb0',Submodule.mem_bot] at hh
  have u4 := finrank_annih_le (back_annih ho 6 4 (by decide))
  have h01 := Submodule.finrank_lt_finrank_of_lt (back_lt_succ ha ho (n:=0) (by decide))
  have h12 := Submodule.finrank_lt_finrank_of_lt (back_lt_succ ha ho (n:=1) (by decide))
  have h23 := Submodule.finrank_lt_finrank_of_lt (back_lt_succ ha ho (n:=2) (by decide))
  have h34 := Submodule.finrank_lt_finrank_of_lt (back_lt_succ ha ho (n:=3) (by decide))
  change finrank K (back A b 0)<finrank K (back A b 1) at h01
  change finrank K (back A b 1)<finrank K (back A b 2) at h12
  change finrank K (back A b 2)<finrank K (back A b 3) at h23
  change finrank K (back A b 3)<finrank K (back A b 4) at h34
  have hr : ∀ n≤4, finrank K (back A b n)=n := by intro n hn;interval_cases n <;> omega
  refine ⟨hsize,hf5,hf6,he6,hz,hr,backward_exact_of_ranks (j:=6) (n:=4) ho (by decide) (by rw [he6,hr 4 (by decide)];omega),?_⟩
  intro j hj
  have h := backward_count ha ho j (10-j) (by omega)
  omega

omit [CharZero K] in
theorem tail_col_mem {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (hs : Saturation A b)
    {i j : Fin (s+1)} (hi : b i≠0) (hl : ∀ k, i<k → b k=0) (hj : i≤j) :
    (Pi.single j 1 : Vec K (s+1)) ∈ treeSpace A 6 := by
  apply row_annih_test
  intro w hw
  rw [← hs.back4] at hw
  have he := back_vanish ha hi hl hs.backZero 4 hw j hj
  simp [row_apply,Pi.single_apply,Finset.sum_ite_eq',he]

omit [CharZero K] in
theorem active_last_normal {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (hs : Saturation A b) {i : Fin (s+1)}
    (hi : b i≠0) (hl : ∀ k, i<k → b k=0) : nodes A i=1 := by
  have h := last_mirror_zero ha hi hl hs.backZero
  change 1-nodes A i=0 at h
  exact (sub_eq_zero.mp h).symm

omit [CharZero K] in
theorem f5_vanish_at_last_active {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b)
    {i : Fin (s+1)} (hi : b i≠0) (hl : ∀ k, i<k → b k=0)
    {f : Vec K (s+1)} (hf : f∈zeroSpace A 5) : f i=0 := by
  have e : (Pi.single i 1 : Vec K (s+1))∈treeSpace A 6 := tail_col_mem ha hs hi hl le_rfl
  have h := probe_zeroSpace ho (by decide : 0+(5+6)+1≤12) (zeroSpace_mul_treeSpace ho (by decide) hf e)
  have he : f*Pi.single i (1:K)=Pi.single i (f i) := by
    classical ext j; by_cases hj:j=i <;> simp [hj]
  rw [he] at h
  have hp : b i*f i=0 := by
    classical simpa [probe,row_apply,Pi.single_apply,Finset.sum_ite_eq',mul_ite] using h
  exact (mul_eq_zero.mp hp).resolve_left hi

theorem f5_noninvariant {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b) :
    ¬ (zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5 := by
  intro h
  have hh := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=5) (by decide) (zeroSpace A 5)
    le_rfl (fun f hf => h (Submodule.mem_map_of_mem hf))
  change finrank K (zeroSpace A 5)+3≤finrank K (zeroSpace A 6) at hh
  have hf5 := hs.f5
  have hf6 := hs.f6
  omega

theorem f6_vanish_at_last_active {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b)
    {i : Fin (s+1)} (hi : b i≠0) (hl : ∀ k, i<k → b k=0)
    {f : Vec K (s+1)} (hf : f∈zeroSpace A 6) : f i=0 := by
  have hh : finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1 := by rw [hs.f5,hs.f6]
  rw [Clock.ordinary_step hh (f5_noninvariant ha ho hs)] at hf
  obtain ⟨v,hv,u,⟨w,hw,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hf
  simp [f5_vanish_at_last_active ha ho hs hi hl hv,f5_vanish_at_last_active ha ho hs hi hl hw]

end RKCert.Paired.OrderTwelve
