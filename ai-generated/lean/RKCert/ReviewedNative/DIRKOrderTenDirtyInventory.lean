module

public import RKCert.ReviewedNative.DIRKOrderTenSaturation
public import RKCert.ReviewedNative.GradedProducts
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Signed DIRK10 cubic-defect label inventory
Repeated clocks are counted only after grouping; an unweighted dirty
row does not count as a live label, but it still spends a physical row.
-/
namespace RKResearch.Certified.Graded.CrossedOrderTen

open RKResearch Module FiniteRootedTree Reverse Polynomial
open scoped Matrix BigOperators Classical
noncomputable section
variable {K : Type*} [Field K]

/-- Individually active rows with nonzero cubic defect. We use the
unscaled native defect (three times the classical defect). -/
def activeDirtyRows {ι : Type*} [Fintype ι] (b g : ι → K) : Finset ι :=
  Finset.univ.filter (fun i => b i≠0 ∧ g i≠0)

/-- Ghost dirty rows, excluded from the labels but not the stage count. -/
def ghostDirtyRows {ι : Type*} [Fintype ι] (b g : ι → K) : Finset ι :=
  Finset.univ.filter (fun i => b i=0 ∧ g i≠0)

def dirtyClockLabels {ι : Type*} [Fintype ι] (c b g : ι → K) : Finset K :=
  (activeDirtyRows b g).image c

private def fiber {ι : Type*} (D : Finset ι) (c : ι → K) (x : K) : Finset ι :=
  D.filter (fun i => c i=x)

omit [Field K] in
private theorem mem_fiber {ι : Type*} {D : Finset ι} {c : ι→K} {x : K} {i : ι} :
    i ∈ fiber D c x ↔ i∈D ∧ c i=x := by simp [fiber]


private def nodalHull (D : Finset K) : K[X] := ∏ x∈D,(X-C x)

private theorem natDegree_nodalHull (D : Finset K) : (nodalHull D).natDegree=D.card :=
  natDegree_finsetProd_X_sub_C_eq_card D id

private theorem monic_nodalHull (D : Finset K) : (nodalHull D).Monic :=
  monic_prod_X_sub_C id D

private theorem nodalHull_eval_of_mem {D : Finset K} {x : K} (hx : x∈D) :
    (nodalHull D).eval x=0 := by
  rw [nodalHull,eval_prod]
  apply Finset.prod_eq_zero hx
  simp

private theorem coeffEval_poly {ι : Type*} [Fintype ι] (A : Matrix ι ι K)
    (P : K[X]) {n : ℕ} (h : P.natDegree≤n) (i : ι) :
    coeffEval A n (fun j=>P.coeff j.val) i=P.eval (nodes A i) := by
  rw [coeffEval_apply,Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,normTree_clockTree]
  rw [Fin.sum_univ_eq_sum_range (fun j => P.coeff j*(nodes A i)^j)]
  conv_rhs => rw [P.as_sum_range' (n+1) (by omega)]
  simp only [eval_finsetSum,eval_monomial]

private theorem polynomial_dark {ι : Type*} (D : Finset ι) (c w : ι→K) {k : ℕ}
    (m : ∀ n≤k, (∑ i∈D,w i*(c i)^n)=0) (P : K[X])
    (dp : P.natDegree≤k) : (∑ i∈D,w i*P.eval (c i))=0 := by
  have expansion (x : K) : P.eval x =
      ∑ n∈Finset.range (k+1),P.coeff n*x^n := by
    conv_lhs => rw [P.as_sum_range' (k+1) (by omega)]
    simp only [eval_finsetSum,eval_monomial]
  simp only [expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  calc
    _ = P.coeff n*(∑ i∈D,w i*(c i)^n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [m n (by simpa using hn),mul_zero]

private theorem all_fibers_dark {ι : Type*} (D : Finset ι) (c w : ι→K) {k : ℕ}
    (card : (D.image c).card≤k+1)
    (m : ∀ n≤k, (∑ i∈D,w i*(c i)^n)=0)
    (x : K) (hx : x∈D.image c) : (∑ i∈fiber D c x,w i)=0 := by
  let S := (D.image c).erase x
  let P := nodalHull S
  have notx : x∉S := Finset.notMem_erase x _
  have deg : P.natDegree≤k := by
    dsimp [P,S]
    rw [natDegree_nodalHull,Finset.card_erase_of_mem hx]
    omega
  have nz : P.eval x≠0 := by
    rw [show P=nodalHull S from rfl,nodalHull,eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    simp only [eval_sub,eval_X,eval_C,sub_ne_zero]
    exact fun e => notx (e ▸ hz)
  have z := polynomial_dark D c w m P deg
  have support : (∑ i∈fiber D c x,w i*P.eval (c i)) =
      ∑ i∈D,w i*P.eval (c i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi off
    have ne : c i≠x := fun e => off (mem_fiber.mpr ⟨hi,e⟩)
    rw [nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨ne,Finset.mem_image_of_mem c hi⟩),mul_zero]
  have mass : (∑ i∈fiber D c x,w i)*P.eval x=0 := by
    rw [Finset.sum_mul,←z,←support]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(mem_fiber.mp hi).2]
  exact (mul_eq_zero.mp mass).resolve_right nz

private theorem dark_pair {ι : Type*} [Fintype ι] {c b g : ι→K} {x : K}
    (card : (fiber (activeDirtyRows b g) c x).card=2)
    (m1 : (∑ i∈fiber (activeDirtyRows b g) c x,b i*g i)=0)
    (m2 : (∑ i∈fiber (activeDirtyRows b g) c x,b i*(g i)^2)=0) :
    (∑ i∈fiber (activeDirtyRows b g) c x,b i)=0 := by
  obtain ⟨i,j,ne,two⟩ := Finset.card_eq_two.mp card
  have hi : i ∈ activeDirtyRows b g := (mem_fiber.mp (by rw [two]; simp)).1
  have hj : j ∈ activeDirtyRows b g := (mem_fiber.mp (by rw [two]; simp)).1
  obtain ⟨bi,gi⟩ : b i≠0 ∧ g i≠0 := (Finset.mem_filter.mp hi).2
  obtain ⟨bj,gj⟩ : b j≠0 ∧ g j≠0 := (Finset.mem_filter.mp hj).2
  rw [two,Finset.sum_pair ne] at m1 m2 ⊢
  have e : (b i*g i)*(g i-g j)=0 := by linear_combination m2 - g j*m1
  have dg := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (mul_ne_zero bi gi))
  apply (mul_eq_zero.mp (show (b i+b j)*g j=0 by rw [dg] at m1; linear_combination m1)).resolve_right gj

private theorem each_fiber_two {ι : Type*} [Fintype ι] {c b g : ι→K}
    (x : K) (hx : x∈dirtyClockLabels c b g)
    (h : (∑ i∈fiber (activeDirtyRows b g) c x,b i*g i)=0) :
    2≤(fiber (activeDirtyRows b g) c x).card := by
  obtain ⟨i,hi,ci⟩ := Finset.mem_image.mp hx
  have live : i∈fiber (activeDirtyRows b g) c x := mem_fiber.mpr ⟨hi,ci⟩
  have pos := Finset.card_pos.mpr ⟨i,live⟩
  by_contra! h'
  obtain ⟨j,single⟩ := Finset.card_eq_one.mp (by omega :
    (fiber (activeDirtyRows b g) c x).card=1)
  have hd : j∈activeDirtyRows b g := (mem_fiber.mp (by rw [single]; simp)).1
  obtain ⟨bj,gj⟩ : b j≠0 ∧ g j≠0 := (Finset.mem_filter.mp hd).2
  rw [single,Finset.sum_singleton] at h
  exact (mul_ne_zero bj gj) h

/-- Choose exactly two distinct physical rows from each active dirty
fiber. Every remaining member of the fiber, if any, is uncharged. -/
private theorem choose_pairs {ι : Type*} [Fintype ι] {c b g : ι→K}
    (m : ∀ x∈dirtyClockLabels c b g, (∑ i∈fiber (activeDirtyRows b g) c x,b i*g i)=0) :
    ∃ (T : Finset ι), T⊆activeDirtyRows b g ∧
      T.card=2*(dirtyClockLabels c b g).card ∧
      ∀ x, (fiber T c x).card≤2 := by
  let S := dirtyClockLabels c b g
  have choose (x : S) : ∃ U : Finset ι, U⊆fiber (activeDirtyRows b g) c x.val ∧ U.card=2 :=
    Finset.exists_subset_card_eq (each_fiber_two x.val x.property (m x.val x.property))
  choose U hU cardU using choose
  let T := S.attach.biUnion U
  have disj : (S.attach : Set S).PairwiseDisjoint U := by
    intro x hx y hy ne
    apply Finset.disjoint_left.mpr
    intro i hi hj
    apply ne
    exact Subtype.ext (((mem_fiber.mp (hU x hi)).2).symm.trans ((mem_fiber.mp (hU y hj)).2))
  have hcard : T.card=2*S.card := by
    rw [show T=S.attach.biUnion U from rfl,Finset.card_biUnion disj]
    simp [cardU,Nat.mul_comm]
  refine ⟨T,?_,hcard,?_⟩
  · intro i hi
    obtain ⟨x,_,e⟩ := Finset.mem_biUnion.mp hi
    exact (mem_fiber.mp (hU x e)).1
  · intro x
    by_cases hx : x∈S
    · let y : S := ⟨x,hx⟩
      rw [←cardU y]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨hit,ci⟩ := mem_fiber.mp hi
      obtain ⟨z,_,hiz⟩ := Finset.mem_biUnion.mp hit
      have eq : z=y := Subtype.ext (((mem_fiber.mp (hU z hiz)).2).symm.trans ci)
      rwa [←eq]
    · have no : fiber T c x=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hit,ci⟩ := mem_fiber.mp hi
        obtain ⟨z,_,hiz⟩ := Finset.mem_biUnion.mp hit
        have e : z.val=x := ((mem_fiber.mp (hU z hiz)).2).symm.trans ci
        exact hx (e ▸ z.property)
      simp [no]

private def rawMass {ι : Type*} [Fintype ι] (c b : ι→K) (x : K) : K :=
  ∑ i∈fiber Finset.univ c x,b i

private theorem group_raw {ι : Type*} [Fintype ι] (c b : ι→K) (f : K→K) :
    (∑ i,b i*f (c i))=∑ x∈Finset.univ.image c,rawMass c b x*f x := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ.image c) (g:=c)
    (fun i hi=>Finset.mem_image_of_mem c hi) (fun i=>b i*f (c i))]
  apply Finset.sum_congr rfl
  intro x _
  rw [rawMass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- A possible support containing the terminal clock 1 cannot fit
in five labels. Even mass cancellation at clock 1 is allowed. -/
private theorem six_possible_clocks {ι : Type*} [Fintype ι]
    {A : Matrix ι ι K} {b : ι→K} (ho : HasOrder 10 A b)
    (T : Finset K) (one : (1:K)∈T)
    (mass : ∀ x∉T, rawMass (nodes A) b x=0) : 6≤T.card := by
  by_contra! small
  let P := nodalHull (T.erase (1:K))
  let B := rawMass (nodes A) b 1 * P.eval 1
  have deg : P.natDegree≤4 := by
    dsimp [P]
    rw [natDegree_nodalHull,Finset.card_erase_of_mem one]
    omega
  let a : Fin 5→K := fun j => P.coeff j.val
  have con (k : ℕ) : probe A b k (coeffEval A 4 a)=B := by
    have eq : probe A b k (coeffEval A 4 a) = ∑ i,b i*((nodes A i)^k*P.eval (nodes A i)) := by
      simp only [probe,row_apply,dotProduct,a,coeffEval_poly A P deg]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    rw [eq,group_raw (nodes A) b (fun x => x^k*P.eval x)]
    rw [Finset.sum_eq_single (1:K)]
    · simp [B]
    · intro x _ ne
      by_cases h : x∈T
      · rw [nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨ne,h⟩),mul_zero,mul_zero]
      · rw [mass x h,zero_mul]
    · intro no
      have raw0 : rawMass (nodes A) b (1:K)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨iU,ci⟩ := mem_fiber.mp hi
        exact False.elim (no (ci ▸ Finset.mem_image_of_mem _ iU))
      rw [raw0,zero_mul]
  have paid (i : Fin 6) : (∑ j : Fin 5,a j/((i.val+j.val+1:ℕ):K))=B := by
    have e := con i.val
    rw [probe_coeffEval ho (by have :=i.isLt; omega)] at e
    exact e
  have z := paid_unanchored_constant_cauchy ho (n:=5) (by decide) a B paid
  have all := moments_detect ho (n:=5) (d:=1) (by decide) (by decide)
    (fun i j=>by have :=i.isLt;have :=j.isLt;omega) a
    (fun i=> by simpa only [Fin.val_castSucc,z] using paid i.castSucc)
  apply (monic_nodalHull (T.erase (1:K))).ne_zero
  ext j
  rw [coeff_zero]
  by_cases hi : j<5
  · exact all ⟨j,hi⟩
  · change P.coeff j=0
    exact coeff_eq_zero_of_natDegree_lt (by omega)

private theorem raw_outside_after_pairs {ι : Type*} [Fintype ι] {c b g : ι→K}
    (U : Finset ι) (sub : U⊆activeDirtyRows b g)
    (atMost : ∀ x,(fiber U c x).card≤2)
    (m1 : ∀ x∈dirtyClockLabels c b g,(∑ i∈fiber (activeDirtyRows b g) c x,b i*g i)=0)
    (m2 : ∀ x∈dirtyClockLabels c b g,(∑ i∈fiber (activeDirtyRows b g) c x,b i*(g i)^2)=0)
    (x : K) (off : x∉((Finset.univ \ (U∪ghostDirtyRows b g)).image c)) :
    rawMass c b x=0 := by
  let D := activeDirtyRows b g
  have use (i : ι) (ci : c i=x) : i∈U ∪ ghostDirtyRows b g := by
    by_contra no
    apply off
    exact Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,no⟩,ci⟩
  have cover : fiber D c x ⊆ fiber U c x := by
    intro i hi
    obtain ⟨hd,ci⟩ := mem_fiber.mp hi
    apply mem_fiber.mpr
    refine ⟨(Finset.mem_union.mp (use i ci)).resolve_right ?_,ci⟩
    intro hg
    exact (Finset.mem_filter.mp hd).2.1 ((Finset.mem_filter.mp hg).2.1)
  have mass : rawMass c b x=∑ i∈fiber D c x,b i := by
    symm
    apply Finset.sum_subset (fun i hi=>mem_fiber.mpr ⟨Finset.mem_univ _,(mem_fiber.mp hi).2⟩)
    intro i hi out
    rcases Finset.mem_union.mp (use i (mem_fiber.mp hi).2) with hu | hg
    · exact False.elim (out (mem_fiber.mpr ⟨sub hu,(mem_fiber.mp hi).2⟩))
    · exact (Finset.mem_filter.mp hg).2.1
  rw [mass]
  by_cases hx : x∈dirtyClockLabels c b g
  · have hi : 2≤(fiber D c x).card := each_fiber_two x hx (m1 x hx)
    have hu := (Finset.card_le_card cover).trans (atMost x)
    exact dark_pair (by change (fiber D c x).card=2; omega) (m1 x hx) (m2 x hx)
  · apply Finset.sum_eq_zero
    intro i hi
    exact False.elim (hx (by exact Finset.mem_image.mpr ⟨i,(mem_fiber.mp hi).1,(mem_fiber.mp hi).2⟩))

variable {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

private theorem last_cubic_clean (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (S : Saturated A b) : monomialStageDefect A 2 (Fin.last 10)=0 := by
  let t := Fin.last 10
  have ht : LastActive b t := ⟨S.last_live,fun j hj=>(not_lt_of_ge (Fin.le_last j) hj).elim⟩
  have inc := primitiveBack_annih ho 5 3 (by decide)
  have lo := dirk_primitiveBack_rank_gain ha ho (r:=1) (n:=3) (by decide) (by decide) (by decide)
  have cap := finrank_annih (treeSpace A 5)
  rw [Fintype.card_fin,S.e5] at cap
  have full : primitiveBack A b 3=annih (treeSpace A 5) := by
    apply Submodule.eq_of_le_of_finrank_le inc
    omega
  have H : coordinate t ∈ treeSpace A 5 := by
    rw [←annih_annih (treeSpace A 5),←full]
    apply mem_annih.mpr
    intro v hv
    have z := mem_tailZero.mp (ht.dirk_primitiveBack_tail ha S.d1 S.d2 3 hv) t le_rfl
    rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,z]
  let g := monomialStageDefect A 2
  have hG := zeroSpace_mul_treeSpace ho (by decide) (monomialStageDefect_mem A 2) H
  have out := probe_zeroSpace ho (k:=0) (by decide) hG
  have pro : g*coordinate t=g t • coordinate t := by
    classical
    ext i
    by_cases e : i=t
    · subst i
      simp [coordinate]
    · simp [coordinate,e]
  change probe A b 0 (g*coordinate t)=0 at out
  rw [pro,map_smul,smul_eq_mul] at out
  change g t*row _ (coordinate t)=0 at out
  rw [row_coordinate,pow_zero,mul_one] at out
  exact (mul_eq_zero.mp out).resolve_right S.last_live

private theorem dirty_moments (ho : HasOrder 10 A b) :
    (∀ k≤6,(∑ i∈activeDirtyRows b (monomialStageDefect A 2),
      (b i*monomialStageDefect A 2 i)*(nodes A i)^k)=0) ∧
    (∀ k≤3,(∑ i∈activeDirtyRows b (monomialStageDefect A 2),
      (b i*(monomialStageDefect A 2 i)^2)*(nodes A i)^k)=0) := by
  let g := monomialStageDefect A 2
  have gm : g∈zeroSpace A 3 := monomialStageDefect_mem A 2
  have g2 : g*g∈zeroSpace A 6 := zeroSpace_mul gm gm
  have read (l k : ℕ) (q : ℕ) (lp : l≠0) (pay : k+q+1≤10) (h : g^l∈zeroSpace A q) :
      (∑ i∈activeDirtyRows b g,(b i*(g i)^l)*(nodes A i)^k)=0 := by
    have out := probe_zeroSpace ho (k:=k) pay h
    rw [←out]
    trans ∑ i,(b i*(g i)^l)*(nodes A i)^k
    · apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      by_cases bi : b i=0
      · simp [bi]
      · have z : g i=0 := by
          by_contra gn
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bi,gn⟩)
        simp [z,zero_pow lp]
    · simp only [probe,row_apply,dotProduct,Pi.pow_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
  constructor
  · intro k hk
    simpa only [pow_one] using read 1 k 3 (by decide) (by omega) (by simpa only [pow_one] using gm)
  · intro k hk
    exact read 2 k 6 (by decide) (by omega) (by simpa only [pow_two] using g2)

/-- Every paid low-support branch must reserve six possible quadrature
representatives, two charged live dirty rows per active dirty clock,
and all ghost dirty rows separately. Works without a node ordering. -/
theorem dirty_inventory_of_small (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (small : (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card≤4) :
    6+2*(dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card+
        (ghostDirtyRows b (monomialStageDefect A 2)).card≤11 := by
  letI : DecidableEq (Fin 11) := Classical.decEq (Fin 11)
  let g := monomialStageDefect A 2
  let D := activeDirtyRows b g
  let c := nodes A
  let L := dirtyClockLabels c b g
  let H := ghostDirtyRows b g
  change L.card≤4 at small
  have both := dirty_moments ho
  have m1 : ∀ x∈L,(∑ i∈fiber D c x,b i*g i)=0 :=
    all_fibers_dark D c _ (by change L.card≤7; omega) both.1
  have m2 : ∀ x∈L,(∑ i∈fiber D c x,b i*(g i)^2)=0 :=
    all_fibers_dark D c _ small both.2
  obtain ⟨U,sub,Uc,cap⟩ := choose_pairs m1
  change U.card=2*L.card at Uc
  have s := saturated ha ho
  let free := (Finset.univ : Finset (Fin 11)) \ (U∪H)
  have live : Fin.last 10 ∈ free := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro z
    have gt := last_cubic_clean ha ho s
    rcases Finset.mem_union.mp z with h | h
    · exact (Finset.mem_filter.mp (sub h)).2.2 gt
    · exact (Finset.mem_filter.mp h).2.2 gt
  have one : (1:K)∈free.image c := Finset.mem_image.mpr ⟨_,live,s.last_node⟩
  have six : 6≤free.card := (six_possible_clocks ho (free.image c) one
    (fun x hx=>raw_outside_after_pairs (c:=c) (b:=b) (g:=g) U sub cap m1 m2 x hx)).trans
      (Finset.card_image_le : (free.image c).card≤free.card)
  have dis : Disjoint U H := by
    rw [Finset.disjoint_left]
    intro i hu hh
    exact (Finset.mem_filter.mp (sub hu)).2.1 (Finset.mem_filter.mp hh).2.1
  have count : free.card + (U∪H).card=11 := by
    dsimp [free]
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  rw [Finset.card_union_of_disjoint dis,Uc] at count
  change 6+2*L.card+H.card≤11
  omega

/-- Orders 5, 6 and 7 in the active dirty-label count fail just by
the first signed moment and true clean endpoint charges. -/
theorem dirty_first_inventory_of_seven (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (small : (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card≤7) :
    2*(dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card≤9 := by
  let g := monomialStageDefect A 2
  let D := activeDirtyRows b g
  let c := nodes A
  let L := dirtyClockLabels c b g
  have m1 : ∀ x∈L,(∑ i∈fiber D c x,b i*g i)=0 :=
    all_fibers_dark D c _ small (dirty_moments ho).1
  obtain ⟨U,sub,Uc,_⟩ := choose_pairs m1
  have s := saturated ha ho
  have h0 := zeroSpace_at_zero_row s.physical_origin 3 (monomialStageDefect_mem A 2)
  have ht := last_cubic_clean ha ho s
  have space : U ⊆ (Finset.univ : Finset (Fin 11)) \ {0,Fin.last 10} := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    have bad := (Finset.mem_filter.mp (sub hi)).2.2
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (rfl|rfl)
    · exact bad h0
    · exact bad ht
  have n := Finset.card_le_card space
  rw [Uc,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
    Finset.card_pair (by decide : (0:Fin 11)≠Fin.last 10)] at n
  exact n

/-- Active dirty support is either small (at most two numerical labels),
or in the separate high-support cases eight and nine. -/
theorem dirty_labels_small_or_high (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card≤2 ∨
    8≤(dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card := by
  by_cases small : (dirtyClockLabels (nodes A) b (monomialStageDefect A 2)).card≤7
  · have q := dirty_first_inventory_of_seven ha ho small
    have extra := dirty_inventory_of_small ha ho (by omega)
    omega
  · exact Or.inr (by omega)

end
end RKResearch.Certified.Graded.CrossedOrderTen
