module

public import RKCert.ReviewedNative.ERKUniform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Rank and a primitive test exclude pure grade-five profiles outside
three physical rows. The stage indices are the original ones. -/
namespace RKResearch.Certified.Graded

open Module
open Reverse
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {n p : Nat}
variable {A : Matrix (Fin n) (Fin n) K} {b : Fin n → K}

private def liftCoord (S : Finset (Fin n)) : (S → K) →ₗ[K] (Fin n → K) where
  toFun f i := if h : i∈S then f ⟨i,h⟩ else 0
  map_add' f g := by ext i; by_cases h : i∈S <;> simp [h]
  map_smul' a f := by ext i; by_cases h : i∈S <;> simp [h]

private def restrictCoord (S : Finset (Fin n)) : (Fin n → K) →ₗ[K] (S → K) where
  toFun f i := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def carrier (S : Finset (Fin n)) : Submodule K (Fin n → K) :=
  LinearMap.range (liftCoord S)

private theorem mem_carrier (S : Finset (Fin n)) {w : Fin n → K} :
    w∈carrier S ↔ ∀ i ∉ S, w i = 0 := by
  constructor
  · rintro ⟨q,rfl⟩ i hi
    simp [liftCoord,hi]
  · intro hw
    refine ⟨fun i => w i, ?_⟩
    ext i
    by_cases hi : i∈S <;> simp [liftCoord,hi,hw]

private theorem rank_carrier (S : Finset (Fin n)) : finrank K (carrier (K:=K) S)=S.card := by
  have h : Function.Injective (liftCoord (K:=K) S) := by
    intro v w e
    ext i
    have h' := congrFun e i.val
    simpa [liftCoord,i.prop] using h'
  rw [carrier, LinearMap.finrank_range_of_inj h,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

private theorem sum_taps {S : Finset (Fin n)} (i : Fin n) (v : Fin n → K)
    (hz : ∀ j ∉ S, A i j*v j=0) :
    (mat A v) i = row (fun j : S => A i j) (fun j : S => v j) := by
  simp only [mat_apply,Matrix.mulVec_apply_eq_sum,row_apply,dotProduct]
  rw [Finset.sum_coe_sort S (fun j : Fin n => A i j * v j)]
  exact (Finset.sum_subset (Finset.subset_univ S)
    (fun j _ h => hz j h)).symm

private theorem pure_power_paid {S : Finset (Fin n)}
    (supp : ∀ v∈zeroSpace A 4, ∀ j ∉ S, v j=0) {i : Fin n} (hi : i∉S)
    (k : Nat) (hk : k≤3) :
    ((k+1:Nat):K)*(mat A (fun j => (nodes A j)^k)) i=(nodes A i)^(k+1) := by
  have q := supp _ (zeroSpace_mono A (show k+1≤4 by omega) (monomialStageDefect_mem A k)) i hi
  exact sub_eq_zero.mp q

private theorem pure_quartic_test {S : Finset (Fin n)}
    (supp : ∀ v∈zeroSpace A 4, ∀ j ∉ S, v j=0) {i : Fin n} (hi : i∉S) (x : K) :
    2*(mat A (fun j => (nodes A j)*((nodes A j)-x)*(2*(nodes A j)-x))) i
      = (nodes A i)^2*((nodes A i)-x)^2 := by
  have eq : (fun j => (nodes A j)*((nodes A j)-x)*(2*(nodes A j)-x)) =
      (2:K) • (fun j => (nodes A j)^3) - (3*x) • (fun j => (nodes A j)^2)
        + x^2 • (fun j => nodes A j) := by
    ext j
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [eq,map_add,map_sub,map_smul,map_smul,map_smul]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  have h1 := pure_power_paid supp hi 1 (by decide)
  have h2 := pure_power_paid supp hi 2 (by decide)
  have h3 := pure_power_paid supp hi 3 (by decide)
  simp only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at h1 h2 h3
  linear_combination h3 - 2*x*h2 + x^2*h1

/-- Three physical coordinates cannot carry the entire grade-four
defect space (trees through five vertices) of an explicit order-five
tableau over a field, including all admissible positive characteristics. -/
theorem no_three_physical_defective_rows_field
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b) (hp : 5≤p)
    (S : Finset (Fin n)) (hs : S.card≤3)
    (supp : ∀ v∈zeroSpace A 4, ∀ j ∉ S, v j=0) : False := by
  classical
  have hsub : zeroSpace A 4≤carrier S := fun v hv => (mem_carrier _).mpr (supp v hv)
  have r4 := zeroSpace_finrank ha ho (n:=3) hp
  have r3 : 2 ≤ finrank K (zeroSpace A 3) := zeroSpace_finrank ha ho (n:=2) (by omega : 2+2≤p)
  have hcar : zeroSpace A 4=carrier S := by
    apply Submodule.eq_of_le_of_finrank_le hsub
    rw [rank_carrier]
    change 3 ≤ finrank K (zeroSpace A 4) at r4
    omega
  have hweight : ∀ j∈S,b j=0 := by
    intro j hj
    have hv : coordinate (K:=K) j∈zeroSpace A 4 := by
      rw [hcar,mem_carrier]
      intro k hk
      have hne : k≠j := fun h => hk (h.symm ▸ hj)
      simp [coordinate,hne]
    have q := probe_zeroSpace (j:=4) (k:=0) ho (by omega) hv
    change probe A b 0 (coordinate j) = 0 at q
    simpa only [pow_zero,mul_one,row_coordinate] using q
  let c := nodes A
  have one : 2*(b ⬝ᵥ c)=1 := by
    simpa only [c,pow_one,Nat.succ_eq_add_one,Nat.reduceAdd,Nat.cast_ofNat] using ho.hasQuadratureOrder 1 (by omega)
  have h2nz : (2:K)≠0 := by
    intro h
    rw [h,zero_mul] at one
    exact zero_ne_one one
  have hpos : ∃ i : Fin n, i∉S ∧ c i≠0 := by
    by_contra! hnone
    have hz : (b ⬝ᵥ c)=0 := by
      unfold dotProduct
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j∈S
      · simp [hweight j hj]
      · simp [hnone j hj]
    have q := ho.hasQuadratureOrder 1 (by omega : 1<p)
    simp only [pow_one] at q
    change (2:K)*(b ⬝ᵥ c)=1 at q
    rw [hz,mul_zero] at q
    exact zero_ne_one q
  obtain ⟨i₀,h₀,early⟩ := wellFounded_lt.has_min {i : Fin n | i∉S ∧ c i≠0} hpos
  have hbefore (j : Fin n) (hj : j < i₀) (hC : j∉S) : c j=0 := by
    by_contra hj0
    exact early j ⟨hC,hj0⟩ hj
  let q := (zeroSpace A 3).map (restrictCoord S)
  have rQ : finrank K (zeroSpace A 3) = finrank K q := by
    let f : zeroSpace A 3 →ₗ[K] (S → K) := (restrictCoord S).comp (zeroSpace A 3).subtype
    have hf : Function.Injective f := by
      intro v w h
      apply Subtype.ext
      ext i
      by_cases hi : i∈S
      · exact congrFun h ⟨i,hi⟩
      · exact (supp _ (zeroSpace_mono A (by decide : 3≤4) v.prop) i hi).trans
          (supp _ (zeroSpace_mono A (by decide : 3≤4) w.prop) i hi).symm
    rw [←LinearMap.finrank_range_of_inj hf]
    have hq : LinearMap.range f = q := by
      simp only [f,LinearMap.range_comp,Submodule.range_subtype,q]
    rw [hq]
  let tap (i : Fin n) : S→K := fun j => A i j
  have htap (i : Fin n) (hi : i∉S) : tap i ∈ annih q := by
    apply mem_annih.mpr
    intro w hw
    obtain ⟨v,hv,ev⟩ := Submodule.mem_map.mp hw
    rw [←ev]
    change row (fun j : S => A i j) (fun j : S => v j) = 0
    rw [←sum_taps]
    · exact supp _ (mat_zeroSpace ho 3 (by omega) hv) i hi
    · intro j hj
      rw [supp v (zeroSpace_mono A (by decide : 3≤4) hv) j hj,mul_zero]
  have noZero : tap i₀ ≠ 0 := by
    intro h
    have e := sum_taps (A:=A) (S:=S) i₀ c (fun j hj => by
      by_cases hlt : j < i₀
      · rw [hbefore j hlt hj,mul_zero]
      · rw [ha i₀ j (le_of_not_gt hlt),zero_mul])
    change (mat A c) i₀ = row (tap i₀) (fun j : S => c j) at e
    rw [h] at e
    have ee : (mat A c) i₀ = 0 := e.trans (by rw [row_apply]; simp [dotProduct])
    have t := pure_power_paid supp h₀.1 1 (by decide)
    simp only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at t
    change 2*(mat A c) i₀=(c i₀)^2 at t
    rw [ee,mul_zero] at t
    exact pow_ne_zero _ h₀.2 t.symm
  have share : annih q = K ∙ tap i₀ := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (htap _ h₀.1)
    · have h := finrank_annih q
      rw [Fintype.card_coe,←rQ] at h
      rw [finrank_span_singleton noZero]
      omega
  let x := c i₀
  let P (j : Fin n) := c j*(c j-x)*(2*c j-x)
  have hpTap : row (tap i₀) (fun j : S => P j) = 0 := by
    rw [←sum_taps]
    · have f := pure_quartic_test supp h₀.1 x
      change 2*(mat A P) i₀=(c i₀)^2*(c i₀ - x)^2 at f
      simp only [x,sub_self,zero_pow (by decide : (2:Nat)≠0),mul_zero] at f
      exact (mul_eq_zero.mp f).resolve_left h2nz
    · intro j hj
      by_cases hlt : j < i₀
      · simp [P,hbefore j hlt hj]
      · rw [ha i₀ j (le_of_not_gt hlt),zero_mul]
  have clocks (i : Fin n) : i∉S → c i=0 ∨ c i=x := by
    induction i using (wellFounded_lt : WellFounded (α:=Fin n) (· < ·)).induction
    next i ih =>
      intro hi
      have hw := htap i hi
      rw [share] at hw
      obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp hw
      have tapZero : row (tap i) (fun j : S => P j)=0 := by
        rw [←hz]
        simp only [row_apply,dotProduct,Pi.smul_apply,smul_eq_mul,mul_assoc,
          ←Finset.mul_sum]
        have hh := hpTap
        simp only [row_apply,dotProduct] at hh
        rw [hh,mul_zero]
      have H : (mat A P) i=0 := by
        rw [sum_taps (S:=S)]
        · exact tapZero
        · intro j hj
          by_cases hlt : j < i
          · rcases ih j hlt hj with hz | hz <;> simp [P,hz]
          · rw [ha i j (le_of_not_gt hlt),zero_mul]
      have t := pure_quartic_test supp hi x
      change 2*(mat A P) i=(c i)^2*(c i-x)^2 at t
      rw [H,mul_zero] at t
      rcases mul_eq_zero.mp t.symm with hz|hz
      · exact Or.inl (by by_contra h; exact pow_ne_zero _ h hz)
      · exact Or.inr (sub_eq_zero.mp (by by_contra h; exact pow_ne_zero _ h hz))
  have two : 3*(b ⬝ᵥ (c^2))=1 := by
    simpa only [c,Nat.succ_eq_add_one,Nat.reduceAdd,Nat.cast_ofNat] using ho.hasQuadratureOrder 2 (by omega)
  have three : 4*(b ⬝ᵥ (c^3))=1 := by
    simpa only [c,Nat.succ_eq_add_one,Nat.reduceAdd,Nat.cast_ofNat] using ho.hasQuadratureOrder 3 (by omega)
  have hm (k : Nat) : (b ⬝ᵥ (c^(k+1)))=x^k*(b ⬝ᵥ c) := by
    simp only [dotProduct,Pi.pow_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j∈S
    · simp [hweight j hj]
    · rcases clocks j hj with hz|hz
      · simp [hz, pow_succ]
      · rw [hz,pow_succ]
        ring
  have h2 := hm 1
  have h3 := hm 2
  simp only [pow_one] at h2
  rw [h2] at two
  rw [h3] at three
  have hx : 3*x=2 := by linear_combination 2*two - 3*x*one
  have hsq : 9*x^2=4 := calc
    _ = (3*x)^2 := by ring
    _ = 4 := by rw [hx]; ring
  have imposs : (1:K)=0 := by linear_combination (-9:K)*three + 4*(b ⬝ᵥ c)*hsq + 8*one
  exact one_ne_zero imposs

/-- Five-node stage defects of an order-five explicit method over a
nontrivial commutative ring cannot be confined to three stage rows. -/
theorem no_three_physical_defective_rows {R : Type*} [CommRing R] [Nontrivial R]
    {T : Matrix (Fin n) (Fin n) R} {w : Fin n → R}
    (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder p T w) (hp : 5≤p)
    (S : Finset (Fin n)) (hs : S.card≤3)
    (supp : ∀ v∈zeroSpace T 4, ∀ j ∉ S, v j=0) : False := by
  classical
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let _ := hI
  let _ := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  apply no_three_physical_defective_rows_field
    (A:=T.map f) (fun i j hij => by rw [Matrix.map_apply,ha i j hij,map_zero])
    (ho.map f) hp S hs
  intro v hv j hj
  have q : zeroSpace (T.map f) 4 ≤ (LinearMap.proj j).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,u,hor,hsize,rfl⟩
    have h := supp _ (normDiff_mem (j:=4) T t u hor hsize) j hj
    change (normTree (T.map f) t j - normTree (T.map f) u j)=0
    have eq (r : FiniteRootedTree) : normTree (T.map f) r j = f (normTree T r j) := by
      simp [normTree,←RKResearch.map_Φ,Pi.smul_apply,smul_eq_mul]
    rw [eq,eq,←map_sub]
    exact (congrArg f h).trans (map_zero f)
  exact q hv

/-- Width 11 at order 8 has only two midpoint defect ranks; the larger
rank forces the first exact reflected balance. -/
theorem width11_order8_defect_rank_options {T : Matrix (Fin 11) (Fin 11) K}
    {w : Fin 11 → K} (ha : ∀ i j, i≤j → T i j=0) (ho : HasOrder 8 T w) :
    (finrank K (zeroSpace T 4)=3 ∨ finrank K (zeroSpace T 4)=4) ∧
      (finrank K (zeroSpace T 4)=4 → firstSeed T w=0) := by
  have lo : 3 ≤ finrank K (zeroSpace T 4) := zeroSpace_finrank ha ho (n:=3) (by decide)
  have room := erk_even_midpoint_budget ha ho (q:=4) (by decide) (by decide)
  have r : 7+finrank K (zeroSpace T 4)+finrank K (back T w 0) ≤ 11 := room
  refine ⟨by omega,?_⟩
  intro hr
  by_contra! hn
  change 7+finrank K (zeroSpace T 4)+finrank K (K ∙ firstSeed T w) ≤ 11 at r
  rw [finrank_span_singleton hn] at r
  omega

end

end RKResearch.Certified.Graded

#print axioms RKResearch.Certified.Graded.no_three_physical_defective_rows
#print axioms RKResearch.Certified.Graded.width11_order8_defect_rank_options
