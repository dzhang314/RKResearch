module

public import RKCert.ReviewedNative.WeakFiveSoleInnerGaussianComparison
public import RKCert.ReviewedNative.OrderedSingleGapRoot

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact cell enclosure from the literal SoleInner corners

Each corner's algebraic roots are filled in an ordered extension of
the actual field. A finite-grid base change transports the paid actual
six-node polynomial to that extension, and the resulting inequality
descends. The two extensions do not have to be amalgamated. There is no
assumption that the original field is real closed or Archimedean. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.OrderedSingleGapRoot
open scoped BigOperators Classical

universe u
noncomputable section
variable {K L : Type u}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

private theorem point_map (f : K →+* L) (i : Fin 19) :
    f (point K i) = point L i := by
  simp only [PositiveRule19.point,map_div₀,map_natCast,map_ofNat]

private theorem weight_map (f : K →+* L) (i : Fin 19) :
    f (weight K i) = weight L i := by
  simp only [PositiveRule19.weight,map_div₀,map_natCast]

/-- Bounded change of scalars, justified by the very same checked rational
finite rule on both fields. No additional primitive or physical-moment
mapping API is needed. -/
private theorem unit_moment_map (f : K →+* L) (P : K[X]) (pd : P.natDegree≤19) :
    integral 0 1 (P.map f) = f (integral 0 1 P) := by
  have pd' : (P.map f).natDegree≤19 := natDegree_map_le.trans pd
  rw [unit_exact (P.map f) pd',unit_exact P pd,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,weight_map,←point_map f i,Polynomial.eval_map_apply]

private theorem density_map (f : K →+* L) (s r : K) :
    (density s r).map f = density (f s) (f r) := by
  simp only [density,unitWeight,affineWeight,Polynomial.map_mul,Polynomial.map_sub,
    Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,Polynomial.map_one,map_sub,map_one]

private theorem nodal_map (f : K →+* L) (v : Fin 6 → K) :
    (Lagrange.nodal Finset.univ v).map f =
      Lagrange.nodal Finset.univ (fun i => f (v i)) := by
  simp only [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_C]

namespace SixNodes

variable {s r : K}

/-- Preserve the literal sites and all six tests when reaching a
corner's root field. The extension tests come from the six paid base
monomials, not from an assumption on test coefficients. -/
def along (N : SixNodes s r) (f : K →+* L) (fm : StrictMono f) :
    SixNodes (f s) (f r) where
  sUnit := ⟨by simpa only [map_zero] using fm.monotone N.sUnit.1,
    by simpa only [map_one] using fm.monotone N.sUnit.2⟩
  rUnit := ⟨by simpa only [map_zero] using fm.monotone N.rUnit.1,
    by simpa only [map_one] using fm.monotone N.rUnit.2⟩
  site := fun i => f (N.site i)
  increasing := fm.comp N.increasing
  inside := fun i => ⟨by simpa only [map_zero] using fm (N.inside i).1,
    by simpa only [map_one] using fm (N.inside i).2⟩
  paid := by
    intro H hd
    let A : K[X] := Lagrange.nodal Finset.univ N.site
    let B : L[X] := Lagrange.nodal Finset.univ (fun i => f (N.site i))
    let J : L[X] →ₗ[L] L := (integral 0 1).comp
      (LinearMap.mulLeft L (density (f s) (f r)*B))
    have pow (n : ℕ) (hn : n < 6) : J (X^n) = 0 := by
      have zero : integral 0 1 (density s r*A*X^n)=0 :=
        N.paid _ (by rw [natDegree_X_pow]; omega)
      have aDegree : A.natDegree≤6 := by simp [A]
      have degree : (density s r*A*X^n).natDegree≤19 := by
        have := natDegree_mul_le_of_le
          (natDegree_mul_le_of_le (density_degree s r) aDegree) (natDegree_X_pow (R := K) (n := n)).le
        omega
      have h := unit_moment_map f (density s r*A*X^n) degree
      rw [zero,map_zero] at h
      change integral 0 1 (density (f s) (f r)*B*X^n)=0
      simpa only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
        density_map,A,B,nodal_map] using h
    change J H = 0
    rw [H.as_sum_range' 6 (by omega),map_sum]
    apply Finset.sum_eq_zero
    intro n hn
    rw [←C_mul_X_pow_eq_monomial,←Polynomial.smul_eq_C_mul,map_smul,
      pow n (Finset.mem_range.mp hn),smul_zero]

@[simp] theorem along_site (N : SixNodes s r) (f : K →+* L) (fm : StrictMono f)
    (i : Fin 6) : (N.along f fm).site i = f (N.site i) := rfl

end SixNodes

namespace CornerRow

variable (d : CornerRow)

private theorem s_map (f : K →+* L) : f (d.s K)=d.s L := by
  simp only [s,map_div₀,map_natCast,map_ofNat]

private theorem r_map (f : K →+* L) : f (d.r K)=d.r L := by
  simp only [r,normalizedRight,d.s_map,ratio,map_div₀,map_natCast,map_mul,map_sub,map_add,map_one]

private theorem lower_map (f : K →+* L) (i : Fin 6) :
    f (d.lowerEndpoint K i)=d.lowerEndpoint L i := by
  simp only [lowerEndpoint,map_div₀,map_natCast,map_ofNat]

private theorem upper_map (f : K →+* L) (i : Fin 6) :
    f (d.upperEndpoint K i)=d.upperEndpoint L i := by
  simp only [upperEndpoint,map_div₀,map_natCast,map_ofNat]

private theorem monic_map (f : K →+* L) :
    (d.monicPolynomial K).map f = d.monicPolynomial L := by
  simp only [monicPolynomial,integerPolynomial,ofFn_eq_sum_monomial,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sum,Polynomial.map_monomial,map_inv₀,map_intCast]

/-- The literal six corner cages are occupied by the six simple nodes
of the exact same corner in one ordered extension. -/
theorem exists_nodes_in_corner_cages (hd : d.Verified) :
    ∃ (E : OrderedExtension K) (N : SixNodes (d.s E.carrier) (d.r E.carrier)),
      ∀ i, d.lowerEndpoint E.carrier i < N.site i ∧
        N.site i < d.upperEndpoint E.carrier i := by
  let P := d.monicPolynomial K
  have base := hd.monic_witness (K := K)
  obtain ⟨E,rootSource⟩ := exists_unitRootSource P
  have fill (i : Fin 6) :
      ∃ v : E.carrier, d.lowerEndpoint E.carrier i < v ∧
        v < d.upperEndpoint E.carrier i ∧ (d.monicPolynomial E.carrier).IsRoot v := by
    obtain ⟨l,lh,h⟩ := base.cages.interior i
    have opp : Opposite (P.eval (d.lowerEndpoint K i)) (P.eval (d.upperEndpoint K i)) :=
      mul_neg_iff.mp (base.cages.signs i)
    obtain ⟨v,lv,vh,zero⟩ := rootSource ⟨l,lh.trans h⟩ ⟨l.trans lh,h⟩ lh opp
    have mp : P.map E.embed = d.monicPolynomial E.carrier := d.monic_map E.embed
    refine ⟨v,by simpa only [d.lower_map] using lv,
      by simpa only [d.upper_map] using vh,?_⟩
    simpa only [mp] using zero
  choose v vl vh vz using fill
  have other := hd.monic_witness (K := E.carrier)
  have increasing : StrictMono v := Fin.strictMono_iff_lt_succ.mpr (fun i =>
    (vh i.castSucc).trans ((other.cages.adjacent i).trans (vl i.succ)))
  have unit (i : Fin 6) : v i ∈ Set.Ioo (0 : E.carrier) 1 := by
    obtain ⟨a,_,b⟩ := other.cages.interior i
    exact ⟨a.trans (vl i),(vh i).trans b⟩
  let N := SixNodes.ofMonic other.sUnit other.rUnit other.monic other.degree other.orthogonal
    v increasing unit vz
  exact ⟨E,N,fun i => ⟨vl i,vh i⟩⟩

/-- A lower parameter corner gives an upper cage endpoint for the same
actual indexed node. -/
theorem below_corner_upper (hd : d.Verified) {s r : K} (N : SixNodes s r)
    (hs : d.s K≤s) (hr : d.r K≤r) (i : Fin 6) :
    N.site i < d.upperEndpoint K i := by
  obtain ⟨E,Q,h⟩ := d.exists_nodes_in_corner_cages (K := K) hd
  have hS : d.s E.carrier≤E.embed s := by
    simpa only [d.s_map] using E.mono.monotone hs
  have hR : d.r E.carrier≤E.embed r := by
    simpa only [d.r_map] using E.mono.monotone hr
  have cmp := decreasing_nodes Q (N.along E.embed E.mono) hS hR i
  apply E.mono.lt_iff_lt.mp
  rw [d.upper_map]
  exact cmp.trans_lt (h i).2

/-- An upper parameter corner gives a lower cage endpoint for the same
actual indexed node. -/
theorem above_corner_lower (hd : d.Verified) {s r : K} (N : SixNodes s r)
    (hs : s≤d.s K) (hr : r≤d.r K) (i : Fin 6) :
    d.lowerEndpoint K i < N.site i := by
  obtain ⟨E,Q,h⟩ := d.exists_nodes_in_corner_cages (K := K) hd
  have hS : E.embed s≤d.s E.carrier := by
    simpa only [d.s_map] using E.mono.monotone hs
  have hR : E.embed r≤d.r E.carrier := by
    simpa only [d.r_map] using E.mono.monotone hr
  have cmp := decreasing_nodes (N.along E.embed E.mono) Q hS hR i
  apply E.mono.lt_iff_lt.mp
  rw [d.lower_map]
  exact (h i).1.trans_le cmp

end CornerRow

private theorem normalize_den_pos {s c : K} (hs : s ∈ Set.Icc (0 : K) 1) (hc : 0 < c) :
    0 < 1-s+c*s := by
  by_cases h : s=0
  · simp [h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs.2)
      (mul_pos hc (lt_of_le_of_ne hs.1 (fun e => h e.symm)))

/-- Both compactification arguments are increasing on the paid domain;
this holds also at the endpoint values zero and one. -/
theorem normalizedRight_mono {s₀ s₁ c₀ c₁ : K}
    (h₀ : s₀ ∈ Set.Icc (0 : K) 1) (h₁ : s₁ ∈ Set.Icc (0 : K) 1)
    (hs : s₀≤s₁) (hc : c₀≤c₁) (cpos : 0 < c₀) :
    normalizedRight s₀ c₀≤normalizedRight s₁ c₁ := by
  unfold normalizedRight
  apply (div_le_div_iff₀ (normalize_den_pos h₀ cpos)
    (normalize_den_pos h₁ (cpos.trans_le hc))).mpr
  apply sub_nonneg.mp
  have e : c₁*s₁*(1-s₀+c₀*s₀)-c₀*s₀*(1-s₁+c₁*s₁) =
      (c₁-c₀)*s₁*(1-s₀)+c₀*(s₁-s₀) := by ring
  rw [e]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) h₁.1) (sub_nonneg.mpr h₀.2))
    (mul_nonneg cpos.le (sub_nonneg.mpr hs))

/-- Bounds in the exact published orientation: lower coordinate bounds
come from the high corner's low numerator, and upper coordinate bounds
from the low corner's high endpoint. -/
theorem in_cell_cages (cell : Fin 15) {s r : K} (N : SixNodes s r)
    (slo : (lowCellCorner cell).s K≤s) (shi : s≤(highCellCorner cell).s K)
    (rlo : (lowCellCorner cell).r K≤r) (rhi : r≤(highCellCorner cell).r K)
    (i : Fin 6) :
    (highCellCorner cell).lowerEndpoint K i < N.site i ∧
      N.site i < (lowCellCorner cell).upperEndpoint K i :=
  ⟨(highCellCorner cell).above_corner_lower (cornerRow_verified (highRowIndex cell)) N shi rhi i,
    (lowCellCorner cell).below_corner_upper (cornerRow_verified (lowRowIndex cell)) N slo rlo i⟩

/-- The actual ratio interval, together with one closed breakpoint cell,
implies the exact six cages for the actual ordered sites. -/
theorem normalized_cell_cages (cell : Fin 15) {s r c : K} (N : SixNodes s r)
    (slo : (cellBreaks cell.castSucc : K)/64≤s) (shi : s≤(cellBreaks cell.succ : K)/64)
    (clo : (2 : K)/3≤c) (chi : c≤(6 : K)/7)
    (parameter : r=normalizedRight s c) (i : Fin 6) :
    (highCellCorner cell).lowerEndpoint K i < N.site i ∧
      N.site i < (lowCellCorner cell).upperEndpoint K i := by
  obtain ⟨l,h⟩ := cell_corner_witnesses (K := K) cell
  obtain ⟨ls,lr⟩ := lowCellCorner_coordinates (K := K) cell
  obtain ⟨hs,hr⟩ := highCellCorner_coordinates (K := K) cell
  have slo' : (lowCellCorner cell).s K≤s := ls.symm ▸ slo
  have shi' : s≤(highCellCorner cell).s K := hs.symm ▸ shi
  apply in_cell_cages cell N slo' shi' _ _ i
  · rw [lr,parameter,←ls]
    exact normalizedRight_mono l.sUnit N.sUnit slo' clo (by norm_num)
  · rw [parameter,hr,←hs]
    exact normalizedRight_mono N.sUnit h.sUnit shi' chi ((by norm_num : (0 : K) < 2/3).trans_le clo)

/-- The actual compact parameter lies in at least one of the 15 published
breakpoint intervals. Taking the first endpoint at or above it requires
no vertex enumeration and also handles a parameter on a boundary. -/
theorem breakpoint_cover {s : K} (hs : s ∈ Set.Icc (0 : K) 1) :
    ∃ i : Fin 15, (cellBreaks i.castSucc : K)/64≤s ∧ s≤(cellBreaks i.succ : K)/64 := by
  let a : Fin 16 → K := fun j => (cellBreaks j : K)/64
  let U : Finset (Fin 16) := Finset.univ.filter (fun j => s≤a j)
  have a₀ : a 0=0 := by norm_num [a,cellBreaks]
  have a₁ : 0≤a (0 : Fin 15).succ := by
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have a₁₅ : a 15=1 := by norm_num [a,cellBreaks]
  have nonempty : U.Nonempty := by
    refine ⟨15,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    rw [a₁₅]
    exact hs.2
  let j := U.min' nonempty
  have got : s≤a j := (Finset.mem_filter.mp (Finset.min'_mem U nonempty)).2
  by_cases h : j.val=0
  · have jz : j=0 := Fin.ext h
    have zero : s≤0 := by simpa only [jz,a₀] using got
    refine ⟨0,?_,zero.trans a₁⟩
    change a 0≤s
    rw [a₀]
    exact hs.1
  · have bound := j.isLt
    let i : Fin 15 := ⟨j.val-1,by omega⟩
    have eq : i.succ=j := by
      apply Fin.ext
      change (j.val-1)+1=j.val
      omega
    have prev : i.castSucc < j := by
      change j.val-1 < j.val
      omega
    have low : a i.castSucc≤s := by
      apply le_of_lt
      apply lt_of_not_ge
      intro b
      have member : i.castSucc∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,b⟩
      exact (not_le_of_gt prev) (Finset.min'_le U _ member)
    exact ⟨i,low,eq.symm ▸ got⟩

/-- All six actual sites share the same exact cell; there is no narrowing
to a sampled value of either compact parameter. -/
theorem exists_actual_cell_cages {s r c : K} (N : SixNodes s r)
    (clo : (2 : K)/3≤c) (chi : c≤(6 : K)/7) (parameter : r=normalizedRight s c) :
    ∃ cell : Fin 15, (cellBreaks cell.castSucc : K)/64≤s ∧
      s≤(cellBreaks cell.succ : K)/64 ∧
      ∀ i : Fin 6, (highCellCorner cell).lowerEndpoint K i < N.site i ∧
        N.site i < (lowCellCorner cell).upperEndpoint K i := by
  obtain ⟨cell,hlo,hhi⟩ := breakpoint_cover N.sUnit
  exact ⟨cell,hlo,hhi,normalized_cell_cages cell N hlo hhi clo chi parameter⟩

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
