module

public import RKCert.ReviewedNative.GradedPrimitives
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

/-! # Transport a native primitive zero to a specified conjugate root

Only the finite rational splitting field is compared between extensions.
In particular no order is ever carried by the field maps. This lemma does
not select a root, require an ordered field, or certify any fixed polynomial.
-/

namespace RKResearch.Certified.Graded.NativeRootTransport

open Polynomial
noncomputable section

/-- Algebraic naturality of the zero-constant native primitive. -/
theorem primitive_map {K E : Type*} [Field K] [Field E]
    (f : K →+* E) (P : K[X]) :
    (primitive P).map f = primitive (P.map f) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_map, primitive_coeff_succ, map_div₀, map_natCast]

theorem first_primitive_map {K E : Type*} [Field K] [Field E]
    (f : K →+* E) (P : K[X]) (x : K) :
    (primitive (X * P.map f)).eval (f x) = f ((primitive (X*P)).eval x) := by
  rw [← Polynomial.map_X f, ← Polynomial.map_mul, ← primitive_map,
    Polynomial.eval_map_apply]

private theorem map_base {S E : Type*} [Field S] [Field E] [Algebra ℚ S] [Algebra ℚ E]
    (H : ℚ[X]) (i : S →ₐ[ℚ] E) :
    (H.map (algebraMap ℚ S)).map i.toRingHom = H.map (algebraMap ℚ E) := by
  rw [map_map]
  congr 1
  ext x
  exact i.commutes x

private theorem root_preimage {E : Type*} [Field E] [Algebra ℚ E]
    (H : ℚ[X]) (hm : H.Monic) (i : H.SplittingField →ₐ[ℚ] E)
    {z : E} (hz : (H.map (algebraMap ℚ E)).IsRoot z) :
    ∃ x : H.SplittingField, x ∈ H.rootSet H.SplittingField ∧ i x=z := by
  have hmem : z ∈ H.rootSet E := hm.mem_rootSet.mpr (by
    rw [← Polynomial.eval_map_algebraMap H z]
    exact hz)
  have himage :=
    (IsSplittingField.splits H.SplittingField H).image_rootSet_of_map_ne_zero
      i ((hm.map (algebraMap ℚ E)).ne_zero)
  rw [← himage] at hmem
  exact hmem

private theorem lift_monic_factor {E : Type*} [Field E] [Algebra ℚ E]
    (H : ℚ[X]) (hm : H.Monic) (i : H.SplittingField →ₐ[ℚ] E)
    (splits : (H.map (algebraMap ℚ E)).Splits)
    {P : E[X]} (pm : P.Monic) (dvd : P ∣ H.map (algebraMap ℚ E)) :
    ∃ R : H.SplittingField[X], R.map i.toRingHom=P := by
  have s := splits.of_dvd ((hm.map (algebraMap ℚ E)).ne_zero) dvd
  apply (Polynomial.mem_lifts (f:=i.toRingHom) P).mp
  refine s.mem_lift_of_roots_mem_range pm i.toRingHom ?_
  intro z hz
  have hit := ((mem_roots pm.ne_zero).mp hz).dvd dvd
  obtain ⟨z',_,he⟩ := root_preimage H hm i hit
  exact ⟨z',he⟩

/-- A factor window with zero first primitive at one root transfers to any
specified rational conjugate in another field that splits the base polynomial.
Both polynomial factors, their degrees, and the exact primitive zero survive.
The source field need not split the base polynomial and need not be ordered. -/
theorem transport_first_primitive_zero
    {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    (H : ℚ[X]) (hm : H.Monic) (hi : Irreducible H)
    {Q N : K[X]} {u : K} (qm : Q.Monic) (nm : N.Monic)
    (prod : Q*N=H.map (algebraMap ℚ K))
    (root : N.IsRoot u) (zero : (primitive (X*Q)).eval u=0)
    (split : (H.map (algebraMap ℚ E)).Splits)
    {v : E} (rootV : (H.map (algebraMap ℚ E)).IsRoot v) :
    ∃ Q' N' : E[X],
      Q'.Monic ∧ N'.Monic ∧ Q'.natDegree=Q.natDegree ∧ N'.natDegree=N.natDegree ∧
      Q'*N'=H.map (algebraMap ℚ E) ∧ N'.IsRoot v ∧ (primitive (X*Q')).eval v=0 := by
  classical
  let S := H.SplittingField
  let HK := H.map (algebraMap ℚ K)
  let L := HK.SplittingField
  let k : K →+* L := algebraMap K L
  have base : HK.map k = H.map (algebraMap ℚ L) := by
    dsimp only [HK,k]
    rw [map_map, ← IsScalarTower.algebraMap_eq ℚ K L]
  have hs : (H.map (algebraMap ℚ L)).Splits :=
    base ▸ IsSplittingField.splits L HK
  let j : S →ₐ[ℚ] L := IsSplittingField.lift S H hs
  let i : S →ₐ[ℚ] E := IsSplittingField.lift S H split
  have prodL : Q.map k * N.map k = H.map (algebraMap ℚ L) := by
    rw [← Polynomial.map_mul, prod, ← base]
  have hku : (N.map k).IsRoot (k u) := by
    rw [IsRoot,eval_map_apply]
    exact (congrArg k (show N.eval u=0 from root)).trans (map_zero k)
  have ndvd : N.map k ∣ H.map (algebraMap ℚ L) :=
    ⟨Q.map k, by rw [mul_comm,prodL]⟩
  have qdvd : Q.map k ∣ H.map (algebraMap ℚ L) := ⟨N.map k,prodL.symm⟩
  obtain ⟨us,hus,ju⟩ := root_preimage H hm j (hku.dvd ndvd)
  obtain ⟨vs,hvs,iv⟩ := root_preimage H hm i rootV
  obtain ⟨QS,jQ⟩ := lift_monic_factor H hm j hs (qm.map k) qdvd
  obtain ⟨NS,jN⟩ := lift_monic_factor H hm j hs (nm.map k) ndvd
  have sQM : QS.Monic := monic_map_iff.mp (jQ.symm ▸ qm.map k)
  have sNM : NS.Monic := monic_map_iff.mp (jN.symm ▸ nm.map k)
  have sProd : QS*NS=H.map (algebraMap ℚ S) := by
    apply Polynomial.map_injective j.toRingHom j.injective
    rw [Polynomial.map_mul,jQ,jN,map_base]
    exact prodL
  have sRoot : NS.IsRoot us := by
    change NS.eval us=0
    apply j.injective
    rw [map_zero,← eval_map_apply,jN]
    change (N.map k).eval (j us)=0
    rw [ju]
    exact hku
  have sZero : (primitive (X*QS)).eval us=0 := by
    apply j.injective
    rw [map_zero,← first_primitive_map,jQ]
    change (primitive (X*(Q.map k))).eval (j us)=0
    rw [ju,first_primitive_map,zero,map_zero]
  have evU : aeval us H=0 := hm.mem_rootSet.mp hus
  have evV : aeval vs H=0 := hm.mem_rootSet.mp hvs
  have algV : IsAlgebraic ℚ vs := ⟨H,hm.ne_zero,evV⟩
  have mv : H=minpoly ℚ vs := minpoly.eq_of_irreducible_of_monic hi evV hm
  have uv : aeval us (minpoly ℚ vs)=0 := by rw [←mv]; exact evU
  obtain ⟨σ,hσ⟩ := minpoly.exists_algEquiv_of_root (K:=ℚ) algV uv
  let f : S →ₐ[ℚ] E := i.comp σ.toAlgHom
  have point : f.toRingHom us=v := by
    change i (σ us)=v
    rw [hσ,iv]
  refine ⟨QS.map f.toRingHom,NS.map f.toRingHom,sQM.map _,sNM.map _,?_,?_,?_,?_,?_⟩
  · rw [natDegree_map_eq_of_injective f.injective,
      ← natDegree_map_eq_of_injective j.injective QS,jQ,
      natDegree_map_eq_of_injective k.injective]
  · rw [natDegree_map_eq_of_injective f.injective,
      ← natDegree_map_eq_of_injective j.injective NS,jN,
      natDegree_map_eq_of_injective k.injective]
  · rw [←Polynomial.map_mul,sProd,map_base]
  · change (NS.map f.toRingHom).eval v=0
    rw [←point,eval_map_apply,show NS.eval us=0 from sRoot,map_zero]
  · rw [←point,first_primitive_map,sZero,map_zero]

end
end RKResearch.Certified.Graded.NativeRootTransport
