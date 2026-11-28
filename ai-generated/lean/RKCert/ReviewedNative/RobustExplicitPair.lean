module

public import RKCert.ReviewedNative.ExactExplicitPortfolio
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ExactExplicitPortfolio
open FiniteRootedTree
open scoped Matrix

/-- Denominator-free residual of the ordinary order equation for one tree. -/
def residual {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (t : FiniteRootedTree) : R :=
  (t.factorial : R) * (b ⬝ᵥ Φ t A) - 1

/-- A fixed pair of residuals guards exactness after *arbitrary*
unital scalar extension to a nontrivial ring. -/
def PairCert (s p : ℕ) (t₀ t₁ : FiniteRootedTree) (R : Type*) [CommRing R] : Prop :=
  ∃ (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (a₀ a₁ : R),
    ERK A ∧ HasOrder p A b ∧ a₀ * residual A b t₀ + a₁ * residual A b t₁ = 1

variable {R S : Type*} [CommRing R] [CommRing S]
variable {s p : ℕ} {t₀ t₁ : FiniteRootedTree}

theorem residual_map (f : R →+* S) (A : Matrix (Fin s) (Fin s) R)
    (b : Fin s → R) (t : FiniteRootedTree) :
    f (residual A b t) = residual (A.map f) (f ∘ b) t := by
  simp only [residual, map_sub, map_one, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]

theorem PairCert.map (h : PairCert s p t₀ t₁ R) (f : R →+* S) :
    PairCert s p t₀ t₁ S := by
  obtain ⟨A,b,x,y,ha,hp,hr⟩ := h
  refine ⟨A.map f, f ∘ b, f x, f y, ?_, hp.map f, ?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [ha hij, map_zero]
  · simpa only [map_add, map_mul, residual_map, map_one] using congrArg f hr

theorem PairCert.exact [Nontrivial R] (h : PairCert s p t₀ t₁ R)
    (h₀ : (t₀.order : Nat) ≤ p+1) (h₁ : (t₁.order : Nat) ≤ p+1) :
    Exact s p R := by
  obtain ⟨A,b,x,y,ha,hp,hr⟩ := h
  refine ⟨A,b,ha,hp,?_⟩
  intro hn
  unfold residual at hr
  rw [hn t₀ h₀, hn t₁ h₁, sub_self, mul_zero, mul_zero, zero_add] at hr
  exact zero_ne_one hr

private theorem ext_fst (z : R × S) : z.1 = (RingHom.fst R S) z := rfl
private theorem ext_snd (z : R × S) : z.2 = (RingHom.snd R S) z := rfl

theorem PairCert.prod (h : PairCert s p t₀ t₁ R) (k : PairCert s p t₀ t₁ S) :
    PairCert s p t₀ t₁ (R × S) := by
  obtain ⟨A,b,x₀,x₁,ha,hA,hr⟩ := h
  obtain ⟨B,c,y₀,y₁,hb,hB,hs⟩ := k
  let T : Matrix (Fin s) (Fin s) (R × S) := Matrix.of fun i j => (A i j, B i j)
  let w : Fin s → R × S := fun i => (b i, c i)
  refine ⟨T,w,(x₀,y₀),(x₁,y₁),?_ ,?_ ,?_⟩
  · intro i j hij
    exact Prod.ext (ha hij) (hb hij)
  · intro t ht
    apply Prod.ext
    · rw [ext_fst, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hA t ht
    · rw [ext_snd, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ]
      exact hB t ht
  · apply Prod.ext
    · rw [ext_fst, map_add, map_mul, map_mul, residual_map, residual_map]
      exact hr
    · rw [ext_snd, map_add, map_mul, map_mul, residual_map, residual_map]
      exact hs

/-- The commutative clean ring condition. -/
def Clean {T : Type*} [CommRing T] : Prop :=
  ∀ a : T, ∃ (u : Tˣ) (e : T), e*e=e ∧ a=(u:T)+e

theorem Clean.quotient (h : Clean (T := R)) (I : Ideal R) :
    Clean (T := R ⧸ I) := by
  intro a
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨u,e,he,hx⟩ := h x
  let f := Ideal.Quotient.mk I
  refine ⟨Units.map f u,f e,?_,?_⟩
  · rw [←map_mul,he]
  · exact (congrArg f hx).trans (map_add f _ _)

private theorem term_sum_map (ds : List (Int × Nat)) (f : R →+* S) :
    f ((ds.map (fun z => (z.1:R)*(z.2:R))).sum) =
      (ds.map (fun z => (z.1:S)*(z.2:S))).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons, List.sum_cons, map_add, map_mul,
        map_intCast, map_natCast, ih]

private noncomputable def split (e : R) (he : e*e=e) :
    R ≃+* (R ⧸ Ideal.span {e}) × (R ⧸ Ideal.span {1-e}) := by
  let I : Ideal R := Ideal.span {e}
  let J : Ideal R := Ideal.span {1-e}
  have hIJ : IsCoprime I J := (Ideal.isCoprime_span_singleton_iff e (1-e)).2
    ⟨1,1,by ring⟩
  have hab : e*(1-e)=0 := by rw [mul_sub,mul_one,he,sub_self]
  have hbot : I*J=⊥ := by
    dsimp [I,J]
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_bot,hab]
  exact ((RingEquiv.quotientBot R).symm.trans
    (Ideal.quotEquivOfEq hbot.symm)).trans (Ideal.quotientMulEquivQuotientProd I J hIJ)

/-- Select chart denominators by clean decompositions and glue the
robust residual certificates. Charts may give the trivial tableau
in a zero factor; the conclusion has exact order in nonzero rings. -/
theorem PairCert.clean_of_unit_sum {T : Type u} [CommRing T] (hc : Clean (T := T))
    (ds : List (Int × Nat))
    (hs : IsUnit ((ds.map (fun z => (z.1:T)*(z.2:T))).sum))
    (charts : ∀ (U : Type u) [CommRing U], ∀ z ∈ ds,
       IsUnit (z.2 : U) → PairCert s p t₀ t₁ U) :
    PairCert s p t₀ t₁ T := by
  induction ds generalizing T with
  | nil =>
      simp only [List.map_nil,List.sum_nil] at hs
      have hz : (0:T)=1 := by
        obtain ⟨u,hu⟩ := hs
        have hh := u.mul_inv
        rw [hu,zero_mul] at hh
        exact hh
      have : Subsingleton T := subsingleton_of_zero_eq_one hz
      exact ⟨0,0,0,0,fun _ _ _ => Subsingleton.elim _ _,
            fun _ _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | cons z ds ih =>
      let a : T := (z.1:T)*(z.2:T)
      let b : T := (ds.map (fun t => (t.1:T)*(t.2:T))).sum
      change IsUnit (a+b) at hs
      obtain ⟨u,hu⟩ := hs
      let ainv : T := a * (↑(u⁻¹) : T)
      let binv : T := b * (↑(u⁻¹) : T)
      have hab : ainv+binv=1 := by
        dsimp [ainv,binv]
        rw [←add_mul,←hu]
        exact u.mul_inv
      obtain ⟨v,e,he,ha⟩ := hc ainv
      let I : Ideal T := Ideal.span {e}
      let J : Ideal T := Ideal.span {1-e}
      let f := Ideal.Quotient.mk I
      let g := Ideal.Quotient.mk J
      have hef : f e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      have hge : g e = 1 := by
        have hgzero : g (1-e)=0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        rw [map_sub,map_one] at hgzero
        exact (sub_eq_zero.mp hgzero).symm
      have hI : IsUnit (f ainv) := by
        rw [ha,map_add,hef,add_zero]
        exact v.isUnit.map f
      have hI' : IsUnit (z.2 : T ⧸ I) := by
        dsimp [ainv,a] at hI
        simp only [map_mul,map_intCast,map_natCast] at hI
        exact ((Commute.all _ _).isUnit_mul_iff.mp
          ((Commute.all _ _).isUnit_mul_iff.mp hI).1).2
      have hJ : IsUnit (g binv) := by
        have hh := congrArg g hab
        rw [map_add,map_one,ha,map_add,hge] at hh
        have hzero : g (v:T)+g binv=0 := by
          apply add_right_cancel (b := (1 : T ⧸ J))
          simpa only [zero_add, add_right_comm] using hh
        have eq : g binv = -(g (v:T)) := by
          calc
            g binv = (g (v:T)+g binv)-g (v:T) := by ring
            _ = -(g (v:T)) := by rw [hzero, zero_sub]
        rw [eq]
        exact (v.isUnit.map g).neg
      have hJ' : IsUnit ((ds.map (fun z => (z.1:T ⧸ J)*(z.2:T ⧸ J))).sum) := by
        dsimp [binv] at hJ
        rw [map_mul,term_sum_map] at hJ
        exact ((Commute.all _ _).isUnit_mul_iff.mp hJ).1
      have cI := charts (T ⧸ I) z List.mem_cons_self hI'
      have cJ := ih (hc.quotient J) hJ'
        (fun U inst d hd hu => charts U d (List.mem_cons_of_mem _ hd) hu)
      exact (cI.prod cJ).map (split e he).symm.toRingHom

/-- The literal two-tree chart receipts only need integer Bézout
coefficients for the cleared numerators. -/
theorem PairCert.of_integer_receipts
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ha : ERK A) (ho : HasOrder p A b)
    (d₀ d₁ n₀ n₁ e₀ e₁ : Int)
    (h₀ : (d₀:R)*residual A b t₀=(n₀:R))
    (h₁ : (d₁:R)*residual A b t₁=(n₁:R))
    (h : e₀*n₀+e₁*n₁=1) : PairCert s p t₀ t₁ R := by
  refine ⟨A,b,(e₀:R)*(d₀:R),(e₁:R)*(d₁:R),ha,ho,?_⟩
  simp only [mul_assoc,h₀,h₁]
  have hh := congrArg (Int.castRingHom R) h
  simp only [map_add,map_mul,map_one] at hh
  exact hh

/-- Cast a literal integer Bézout sum into the coefficient ring,
then perform the clean splitting. No chart is required at a
denominator that is not a unit on its chosen factor. -/
theorem PairCert.clean_of_bezout {T : Type u} [CommRing T] (hc : Clean (T := T))
    (ds : List (Int × Nat)) {g : Nat}
    (hs : (ds.map (fun z => z.1*(z.2:Int))).sum = (g:Int))
    (hunit : IsUnit (g:T))
    (charts : ∀ (U : Type u) [CommRing U], ∀ z ∈ ds,
       IsUnit (z.2 : U) → PairCert s p t₀ t₁ U) :
    PairCert s p t₀ t₁ T := by
  have map_sum (terms : List (Int × Nat)) :
      ((terms.map (fun z => z.1*(z.2:Int))).sum : T) =
        (terms.map (fun z => (z.1:T)*(z.2:T))).sum := by
    induction terms with
    | nil => simp
    | cons z tail ih => simp [ih]
  apply clean_of_unit_sum hc ds _ charts
  rw [←map_sum,hs,Int.cast_natCast]
  exact hunit

end RKResearch.Certified.ExactExplicitPortfolio

#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.map
#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.prod
#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.exact

#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.clean_of_unit_sum

#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.of_integer_receipts
#print axioms RKResearch.Certified.ExactExplicitPortfolio.PairCert.clean_of_bezout
