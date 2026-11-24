module
public import RKCert.ReviewedNative.OrderNineSixOnQuartic

@[expose] public section

/-! # Off-eighth physical residual yields one of the two exact quartic divisors -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] 

variable [LinearOrder K] [IsStrictOrderedRing K]
theorem order9_actual_five_six_off_eighth
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (N : (offKnots A).card=5) (M : (cleanKnots A).card=6)
    (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (dP : P.natDegree=2) (pn : P≠0)
    (fit : ∀ i,OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i)
    (fg : ActualSixOnFG A P) (off : OneOff.g A (lowPrefix10 (7:Fin 10))≠0) :
    let h := nodes A (lowPrefix10 fg.first)
    let f := nodes A (lowPrefix10 (7:Fin 10))
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let v := nodes A (lowPrefix10 (Fin.last 9))
    let a := 3*(u-v)
    let b := 4*u^2-5*u*v+2*v-1
    let D := C a*X-C b
    let Q := nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1)
    a≠0 ∧ a*f=b ∧
      ((fg.first.val=4 ∧ ∃ t : K,t≠0 ∧ P∣Q-C t*(D*(X^2*(X-C h)^2))) ∨
       (fg.first.val=5 ∧ ∃ t : K,t≠0 ∧ P∣Q-C t*(D*primitive (X*P)))) := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  dsimp only
  let h := nodes A (lowPrefix10 fg.first)
  let f := nodes A (lowPrefix10 (7:Fin 10))
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let a := 3*(u-v)
  let z := 4*u^2-5*u*v+2*v-1
  let D := C a*X-C z
  let Q := nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1)
  let S := firstSixOff A
  let T := offKnots A
  have uv : u≠v := fun e=>(by decide : (2:Fin 4)≠3) (fg.root_set_injective e)
  have an : a≠0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr uv)
  have fx : a*f=z := by
    have e := fg.eighth_off_clock off
    change RKCert.Paired.radauLateL u v f=0 at e
    dsimp only [a,z]
    unfold RKCert.Paired.radauLateL at e
    linear_combination -e
  have eqD : D=C a*(X-C f) := by
    dsimp only [D]
    rw [mul_sub,←map_mul,fx]
  obtain ⟨ds,parts⟩ := order9_actual_five_six_quartic_remainders ha ho N M hF dP pn fit fg
  obtain ⟨⟨k,kn,kd⟩,_⟩ := order9_five_six_remainder ha ho N M hF P dP.le fit
  obtain ⟨bij,_,_,_⟩ := order9_five_six_ten_distinct_prefix ha ho N M
  change Function.Bijective (fun i : Fin 10=>lowNonterminalStateAt ha (lowPrefix10 i)) at bij
  have ss : S⊆T := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact mem_offKnots.mpr ⟨_,(Finset.mem_filter.mp hi).2,rfl⟩
  have fn : f∉S := by
    intro hx
    obtain ⟨i,hi,e⟩ := Finset.mem_image.mp hx
    have gi := (Finset.mem_filter.mp hi).2
    have es : lowStateAt A (lowPrefix10 (firstSixPrefix i))=lowStateAt A (lowPrefix10 7) :=
      lowState_eq_iff.mpr ⟨by simp [gi,off],e⟩
    have x := bij.1 ((lowNonterminalState_eq_iff ha (fun q=>(gi q).elim)
      (fun q=>(off q).elim)).mpr es)
    have xi := congrArg Fin.val x
    change i.val=7 at xi
    have := i.isLt
    omega
  have ft : f∈T := mem_offKnots.mpr ⟨_,off,rfl⟩
  have eST : insert f S = T := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset ft ss) (by rw [Finset.card_insert_of_notMem fn,ds,N])
  have hHull : nodalHull T=(X-C f)*nodalHull S := by
    rw [←eST,nodalHull,Finset.prod_insert fn]
    rfl
  change P∣Q-C k*nodalHull T at kd
  rw [hHull] at kd
  have transfer (W : K[X]) {c : K} (cn:c≠0) (dv:P∣nodalHull S-C c*W) :
      ∃ t : K,t≠0 ∧ P∣Q-C t*(D*W) := by
    obtain ⟨U,eU⟩ := kd
    obtain ⟨V,eV⟩ := dv
    let t := k*c/a
    have e : C t*D=C k*(X-C f)*C c := by
      rw [eqD,←mul_assoc,←map_mul]
      have te : t*a=k*c := div_mul_cancel₀ _ an
      rw [te,map_mul]
      ring
    refine ⟨t,div_ne_zero (mul_ne_zero kn cn) an,⟨U+C k*(X-C f)*V,?_⟩⟩
    rw [←mul_assoc,e]
    linear_combination eU + C k*(X-C f)*eV
  change a≠0 ∧ a*f=z ∧ _
  refine ⟨an,fx,?_⟩
  rcases parts with ⟨p4,c,cn,cv⟩|⟨p5,c,cn,cv⟩
  · exact Or.inl ⟨p4,transfer _ cn cv⟩
  · exact Or.inr ⟨p5,transfer _ cn cv⟩
end RKResearch.Certified.Graded.MultiOff
