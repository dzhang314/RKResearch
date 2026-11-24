module
public import RKCert.IntegralFactorGate
public import Mathlib.Data.List.Sublists

@[expose] public section
/-! # An actually checked small split-prime table works over all residue extensions -/
namespace RKCert.FixedFactor
open Polynomial
universe u
variable {α : Type*} {K : Type*} [Field K]

noncomputable def linearProduct (f : α→K) : List α → K[X]
  | [] => 1
  | z::s => (X-C (f z))*linearProduct f s

theorem mono_product (f : α→K) (s : List α) : (linearProduct f s).Monic := by
  induction s with
  | nil => exact monic_one
  | cons z s ih => exact (monic_X_sub_C _).mul ih

theorem degree_product (f : α→K) (s : List α) : (linearProduct f s).natDegree=s.length := by
  induction s with
  | nil => simp [linearProduct]
  | cons z s ih =>
    rw [linearProduct,natDegree_mul (monic_X_sub_C _).ne_zero (mono_product _ _).ne_zero,
      natDegree_X_sub_C,ih,List.length_cons,Nat.add_comm]

theorem map_product {E : Type*} [Field E] (φ : K→+*E) (f : α→K) (s : List α) :
    (linearProduct f s).map φ=linearProduct (fun z=>φ (f z)) s := by
  induction s with
  | nil => simp [linearProduct]
  | cons z s ih => simp [linearProduct,ih]

theorem endpoint_of_product (f : α→K) (l : List α) (w : K)
    (hh : (linearProduct f l).eval w=0) : ∃a∈l, w=f a := by
  induction l with
  | nil => simp [linearProduct] at hh
  | cons z l ih =>
    simp only [linearProduct,eval_mul,eval_sub,eval_X,eval_C,mul_eq_zero,sub_eq_zero] at hh
    rcases hh with eq|eq
    · exact ⟨z,List.mem_cons_self,eq⟩
    · obtain ⟨a,ha,he⟩:=ih eq; exact ⟨a,List.mem_cons_of_mem _ ha,he⟩

/-- Any monic divisor in an extension is literally the product of a sublist
of the given prime-field linear factors; no squarefreeness is needed. -/
theorem select_monic_factor (f : α→K) (l : List α) (P Q : K[X]) (hm : P.Monic)
    (fact : P*Q=linearProduct f l) :
    ∃t : List α, t.Sublist l ∧ P=linearProduct f t := by
  induction l generalizing P Q with
  | nil =>
    exact ⟨[],.refl _,hm.eq_one_of_isUnit (isUnit_of_dvd_one ⟨Q,fact.symm⟩)⟩
  | cons a l ih =>
    let Z : K[X] := X-C (f a)
    have zm : Z.Monic := monic_X_sub_C _
    have fac : P*Q=Z*linearProduct f l := fact
    have ev : P.eval (f a)*Q.eval (f a)=0 := by
      rw [←eval_mul,fac,eval_mul]; simp [Z]
    rcases mul_eq_zero.mp ev with pz|qz
    · obtain ⟨p,ep⟩ := dvd_iff_isRoot.mpr pz
      change P=Z*p at ep
      have pr : p*Q=linearProduct f l := mul_left_cancel₀ zm.ne_zero (by simpa only [ep,mul_assoc] using fac)
      obtain ⟨t,hh,he⟩:=ih p Q (zm.of_mul_monic_left (ep ▸ hm)) pr
      exact ⟨a::t,hh.cons_cons a,by change P=Z*_; rw [ep,he]⟩
    · obtain ⟨q,eq⟩:=dvd_iff_isRoot.mpr qz
      change Q=Z*q at eq
      have qr : P*q=linearProduct f l := mul_left_cancel₀ zm.ne_zero (by
        calc Z*(P*q)=P*Q := by rw [eq]; ac_rfl
             _ = _ := fac)
      obtain ⟨t,hh,he⟩:=ih P q hm qr
      exact ⟨t,hh.cons a,he⟩

/-- Executable coefficient recurrence for an explicitly listed split factor.
It is independent of classical decidability or the representation of polynomials. -/
def coeffs {R : Type*} [Ring R] : List R → ℕ → R
  | [], i => if i=0 then 1 else 0
  | a::l, 0 => -a*coeffs l 0
  | a::l, i+1 => coeffs l i-a*coeffs l (i+1)

theorem coeff_product (l : List K) (i : ℕ) : (linearProduct id l).coeff i=coeffs l i := by
  induction l generalizing i with
  | nil => simp [linearProduct,coeffs,coeff_one]
  | cons a l ih =>
    cases i with
    | zero => simp [linearProduct,coeffs,sub_mul,ih]
    | succ n => simp [linearProduct,coeffs,sub_mul,ih]

def checked {R : Type*} [CommRing R] [DecidableEq R] (L D : ℕ) (digits roots : List R) : Bool :=
  digits.sublists.all fun l=>decide (D<l.length) || roots.all fun a=>
    decide ((∑i∈Finset.range (D+1), (L/(i+2):ℕ)*coeffs l i*a^(i+2))≠0)

theorem of_checked (L D : ℕ) (digits roots : List K) (v : List K) (a : K)
    [DecidableEq K] (hc : checked L D digits roots=true) (hs : v.Sublist digits)
    (hn : v.length≤D) (ha : a∈roots) : moment L D (linearProduct id v) a≠0 := by
  have h:=List.all_eq_true.mp hc v (List.mem_sublists.mpr hs)
  simp only [Bool.or_eq_true,decide_eq_true_eq] at h
  have hA:=List.all_eq_true.mp (h.resolve_left (Nat.not_lt_of_ge hn)) _ ha
  exact of_decide_eq_true (by simpa only [moment,coeff_product] using hA)

theorem modular_table {p : ℕ} [Fact p.Prime] (F H : ℤ[X]) (L D : ℕ)
    (digits roots : List (ZMod p))
    (fprod : F.map (Int.castRingHom (ZMod p))=linearProduct id digits)
    (hprod : H.map (Int.castRingHom (ZMod p))=linearProduct id roots)
    (checked' : checked L D digits roots=true)
    {E : Type u} [Field E] [CharP E p] (P : E[X]) (w : E)
    (pm : P.Monic) (pdiv : P∣F.map (Int.castRingHom E)) (degP : P.natDegree≤D)
    (root : (H.map (Int.castRingHom E)).eval w=0) : moment L D P w≠0 := by
  let φ:=ZMod.castHom (dvd_refl p) E
  have intH : φ.comp (Int.castRingHom (ZMod p))=Int.castRingHom E := Subsingleton.elim ..
  have fp : F.map (Int.castRingHom E)=linearProduct φ digits := by
    rw [←intH,←map_map,fprod,map_product]; rfl
  have hp : H.map (Int.castRingHom E)=linearProduct φ roots := by
    rw [←intH,←map_map,hprod,map_product]; rfl
  obtain ⟨Q,fq⟩:=pdiv
  obtain ⟨t,ht,pt⟩:=select_monic_factor (fun x=>φ x) digits P Q pm (fq.symm.trans fp)
  obtain ⟨a,ha,wa⟩:=endpoint_of_product _ _ _ (hp ▸ root)
  have dt : t.length≤D := by rw [pt,degree_product] at degP; exact degP
  have hg:=of_checked L D digits roots t a checked' ht dt ha
  have e : P=(linearProduct id t).map φ := pt.trans (map_product φ id t).symm
  rw [e,wa,←map_moment]
  exact fun z=>hg (φ.injective (z.trans φ.map_zero.symm))

end RKCert.FixedFactor
