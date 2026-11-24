module

public import RKCert.CompanionBandMinor

@[expose] public section

/-! # Direct sparse arithmetic for every fixed replay companion moment entry -/
namespace RKCert.Compound
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

def monomialMomentWeight (M j w : ℕ) (u : R) (d : ℕ) : R :=
  u^d * (((M/(j+d+1):ℕ):R) - if w=0 then 0 else u*((M/(j+d+2):ℕ):R))

private theorem scaled_C_X_pow (M j cap : ℕ) (u a : R) {d : ℕ} (dk : d≤cap) :
    scaledMoment M j cap u (C a*X^d)=((M/(j+d+1):ℕ):R)*u^d*a := by
  unfold scaledMoment
  let i : Fin (cap+1) := ⟨d,by omega⟩
  rw [Finset.sum_eq_single i]
  · simp [i]
  · intro t _ h
    have ne : t.val≠d := fun he=>h (Fin.ext he)
    simp [ne]
  · simp

theorem weighted_C_X_pow (M j cap w : ℕ) (u a : R) {d : ℕ} (dk : d≤cap) (w1 : w≤1) :
    scaledMoment M j (cap+w) u ((1-X)^w*(C a*X^d))=
      a*monomialMomentWeight M j w u d := by
  have W : w=0∨w=1 := by omega
  rcases W with e|e
  · subst w
    simp only [pow_zero,one_mul,Nat.add_zero,monomialMomentWeight,ite_true,sub_zero]
    rw [scaled_C_X_pow M j cap u a dk]
    ring
  · subst w
    rw [pow_one,sub_mul,one_mul]
    let L := scaledMomentLinear M j (cap+1) u
    change L (C a*X^d-X*(C a*X^d))=_
    rw [map_sub,show X*(C a*X^d)=C a*X^(d+1) by rw [pow_succ]; ring]
    change scaledMoment M j (cap+1) u (C a*X^d)-
      scaledMoment M j (cap+1) u (C a*X^(d+1))=_
    rw [scaled_C_X_pow M j (cap+1) u a (d:=d) (by omega),
      scaled_C_X_pow M j (cap+1) u a (d:=d+1) (by omega)]
    unfold monomialMomentWeight
    simp only [Nat.one_ne_zero,ite_false]
    rw [show j+(d+1)+1=j+d+2 by omega,pow_succ]
    ring

def tagMoment (M j w : ℕ) (u : R) (t : Option (ℕ×ℤ)) : R :=
  match t with
  | none => 0
  | some t => (t.2:R)*monomialMomentWeight M j w u t.1

theorem tagMoment_exact (M j cap w : ℕ) (u : R) (L : List (ℕ×ℕ)) (size : L.length≤cap)
    (w1 : w≤1) :
    tagMoment M j w u (bandTag L)=
      scaledMoment M j (cap+w) u ((1-X)^w*bandPolynomial L) := by
  cases h : bandTag L with
  | none => simp [tagMoment,bandPolynomial,h,scaledMoment]
  | some t =>
    have d : t.1≤cap := (bandTag_degree L h).trans size
    simp only [tagMoment,bandPolynomial,h]
    exact (weighted_C_X_pow M j cap w u _ d w1).symm

def tagLinearMoment (M j w : ℕ) (u a₀ a₁ : R) (t : Option (ℕ×ℤ)) : R :=
  match t with
  | none => 0
  | some t => (t.2:R)*(a₀*monomialMomentWeight M j w u t.1+
      a₁*monomialMomentWeight M j w u (t.1+1))

theorem tagLinearMoment_exact (M j cap w : ℕ) (u a₀ a₁ : R) (L : List (ℕ×ℕ)) (size : L.length+1≤cap)
    (w1 : w≤1) :
    tagLinearMoment M j w u a₀ a₁ (bandTag L)=
      scaledMoment M j (cap+w) u ((1-X)^w*((C a₁*X+C a₀)*bandPolynomial L)) := by
  cases h : bandTag L with
  | none => simp [tagLinearMoment,bandPolynomial,h,scaledMoment]
  | some t =>
    have d := bandTag_degree L h
    simp only [tagLinearMoment,bandPolynomial,h]
    have de : (C a₁*X+C a₀)*(C (t.2:R)*X^t.1)=
        C (a₀*(t.2:R))*X^t.1+C (a₁*(t.2:R))*X^(t.1+1) := by
      simp only [map_mul,pow_succ]
      ring
    rw [de]
    let J : R[X] →ₗ[R] R := (scaledMomentLinear M j (cap+w) u).comp (LinearMap.mulLeft R ((1-X)^w))
    change _=J (C (a₀*(t.2:R))*X^t.1+C (a₁*(t.2:R))*X^(t.1+1))
    rw [map_add]
    change _=scaledMoment M j (cap+w) u ((1-X)^w*(C (a₀*(t.2:R))*X^t.1))+
      scaledMoment M j (cap+w) u ((1-X)^w*(C (a₁*(t.2:R))*X^(t.1+1)))
    rw [weighted_C_X_pow M j cap w u _ (by omega) w1,
      weighted_C_X_pow M j cap w u _ (by omega) w1]
    ring

def sparseMomentEntry {n k h : ℕ} (E : OrderedAxes n (k+1) h) (M j w : ℕ) (u : R)
    (b : Fin (n+1)→R) (i t : Fin h) : R :=
  if (E.axis t (Fin.last k)).val+1<n then tagMoment M j w u (bandTag (fullBandPairs E i t))
  else (List.ofFn fun s : Fin (k+1) => (-1:R)^(s.val+k)*
    tagLinearMoment M j w u (b (E.axis i s).castSucc)
      (if E.axis i s=E.axis t (Fin.last k) then b (Fin.last n) else 0)
      (bandTag (reducedBandPairs E i t s))).sum

theorem sparseMomentEntry_exact {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (M j w : ℕ) (w1 : w≤1) (u : R) (b : Fin (n+1)→R) (i t : Fin h) :
    sparseMomentEntry E M j w u b i t=rawMomentMatrix M j w u b (E.index i) (E.index t) := by
  unfold sparseMomentEntry rawMomentMatrix
  rw [ordered_minor_expansion]
  by_cases l : (E.axis t (Fin.last k)).val+1<n
  · simp only [l,ite_true]
    exact tagMoment_exact M j (k+1) w u _ (by simp [fullBandPairs]) w1
  · simp only [l,ite_false]
    let L : R[X] →ₗ[R] R := (scaledMomentLinear M j (k+1+w) u).comp (LinearMap.mulLeft R ((1-X)^w))
    change (List.ofFn _).sum=L (∑ s : Fin (k+1),(-1:R[X])^(s.val+k)*
      ((if E.axis i s=E.axis t (Fin.last k) then C (b (Fin.last n))*X else 0)+
        C (b (E.axis i s).castSucc))*bandPolynomial (reducedBandPairs E i t s))
    rw [List.sum_ofFn,map_sum]
    apply Finset.sum_congr rfl
    intro s _
    let a₁ := if E.axis i s=E.axis t (Fin.last k) then b (Fin.last n) else 0
    have z : (if E.axis i s=E.axis t (Fin.last k) then C (b (Fin.last n))*X else 0)=C a₁*X := by
      by_cases h : E.axis i s=E.axis t (Fin.last k) <;> simp [a₁,h]
    rw [z,show (-1:R[X])^(s.val+k)*(C a₁*X+C (b (E.axis i s).castSucc))*
      bandPolynomial (reducedBandPairs E i t s)=
        ((-1:R)^(s.val+k)) • ((C a₁*X+C (b (E.axis i s).castSucc))*
          bandPolynomial (reducedBandPairs E i t s)) by rw [smul_eq_C_mul]; simp [mul_assoc]]
    rw [map_smul,smul_eq_mul]
    change _ = (-1:R)^(s.val+k)*scaledMoment M j (k+1+w) u
      ((1-X)^w*((C a₁*X+C (b (E.axis i s).castSucc))*bandPolynomial (reducedBandPairs E i t s)))
    rw [←tagLinearMoment_exact M j (k+1) w u _ _ _ (by simp [reducedBandPairs]) w1]

end RKCert.Compound
