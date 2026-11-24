module
public import RKCert.FiveDebutObservations
@[expose] public section
namespace RKCert.FiveDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s}
noncomputable section

def first3 (z : Fin 5→K) (i:Fin 3):K := z (Fin.castLE (by decide) i)
def first4 (z : Fin 5→K) (i:Fin 4):K := z (Fin.castLE (by decide) i)

/-- Normalized scalar observations at five *distinct chronological*
nonzero outside debut clocks, in increasing physical order. -/
structure ScalarObservations (z W : Fin 5→K) : Prop where
  injective : Function.Injective z
  nonzero : ∀i,z i≠0
  scale : ∃ t:K, t≠0 ∧ ∀i, first4 W i=t*(first4 z i)^2*(Lagrange.nodal Finset.univ (first4 z)).derivative.eval (first4 z i)
  old : ∃ Q:K[X], Q.degree<(2:WithBot ℕ) ∧ ∀i,
    (primitive (X*Lagrange.nodal Finset.univ (first3 z))).eval (first3 z i)=first3 W i*Q.eval (first3 z i)
  first : ∃ Q:K[X], Q.degree<(2:WithBot ℕ) ∧ ∀i,
    (primitive (X*Lagrange.nodal Finset.univ (first4 z))).eval (z i)=W i*Q.eval (z i)
  second : ∃ Q:K[X], Q.degree<(3:WithBot ℕ) ∧ ∀i,
    (primitive (X^2*Lagrange.nodal Finset.univ (first4 z))).eval (z i)=W i*Q.eval (z i)

/-- Everything on the scalar side is derived on the original tableau:
physical chronological distinctness, all equal-clock and origin charges,
the fifth diagonal refund, barycentric amplitude scale, and three primitive
tests. The degree-seven flag is the last one used. -/
theorem original_refunded_five (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k)) :
    ∃ z W : Fin 5→K, ScalarObservations z W := by
  obtain ⟨h⟩:=original_five_data ha ho hp inv alg inc (band 1 (by decide)).le (band 2 (by decide)).le
  have i3 (l:Fin 3):h.i5 (Fin.castLE (by decide : 3≤5) l)=h.ix l:=by
    change h.i5 l.castSucc.castSucc=_
    simp only [FiveData.i5,FiveData.i4,Fin.snoc_castSucc]
  have i4 (l:Fin 4):h.i5 (Fin.castLE (by decide : 4≤5) l)=h.i4 l:=by
    change h.i5 l.castSucc=_
    simp only [FiveData.i5,Fin.snoc_castSucc]
  have Z3:first3 h.z5=h.z3:=funext (fun l=>congrArg (nodes A) (i3 l))
  have Z4:first4 h.z5=h.z4:=funext (fun l=>congrArg (nodes A) (i4 l))
  have W3:first3 h.W5=h.W3:=funext (fun l=>congrArg w (i3 l))
  have W4:first4 h.W5=h.W4:=funext (fun l=>congrArg w (i4 l))
  obtain ⟨o,a,c⟩:=h.actual_observations ha inv alg inc (band 1 (by decide)).le (band 2 (by decide)).le
  refine ⟨h.z5,h.W5,h.inj5,h.nz5,?_,?_,?_,?_⟩
  · rw [Z4,W4]
    exact h.actual_scale ha inv alg inc band
  · rwa [Z3,W3]
  · rwa [Z4]
  · rwa [Z4]

end
end RKCert.FiveDebut
