module

public import RKCert.Dirk15K2Factor
public import RKCert.Dirk15TwoEndedPivots

@[expose] public section

/-! # The active reversed K2 pivot is a true omitted factor root

The clock-one auxiliary factor is removed only at the actual nonzero
reflected pivot. This permits reuse of the original terminal-zero cut
without granting extra claims on any other rows with clock one.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b v : Vec K 20}

namespace Order15K2Head.TrueVisibleFactor
variable {h : Order15K2Head A b v} {D : h.head.DeletedPencil}
variable (V : h.TrueVisibleFactor D)

theorem true_reverse_pivot (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hm : Module.finrank K (marked A 15 4)=2) :
    ∃ i : Fin 20, i≠Fin.last 19 ∧ mirror A i≠0 ∧ b i≠0 ∧ v i=0 ∧
      V.P.eval (nodes A i)≠0 ∧ D.D.eval (nodes A i)=0 ∧ A i i=0 ∧
      paidMoment (reflectPolynomial V.P) (mirror A i) 1=0 ∧
      paidMoment (reflectPolynomial V.P) (mirror A i) 2=0 := by
  let D' := (1-Polynomial.X)*D.D
  have clean (i : Fin 20) (nt : i≠Fin.last 19) (bi : b i≠0) (vi : v i=0)
      (pn : V.P.eval (nodes A i)≠0) : D'.eval (nodes A i)=0 := by
    by_cases e : nodes A i=1
    · simp [D',e]
    · have d := V.weighted_good i nt e bi
      rw [vi,zero_mul] at d
      simp [D',d]
  obtain ⟨i,it,iy,ib,iv,ip,id,ia,h1,h2⟩ := order15_reverse_quartic_cut
    (D:=D') ha ho H hm (order15_minimal_reverse_nonlocal ha ho H)
    V.nonzero V.degree h.paid V.matchMark clean
  have de : (1-nodes A i)*D.D.eval (nodes A i)=0 := by
    simpa [D'] using id
  have c : 1-nodes A i≠0 := iy
  exact ⟨i,it,iy,ib,iv,ip,(mul_eq_zero.mp de).resolve_left c,ia,h1,h2⟩

end Order15K2Head.TrueVisibleFactor
end
end RKCert.Paired
