import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneGapDiagonals

open scoped BigOperators
variable {K : Type*} [CommRing K]

/-- The sixth blocked quotient has no nonzero vector after the fourth
regular reverse row and the preceding physical ghost have been sampled. -/
theorem sixth_pivot [IsDomain K] {u r μ θ a : K}
    (hr : r ≠ 0) (hu : u ≠ 0) (hv : μ*r=0) (hz : θ*u=μ*a) :
    μ=0 ∧ θ=0 := by
  have hm := (mul_eq_zero.mp hv).resolve_right hr
  exact ⟨hm, (mul_eq_zero.mp (by simpa [hm] using hz)).resolve_right hu⟩

/-- The seventh quotient has the analogous four scalar pivots on the
two extra regular and two extra ghost samples. -/
theorem seventh_pivot [IsDomain K] {v b z x rv rb rz rx uz ux a c h k : K}
    (hvb : v ≠ b) (hzx : z ≠ x) (hrv : rv ≠ 0) (hrb : rb ≠ 0)
    (huz : uz ≠ 0) (hux : ux ≠ 0)
    (hv : (a+c*v)*rv=0) (hb : (a+c*b)*rb=0)
    (hz : (h+k*z)*uz=(a+c*z)*rz) (hx : (h+k*x)*ux=(a+c*x)*rx) :
    a=0 ∧ c=0 ∧ h=0 ∧ k=0 := by
  have h1 := (mul_eq_zero.mp hv).resolve_right hrv
  have h2 := (mul_eq_zero.mp hb).resolve_right hrb
  have h3 : c*(v-b)=0 := by linear_combination h1-h2
  have hc := (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hvb)
  have ha : a=0 := by simpa [hc] using h1
  have h4 : h+k*z=0 :=
    (mul_eq_zero.mp (by simpa [ha,hc] using hz)).resolve_right huz
  have h5 : h+k*x=0 :=
    (mul_eq_zero.mp (by simpa [ha,hc] using hx)).resolve_right hux
  have h6 : k*(z-x)=0 := by linear_combination h4-h5
  have hk := (mul_eq_zero.mp h6).resolve_right (sub_ne_zero.mpr hzx)
  exact ⟨ha,hc,by simpa [hk] using h4,hk⟩

/-- Left application by the literal lower triangular reverse array. -/
def applyArray {s : ℕ} (N : Fin s → Fin s → K) (u : Fin s → K) (i : Fin s) : K :=
  ∑ j, N i j * u j

theorem apply_first {s : ℕ} {N : Fin s → Fin s → K}
    (hN : ∀ i j, i < j → N i j=0) {u : Fin s → K} {i : Fin s}
    (hpre : ∀ j, j < i → u j=0) :
    applyArray N u i=N i i*u i := by
  unfold applyArray
  apply Finset.sum_eq_single i
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with h | h
    · simp [hpre j h]
    · simp [hN i j h]
  · simp

theorem apply_first_commutator {s : ℕ} {N : Fin s → Fin s → K}
    (hN : ∀ i j, i < j → N i j=0) (Y : Fin s → K) {u : Fin s → K} {i : Fin s}
    (hpre : ∀ j, j < i → u j=0) :
    Y i * applyArray N u i - applyArray N (fun j => Y j*u j) i
      - applyArray N (applyArray N u) i= -(N i i)^2*u i := by
  have hy : ∀ j, j<i → Y j*u j=0 := by
    intro j h
    simp [hpre j h]
  have hn : ∀ j, j<i → applyArray N u j=0 := by
    intro j h
    rw [apply_first hN (i:=j) (fun k hk => hpre k (lt_trans hk h)), hpre j h, mul_zero]
  rw [apply_first hN hpre, apply_first hN hy, apply_first hN hn,
    apply_first hN hpre]
  ring

/-- The commutator's zero row forces the literal first supported
diagonal to vanish, with no ordering assumption on the coefficients. -/
theorem first_diagonal_zero [IsDomain K] {d u : K} (hu : u≠0)
    (h : -d^2*u=0) : d=0 := by
  have h' : d*d*u=0 := by linear_combination -h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hu)).elim id id

/-- Kernel transfer in the late reverse chart, including (1+q=0). -/
theorem kernel_transfer {X x q η nv nYv nNv np nMark : K}
    (hC : X*nv-nYv-nNv=0) (hMark : nMark=nYv-x*nv)
    (hNv : nNv=q*nMark-η*np) :
    (1+q)*nMark=(X-x)*nv+η*np := by
  linear_combination -hC+hMark-hNv

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneGapDiagonals
