module
public import RKCert.GradeSeparation
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial
variable {K : Type*} [Field K] {s p m : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}
noncomputable section

/-- A scalar weight with constant moments detects every nonconstant coefficient
at the *even* budget, provided both candidate and unknown vanish at zero. -/
theorem identify_coefficients (ho : HasTreeOrderAtLeast A b p) (hm : 2*m≤p)
    {a g : Fin (m+1) → K} (a0 : a 0=0) (g0 : g 0=0) (B : K)
    (ha : ∀ k:Fin m, (∑ j:Fin (m+1), a j / ((k.val+j.val+1:ℕ):K)) = B)
    (hg : ∀ k:Fin m, (∑ j:Fin (m+1), g j / ((k.val+j.val+1:ℕ):K)) = 1) :
    a = B • g := by
  have he (k:Fin m) :
      (∑ j:Fin m, (a j.succ-B*g j.succ)/((k.val+j.val+2:ℕ):K))=0 := by
    have h1 := ha k
    have h2 := hg k
    rw [Fin.sum_univ_succ,a0,zero_div,zero_add] at h1
    rw [Fin.sum_univ_succ,g0,zero_div,zero_add] at h2
    simp only [Fin.val_succ,Nat.add_assoc] at h1 h2
    simp only [sub_div,mul_div_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp only [Nat.add_assoc]
    rw [h1,h2,mul_one,sub_self]
  have h := moments_detect ho (d:=2) (by decide) (by omega) (fun i j => by omega) _ he
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [a0,g0]
  · exact sub_eq_zero.mp (h j)

theorem polyEval_node (a : Fin (m+1)→K) (i:Fin s) :
    polyEval A m a i=∑ j:Fin (m+1), a j*(nodes A i)^j.val := by
  simp [polyEval_apply,Finset.sum_apply,normTree_bush]

/-- From an actual terminal cardinal in the tree span, with clean origin and
terminal clocks, recover the class of the cardinal and its quadrature weight.
No positivity or support pruning is used. -/
theorem identify_cardinal (ho : HasTreeOrderAtLeast A b p) (hm : 2*m≤p) (hm' : 1≤m)
    (o t:Fin s) (h0 : nodes A o=0) (h1 : nodes A t=1)
    (clean0 : ∀f∈zeroSpace A m, f o=0) (clean1 : ∀f∈zeroSpace A m, f t=0)
    (hcard : Pi.single t (1:K)∈treeSpace A m)
    (g : Fin (m+1)→K) (g0:g 0=0)
    (hg : ∀ k:Fin m, (∑ j:Fin (m+1),g j/((k.val+j.val+1:ℕ):K))=1) :
    Pi.single t (1:K)-(b t) • polyEval A m g∈zeroSpace A m ∧
    b t*(∑ j:Fin (m+1),g j)=1 := by
  classical
  have hot:o≠t := by intro e; rw [← e,h0] at h1; exact zero_ne_one h1
  obtain ⟨a,ha⟩ := exists_poly_zeroSpace ho (by omega) hcard
  have hao : a 0=0 := by
    have hz:=clean0 _ ha
    rw [Pi.sub_apply,Pi.single_eq_of_ne hot,zero_sub,neg_eq_zero,polyEval_node,
      Fin.sum_univ_succ,h0] at hz
    simpa using hz
  have hme (k:Fin m) :
      (∑ j:Fin (m+1), a j / ((k.val+j.val+1:ℕ):K))=b t := by
    have hh : probe A b k.val (Pi.single t (1:K)-polyEval A m a)=0 := probe_zeroSpace ho (k:=k.val) (by omega) ha
    rw [map_sub,sub_eq_zero,probe_polyEval ho (by omega)] at hh
    simpa [probe,Pi.single_apply,h1] using hh.symm
  have eg:=identify_coefficients ho hm hao g0 (b t) hme hg
  rw [eg,map_smul] at ha
  refine ⟨ha,?_⟩
  have hz:=clean1 _ ha
  rw [Pi.sub_apply,Pi.single_eq_same,sub_eq_zero,Pi.smul_apply,smul_eq_mul,
    polyEval_node,h1] at hz
  simpa using hz.symm

/-- Every clean nonterminal row of the *original* tableau lies on the
identified grid. The identity at the terminal already ensures a nonzero
weight, including over a nonordered field. -/
theorem clean_grid (t:Fin s) {g : Fin (m+1)→K}
    (hg : Pi.single t (1:K)-(b t) • polyEval A m g∈zeroSpace A m)
    (hw : b t*(∑ j:Fin (m+1),g j)=1) {i:Fin s} (hit:i≠t)
    (hc : ∀f∈zeroSpace A m, f i=0) :
    (∑ j:Fin (m+1), g j*(nodes A i)^j.val)=0 := by
  have hx:=hc _ hg
  rw [Pi.sub_apply,Pi.single_eq_of_ne hit,zero_sub,neg_eq_zero,
    Pi.smul_apply,smul_eq_mul,polyEval_node] at hx
  exact (mul_eq_zero.mp hx).resolve_left (left_ne_zero_of_mul_eq_one hw)

end
end RKCert.Paired.Terminal
