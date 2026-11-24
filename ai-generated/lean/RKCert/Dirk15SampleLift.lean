module

public import RKCert.Dirk15ReplayInterface
public import RKCert.ERKCompactResidueSound

@[expose] public section

/-! # Kernel lift from exact residue samples to degree-preserving pairs -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.GoodPrimeDense RKCert.CompactResidue
open scoped Classical

local notation "F" => ZMod 1009
noncomputable section

theorem sampleSite_injective {d : ℕ} (small : d<1009) :
    Function.Injective (fun i : Fin (d+1) => (i.val:F)) := by
  intro i j he
  have il : i.val<1009 := i.isLt.trans_le (Nat.succ_le_of_lt small)
  have jl : j.val<1009 := j.isLt.trans_le (Nat.succ_le_of_lt small)
  apply Fin.ext
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt il,Nat.mod_eq_of_lt jl] using congrArg ZMod.val he

theorem poly_eq_on_samples {d : ℕ} {P Q : F[X]} (small : d<1009)
    (pd : P.natDegree≤d) (qd : Q.natDegree≤d)
    (h : ∀ i : Fin (d+1),P.eval (i.val:F)=Q.eval (i.val:F)) : P=Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ (sampleSite_injective small).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    exact (P-Q).degree_le_natDegree.trans_lt (by
      exact_mod_cast Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le pd qd)))
  · intro i _
    rw [eval_sub,h,sub_self]

abbrev residuePoly (c : List ℕ) : F[X] := RKCert.CompactResidue.polynomial F c

theorem coeff_residuePoly (c : List ℕ) (i : ℕ) :
    (residuePoly c).coeff i=((c[i]?.getD 0):F) := by
  simp only [residuePoly,RKCert.CompactResidue.polynomial,decode,coeff_ofCoeffList,
    List.getD_eq_getElem?_getD,List.getElem?_map]
  cases c[i]? <;> simp

theorem residuePoly_degree_le (c : List ℕ) {d : ℕ} (len : c.length≤d+1) :
    (residuePoly c).natDegree≤d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_residuePoly,List.getElem?_eq_none_iff.mpr (by omega)]
  rfl

theorem residuePoly_degree_eq (c : List ℕ) {d : ℕ} (len : c.length≤d+1)
    (lead : ((c[d]?.getD 0:ℕ):F)≠0) : (residuePoly c).natDegree=d :=
  natDegree_eq_of_le_of_coeff_ne_zero (residuePoly_degree_le c len)
    (by rwa [coeff_residuePoly])

end

/-- Horner replay is an ordinary natural computation with modular reductions,
independent of the noncomputable polynomial representation. -/
def sampleHorner (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | c::l => (c+a*sampleHorner a l)%1009

theorem residuePoly_eval_horner (c : List ℕ) (a : ℕ) :
    (residuePoly c).eval (a:F)=(sampleHorner a c:F) := by
  rw [eval_poly]
  induction c with
  | nil => rfl
  | cons c l ih =>
    simp only [GoodPrimeDense.read,sampleHorner,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul]
    rw [←ih]

theorem integer_reduction_of_residue_samples (P : ℤ[X]) (c : List ℕ) {d : ℕ}
    (small : d<1009) (cap : P.natDegree≤d) (len : c.length≤d+1)
    (vals : Fin (d+1)→ℕ)
    (proofs : ∀ i,(P.map order15Reduce).eval (i.val:F)=(vals i:F))
    (kernelCheck : ∀ i,sampleHorner i.val c%1009=vals i%1009) :
    P.map order15Reduce=residuePoly c := by
  apply poly_eq_on_samples small (natDegree_map_le.trans cap) (residuePoly_degree_le c len)
  intro i
  rw [proofs i,residuePoly_eval_horner]
  have v := congrArg (fun n : ℕ => (n:F)) (kernelCheck i)
  simpa only [ZMod.natCast_mod] using v.symm

private theorem residueBezout (P Q a b : List ℕ)
    (cert : plus (naturalPrime 1009) (times (naturalPrime 1009) a P)
      (times (naturalPrime 1009) b Q)=[1]) :
    IsCoprime (residuePoly P) (residuePoly Q) := by
  let s : Sound (naturalPrime 1009) (fun n : ℕ => (n:F)) :=
    Sound.naturalPrime (by decide)
  refine ⟨residuePoly a,residuePoly b,?_⟩
  change decode _ a*decode _ P+decode _ b*decode _ Q=_
  rw [←decode_times s,←decode_times s,←decode_plus s,cert]
  simp [decode,Polynomial.ofCoeffList_cons]

theorem goodPrimePair_of_samples {P Q : ℤ[X]} {d e : ℕ} (p q a b : List ℕ)
    (left : P.map order15Reduce=residuePoly p) (right : Q.map order15Reduce=residuePoly q)
    (pLen : p.length≤d+1) (qLen : q.length≤e+1)
    (pLead : ((p[d]?.getD 0:ℕ):F)≠0)
    (qLead : ((q[e]?.getD 0:ℕ):F)≠0) (positive : d≠0∨e≠0)
    (checked : plus (naturalPrime 1009) (times (naturalPrime 1009) a p)
      (times (naturalPrime 1009) b q)=[1]) :
    Order15GoodPrimePair P Q d e := by
  refine ⟨(congrArg natDegree left).trans (residuePoly_degree_eq p pLen pLead),
    (congrArg natDegree right).trans (residuePoly_degree_eq q qLen qLead),positive,?_⟩
  rw [left,right]
  exact residueBezout p q a b checked

end RKCert.FixedPolynomial
