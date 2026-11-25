module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorDensityPencil
public import Mathlib.Algebra.BigOperators.Group.List.Basic

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Transport for the two published integer determinant templates

This file copies only the sparse terms of the two allowed determinant
templates. Equality everywhere follows from equality on the product
grid of 49 or 64 integer points and the separate degree bounds.
It neither reads nor regenerates any 1212-row root cage.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.PolynomialCertificate
open scoped Polynomial BigOperators

structure SparseDetTemplate (N : ℕ) where
  terms : List (ℕ × ℕ × ℤ)
  bounded : ∀ a ∈ terms, a.1 ≤ N ∧ a.2.1 ≤ N

private def terms6 : List (ℕ × ℕ × ℤ) :=
  [(6,6,26693301149852480),
   (6,5,-74741243219586944),
   (6,4,80079903449557440),
   (6,3,-41066617153619200),
   (6,2,10266654288404800),
   (6,1,-1119998649644160),
   (6,0,37333288321472),
   (5,6,560559324146902080),
   (5,5,-1606936729221119296),
   (5,4,1761757875890263680),
   (5,3,-923998885956432000),
   (5,2,236133048633310400),
   (5,1,-26319968266637760),
   (5,0,895998919715328),
   (4,6,2802796620734510400),
   (4,5,-8221536754154563840),
   (4,4,9235882197848958080),
   (4,3,-4969060675587923200),
   (4,2,1303865094627409600),
   (4,1,-149333153285888000),
   (4,0,5226660365006080),
   (3,6,4671327701224184000),
   (3,5,-14013983103672552000),
   (3,4,16149447195660750400),
   (3,3,-8942255885200580800),
   (3,2,2422930412063532800),
   (3,1,-287466320075334400),
   (3,0,10453320730012160),
   (2,6,2802796620734510400),
   (2,5,-8595242970252498560),
   (2,4,10170147738093794880),
   (2,3,-5815032988952478720),
   (2,2,1638558024429406080),
   (2,1,-203839754235237120),
   (2,0,7839990547509120),
   (1,6,560559324146902080),
   (1,5,-1756419215660293184),
   (1,4,2135464091988198400),
   (1,3,-1264851808331471360),
   (1,2,373706216097934720),
   (1,1,-49653273467557760),
   (1,0,2090664146002432),
   (0,6,26693301149852480),
   (0,5,-85418563679527936),
   (0,4,106773204599409920),
   (0,3,-65706587445790720),
   (0,2,20533308576809600),
   (0,1,-2986663065717760),
   (0,0,149333153285888)]

def publishedTemplate6 : SparseDetTemplate 6 where
  terms := terms6
  bounded := by
    have h : terms6.all (fun a => decide (a.1 ≤ 6 ∧ a.2.1 ≤ 6)) = true := by
      decide +kernel
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)

private def terms7 : List (ℕ × ℕ × ℤ) :=
  [(7,7,-634665901465024),
   (7,6,2090664146002432),
   (7,5,-2743996691628192),
   (7,4,1829331127752128),
   (7,3,-653332545625760),
   (7,2,120615239192448),
   (7,1,-10051269932704),
   (7,0,261071946304),
   (6,7,-17770645241020672),
   (6,6,59583928161069312),
   (6,5,-79575904057217568),
   (6,4,53965268268687776),
   (6,3,-19599976368772800),
   (6,2,3678764795369664),
   (6,1,-311589367913824),
   (6,0,8223766308576),
   (5,7,-124394516687144704),
   (5,6,424404821638493696),
   (5,5,-577153970805796384),
   (5,4,398794185849963904),
   (5,3,-147653155311421760),
   (5,2,28264171050763648),
   (5,1,-2442458593647072),
   (5,0,65790130468608),
   (4,7,-310986291717861760),
   (4,6,1079305365373755520),
   (4,5,-1495478196937364640),
   (4,4,1054609395149101792),
   (4,3,-399186185377339360),
   (4,2,78249136426100640),
   (4,1,-6935376253565760),
   (4,0,191887880533440),
   (3,7,-310986291717861760),
   (3,6,1097598676651276800),
   (3,5,-1550358130769928480),
   (3,4,1117721319056550208),
   (3,3,-433943476804629792),
   (3,2,87566663653717248),
   (3,1,-8020913406297792),
   (3,0,230265456640128),
   (2,7,-124394516687144704),
   (2,6,446356795171519232),
   (2,5,-643009891404872992),
   (2,4,474711427651677216),
   (2,3,-189727771249720704),
   (2,2,39682413694315392),
   (2,1,-3799380034562112),
   (2,0,115132728320064),
   (1,7,-17770645241020672),
   (1,6,64810588526075392),
   (1,5,-95255885152235808),
   (1,4,72127913037083904),
   (1,3,-29791964080534656),
   (1,2,6513222916392192),
   (1,1,-663383815558464),
   (1,0,21930043489536),
   (0,7,-634665901465024),
   (0,6,2351997164252736),
   (0,5,-3527995746379104),
   (0,4,2743996691628192),
   (0,3,-1175998582126368),
   (0,2,271384288183008),
   (0,1,-30153809798112),
   (0,0,1174823758368)]

def publishedTemplate7 : SparseDetTemplate 7 where
  terms := terms7
  bounded := by
    have h : terms7.all (fun a => decide (a.1 ≤ 7 ∧ a.2.1 ≤ 7)) = true := by
      decide +kernel
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)

section
variable {K : Type*} [Field K]

def SparseDetTemplate.value {N : ℕ} (T : SparseDetTemplate N) (s x : K) : K :=
  (T.terms.map fun a => (a.2.2 : K)*s^a.1*x^a.2.1).sum

noncomputable def SparseDetTemplate.densitySlice {N : ℕ} (T : SparseDetTemplate N) (x : K) : K[X] :=
  (T.terms.map fun a => C ((a.2.2:K)*x^a.2.1)*X^a.1).sum

noncomputable def SparseDetTemplate.trialSlice {N : ℕ} (T : SparseDetTemplate N) (s : K) : K[X] :=
  (T.terms.map fun a => C ((a.2.2:K)*s^a.1)*X^a.2.1).sum

private theorem sum_degrees {N : ℕ} {L : List K[X]} (bound : ∀ P ∈ L, P.natDegree ≤ N) :
    L.sum.natDegree ≤ N := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    rw [List.sum_cons]
    exact natDegree_add_le_of_le (bound p (by simp))
      (ih (fun q hq => bound q (List.mem_cons_of_mem _ hq)))

theorem SparseDetTemplate.densitySlice_degree {N : ℕ} (T : SparseDetTemplate N) (x : K) :
    (T.densitySlice x).natDegree ≤ N := by
  apply sum_degrees
  intro P hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; exact (T.bounded a ha).1)

theorem SparseDetTemplate.trialSlice_degree {N : ℕ} (T : SparseDetTemplate N) (s : K) :
    (T.trialSlice s).natDegree ≤ N := by
  apply sum_degrees
  intro P hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; exact (T.bounded a ha).2)

theorem SparseDetTemplate.densitySlice_eval {N : ℕ} (T : SparseDetTemplate N) (s x : K) :
    (T.densitySlice x).eval s = T.value s x := by
  unfold SparseDetTemplate.densitySlice SparseDetTemplate.value
  change (Polynomial.evalRingHom s) ((T.terms.map _).sum) = _
  rw [map_list_sum,List.map_map]
  apply congrArg List.sum
  apply congrArg (fun f : ℕ × ℕ × ℤ → K => T.terms.map f)
  funext a
  simp only [Polynomial.coe_evalRingHom,Function.comp_apply,eval_mul,eval_C,eval_pow,eval_X]
  ring

theorem SparseDetTemplate.trialSlice_eval {N : ℕ} (T : SparseDetTemplate N) (s x : K) :
    (T.trialSlice s).eval x = T.value s x := by
  unfold SparseDetTemplate.trialSlice SparseDetTemplate.value
  change (Polynomial.evalRingHom x) ((T.terms.map _).sum) = _
  rw [map_list_sum,List.map_map]
  apply congrArg List.sum
  apply congrArg (fun f : ℕ × ℕ × ℤ → K => T.terms.map f)
  funext a
  simp only [Polynomial.coe_evalRingHom,Function.comp_apply,eval_mul,eval_C,eval_pow,eval_X]

end

/-- The independent, genuinely finite identity check for one template. -/
def SparseDetGrid (N : ℕ) (T : SparseDetTemplate N) : Prop :=
  ∀ i j : Fin (N+1), T.value (i.val : ℚ) (j.val : ℚ) = determinantAt N (i.val : ℚ) (j.val : ℚ)

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem poly_eq_grid {N : ℕ} {P Q : K[X]} (p : P.natDegree ≤ N) (q : Q.natDegree ≤ N)
    (g : ∀ i : Fin (N+1), P.eval (i.val : K) = Q.eval (i.val : K)) : P = Q := by
  let G : Finset (Fin (N+1)) := Finset.univ
  let f (i : Fin (N+1)) := (i.val : K)
  have fi : Function.Injective f := fun a b eq => Fin.ext (Nat.cast_injective eq)
  have size : (P-Q).natDegree < G.card := by
    have h := natDegree_sub_le_of_le p q
    simpa only [G,Finset.card_univ,Fintype.card_fin] using (Nat.lt_succ_of_le h)
  have deg : (P-Q).degree < (G.card : WithBot ℕ) :=
    (P-Q).degree_le_natDegree.trans_lt (by exact_mod_cast size)
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero G fi.injOn deg
  intro i _
  rw [eval_sub,g i,sub_self]

theorem SparseDetTemplate.uniform_rat {N : ℕ} (T : SparseDetTemplate N)
    (accepted : SparseDetGrid N T) (s x : ℚ) :
    T.value s x = determinantAt N s x := by
  have line (i : Fin (N+1)) : T.trialSlice (i.val : ℚ) = trialDeterminant N (i.val : ℚ) := by
    apply poly_eq_grid (T.trialSlice_degree _) (trialDeterminant_degree _ _)
    intro j
    rw [T.trialSlice_eval,trialDeterminant_eval]
    exact accepted i j
  have all : T.densitySlice x = densityDeterminant N x := by
    apply poly_eq_grid (T.densitySlice_degree _) (densityDeterminant_degree _ _)
    intro i
    rw [T.densitySlice_eval,densityDeterminant_eval,← T.trialSlice_eval, line i,trialDeterminant_eval]
  rw [← T.densitySlice_eval,all,densityDeterminant_eval]

theorem SparseDetTemplate.densitySlice_eq_rat {N : ℕ} (T : SparseDetTemplate N)
    (accepted : SparseDetGrid N T) (x : ℚ) : T.densitySlice x = densityDeterminant N x := by
  apply Polynomial.funext
  intro s
  rw [T.densitySlice_eval,densityDeterminant_eval]
  exact T.uniform_rat accepted s x

end
end RKCert.ReviewedNative.ThreeInteriorPencil
