module

public import RKCert.ERKOrderNineOneOffAmplitudeTools

@[expose] public section

/-! # The dependent-square amplitude branch

The proof aggregates only known scalar features. In place of repeated
three-by-three solves it applies a single row relation to every prefix. -/
namespace RKCert.Paired.OneOff
open Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Fin s → Fin s → K}

private theorem caseI_first_on {a v nu : K} {i : Fin s} (ha : StrictLower A)
    (hsep : Separated A 4) (O : Origin A a i) (D : CaseI A a v nu) : nu=1/2 := by
  let S : Set (Fin s) := {j | g A j=0 ∧ nodes A j≠0}
  have ex : S.Nonempty := by
    by_contra hn
    apply clocks_not_covered_by_four hsep ({0,a}:Finset K)
      ((Finset.card_insert_le ..).trans (by simp))
    intro j
    by_cases gj : g A j=0
    · have nj : nodes A j=0 := by by_contra e; exact hn ⟨j,gj,e⟩
      simp [nj]
    · simp [O.off_support j gj]
  obtain ⟨j,hj,hmin⟩ := wellFounded_lt.has_min S ex
  obtain ⟨gz,nz⟩ := show g A j=0 ∧ nodes A j≠0 from hj
  have cpre (l : Fin s) (hl : l < j) : nodes A l=0 ∨ nodes A l=a := by
    by_cases gl : g A l=0
    · left
      by_contra cl
      exact hmin l ⟨gl,cl⟩ hl
    · exact Or.inr (O.off_support l gl)
  have hz := D.on_zero j gz
  have e1 : mat A (nodes A) j=(nodes A j)^2/2 := by
    have e := g_apply A j
    rwa [gz,eq_comm,sub_eq_zero] at e
  have p2 := congrFun D.q2 j
  rw [mDef_apply,clock_power_action ha 1 cpre,e1] at p2
  simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,gz,hz,mul_zero,
    add_zero,Nat.reduceAdd,Nat.cast_ofNat,pow_one] at p2
  have y : nodes A j=3*a/2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 nz)
    linear_combination -3*p2
  have hlin (l : Fin s) (hl : l < j) :
      h A l=(-a/2)*g A l-(a^2/4)*nodes A l := by
    by_cases gl : g A l=0
    · have e : nodes A l=0 := by by_contra cl; exact hmin l ⟨gl,cl⟩ hl
      simp [gl,e,D.on_zero l gl]
    · have e := g_apply A l
      have ef : mat A (nodes A) l=(nodes A l)^2/2+g A l := by linear_combination -e
      have ec (k : Fin s) (hk : k < l) : nodes A k=0 ∨ nodes A k=a :=
        cpre k (hk.trans hl)
      have eq := congrFun D.q2 l
      rw [mDef_apply,clock_power_action ha 1 ec,ef,O.off_support l gl] at eq
      rw [O.off_support l gl]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat,
        pow_one] at eq
      linear_combination (3/2:K)*eq
  have we := causal_action_eq ha j (h A)
    ((-a/2) • g A-(a^2/4) • nodes A) (fun l hl => by
      simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using hlin l hl)
  have kj : k A j= -(9*a^4)/32 := by
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hz,e1,y,mul_zero] at we
    linear_combination we
  have q := congrFun D.q3 j
  rw [mDef_apply,clock_power_action ha 2 cpre,e1,y] at q
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,gz,hz,kj,mul_zero,zero_add,
    Nat.reduceAdd,Nat.cast_ofNat] at q
  apply mul_right_cancel₀ (div_ne_zero (neg_ne_zero.mpr
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 O.a_ne))) (by norm_num) : -(9*a^4)/32≠0)
  linear_combination -q

private def confinedFeature (A : Fin s → Fin s → K) (a v : K) (i : Fin s) : Prop :=
  ((nodes A i=0 ∨ nodes A i=3*a/2) ∧ g A i=0 ∧ h A i=0) ∨
  (nodes A i=a ∧ (g A i= -a^2/2 ∨ g A i=v) ∧ h A i=(-a/2)*(g A i+a^2/2))

private theorem caseI_confined {a v : K} {i : Fin s} (ha : StrictLower A)
    (O : Origin A a i) (D : CaseI A a v (1/2)) :
    ∀ j, confinedFeature A a v j := by
  intro j
  refine wellFounded_lt.induction (C:=confinedFeature A a v) j ?_
  intro j ih
  let L := (nodes A)^3-(9*a/4) • (nodes A)^2+(9*a^2/8) • nodes A
    -(a/4) • g A-(1/2:K) • h A
  have localZero (l : Fin s) (hl : l < j) : L l=0 := by
    rcases ih l hl with ⟨h0|hy,g0,h0'⟩|⟨ha',_,h1⟩
    · simp [L,h0,g0,h0']
    · simp only [L,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul,hy,g0,h0']
      ring
    · simp only [L,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul,ha',h1]
      ring
  have e := causal_mat ha j L localZero
  have e1 : mat A (nodes A) j=(nodes A j)^2/2+g A j := by
    linear_combination -(g_apply A j)
  have e2 : mat A ((nodes A)^2) j=(nodes A j)^3/3+(2*a/3)*g A j-(2/3:K)*h A j := by
    have r := congrFun D.q2 j
    simp only [mDef_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at r
    linear_combination r
  have e3 : mat A ((nodes A)^3) j=(nodes A j)^4/4+(a^2/2)*g A j-a*h A j+(1/2:K)*k A j := by
    have r := congrFun D.q3 j
    simp only [mDef_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at r
    linear_combination r
  simp only [L,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    e1,e2,e3] at e
  change confinedFeature A a v j
  have compat : 2*a^2*g A j+4*a*h A j+(nodes A j)^2*(2*nodes A j-3*a)^2=0 := by
    linear_combination 16*e
  by_cases Gj : g A j=0
  · left
    have Hj := D.on_zero j Gj
    rw [Gj,Hj,mul_zero,mul_zero,zero_add,zero_add] at compat
    have opt : nodes A j=0 ∨ nodes A j=3*a/2 := by
      by_cases x : nodes A j=0
      · exact Or.inl x
      · have y := (mul_eq_zero.mp compat).resolve_left (pow_ne_zero 2 x)
        have dy : 2*nodes A j-3*a=0 := by by_contra e; exact pow_ne_zero 2 e y
        exact Or.inr (by linear_combination (1/2:K)*dy)
    exact ⟨opt,Gj,Hj⟩
  · right
    have cj := O.off_support j Gj
    rw [cj] at compat
    have Hj : h A j=(-a/2)*(g A j+a^2/2) := by
      apply mul_left_cancel₀ (mul_ne_zero (by norm_num) O.a_ne : (4:K)*a≠0)
      linear_combination compat
    have relation := D.law j
    rw [Hj] at relation
    have prod : a*((g A j+a^2/2)*(g A j-v))=0 := by linear_combination relation
    obtain r|r := mul_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left O.a_ne)
    · exact ⟨cj,Or.inl (by linear_combination r),Hj⟩
    · exact ⟨cj,Or.inr (sub_eq_zero.mp r),Hj⟩

/-- The complete dependent-square case, with hypotheses supplied by the
actual p8 and p9 rank charts. The independent-square cases are separate. -/
theorem constant_amplitude_of_dependent_square (ha : StrictLower A) (hsep : Separated A 4)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3)
    {a lam : K} {i j : Fin s} (O : Origin A a i)
    (e3 : zeroSpace A 3=twoSpan (g A) (h A))
    (qform : mDef A 2=(2*a/3) • g A+lam • h A) (F : FirstH A a lam j)
    (sq3 : (g A)^2∈zeroSpace A 3) :
    (g A)^2=(-a^2/2) • g A := by
  by_contra nc
  obtain ⟨v,nu,D⟩ := caseI_of_nonconstant ha hsep rank3 rank4 O e3 qform F sq3 nc
  have nu' := caseI_first_on ha hsep O D
  subst nu
  have closed := caseI_confined ha O D
  apply clocks_not_covered_by_four hsep ({0,a,3*a/2}:Finset K)
  · exact (Finset.card_insert_le ..).trans
      (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp)))
  · intro j
    rcases closed j with ⟨x|x,_,_⟩|⟨x,_,_⟩ <;> simp [x]

end RKCert.Paired.OneOff
