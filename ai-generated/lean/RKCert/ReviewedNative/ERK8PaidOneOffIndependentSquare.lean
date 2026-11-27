module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffAmplitudeTools
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Common start of the two independent-square cases -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof

open Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

noncomputable def correctedSquare (A : Matrix (Fin s) (Fin s) K) (a : K) (j : Fin s) : Fin s → K :=
  let Z := (g A)^2-(-a^2/2) • g A
  Z+(-Z j/h A j) • h A

theorem corrected_square_values {a lam : K} {j : Fin s} (F : FirstH A a lam j) :
    (g A j=0 → correctedSquare A a j=(g A)^2-(-a^2/2) • g A) ∧
    (g A j≠0 → correctedSquare A a j=(g A)^2-(-a^2/2) • g A+
      (2*g A j/a) • h A) := by
  constructor
  · intro gj
    simp [correctedSquare,gj]
  · intro gj
    rcases F.alternative with e|⟨_,vc,_,hj,_⟩
    · exact (gj e.1).elim
    have a_ne : a≠0 := by
      intro eq
      apply F.nonzero
      simp [hj,eq]
    let w := (g A)^2-(-a^2/2) • g A
    have eq : (-w j/h A j)=(2*g A j/a) := by
      apply (div_eq_iff F.nonzero).mpr
      rw [hj]
      simp only [w,Pi.pow_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,a_ne]
      eight_ring K
    change w+(-w j/h A j) • h A=w+(2*g A j/a) • h A
    rw [eq]

theorem vanish_at_two_implies_extra {a lam : K} {i j : Fin s} (ha : ∀ i j, i ≤ j → A i j = 0)
    (O : Origin A a i) (F : FirstH A a lam j)
    (e3 : zeroSpace A 3=Submodule.span K {g A, h A}) {v x : Fin s → K}
    (e4 : zeroSpace A 4=zeroSpace A 3⊔Submodule.span K {v})
    (vi : v i=0) (vj : v j=0) (xm : x∈zeroSpace A 4) (xi : x i=0) (xj : x j=0) :
    ∃ c : K, x=c • v := by
  obtain ⟨a',b',c,ex⟩ := rank_three_rep e3 e4 xm
  have ei := congrFun ex i
  simp only [xi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,O.h_first ha,vi,
    mul_zero,add_zero] at ei
  have a0 : a'=0 := (mul_eq_zero.mp ei.symm).resolve_right O.g_ne
  have ej := congrFun ex j
  simp only [xj,Pi.add_apply,Pi.smul_apply,smul_eq_mul,a0,vj,
    zero_mul,mul_zero,zero_add,add_zero] at ej
  have b0 : b'=0 := (mul_eq_zero.mp ej.symm).resolve_right F.nonzero
  exact ⟨c,by simpa [a0,b0] using ex⟩

/-- Exact rank-three normal form before the independent-square branches
calibrate their first new features. It keeps every chronological row. -/
structure IndependentShape (A : Matrix (Fin s) (Fin s) K) (a lam : K) (i j : Fin s) : Prop where
  span_four : zeroSpace A 4=zeroSpace A 3⊔Submodule.span K {correctedSquare A a j}
  zin : correctedSquare A a j∈zeroSpace A 4
  zout : correctedSquare A a j∉zeroSpace A 3
  zero_first : correctedSquare A a j i=0
  zero_next : correctedSquare A a j j=0
  relations :
    ∃ eta kap mu nu : K,
      diag (nodes A) (h A)=nodes A j • h A+eta • correctedSquare A a j ∧
      k A=kap • correctedSquare A a j ∧
      mDef A 3=((a^2/2) • g A+mu • h A)+nu • correctedSquare A a j ∧
      (g A j=0 → mu=((nodes A j)^2-2*a^2)/a) ∧
      (g A j≠0 → mu= -a)

theorem independent_square_shape
    (ha : ∀ i j, i ≤ j → A i j = 0) (rank3 : finrank K (zeroSpace A 3)=2)
    (rank4 : finrank K (zeroSpace A 4)=3)
    {a lam : K} {i j : Fin s} (O : Origin A a i) (F : FirstH A a lam j)
    (e3 : zeroSpace A 3=Submodule.span K {g A, h A}) (sq : (g A)^2∉zeroSpace A 3) :
    IndependentShape A a lam i j := by
  let Z := correctedSquare A a j
  have gm : g A∈zeroSpace A 3 := zeroSpace_mono A (by decide) (mDef_mem A 1)
  have hm : h A∈zeroSpace A 3 := mat_zeroSpace_bounded A 2 (mDef_mem A 1)
  have sq4 : (g A)^2∈zeroSpace A 4 := by
    simpa only [g,pow_two] using zeroSpace_mul (mDef_mem A 1) (mDef_mem A 1)
  have zm : Z∈zeroSpace A 4 := by
    unfold Z correctedSquare
    apply Submodule.add_mem
    · exact (zeroSpace A 4).sub_mem sq4 ((zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide) gm))
    · exact (zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide) hm)
  have zout : Z∉zeroSpace A 3 := by
    intro zz
    apply sq
    let w : Fin s → K := (g A)^2-(-a^2/2) • g A
    have e : (g A)^2=Z-(-w j/h A j) • h A+(-a^2/2) • g A := by
      change (g A)^2=(w+(-w j/h A j) • h A)-(-w j/h A j) • h A+(-a^2/2) • g A
      dsimp only [w]
      abel
    rw [e]
    exact (zeroSpace A 3).add_mem ((zeroSpace A 3).sub_mem zz ((zeroSpace A 3).smul_mem _ hm))
      ((zeroSpace A 3).smul_mem _ gm)
  have zi : Z i=0 := by
    simp only [Z,correctedSquare,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,
      smul_eq_mul,O.defect,O.h_first ha,mul_zero,add_zero]
    eight_ring K
  have zj : Z j=0 := by
    let w : Fin s → K := (g A)^2-(-a^2/2) • g A
    change (w+(-w j/h A j) • h A) j=0
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [div_mul_cancel₀ _ F.nonzero,add_neg_cancel]
  have e4 := extra_rank_three_span rank3 rank4 zm zout
  refine ⟨e4,zm,zout,zi,zj,?_⟩
  let Y := diag (nodes A) (h A)-nodes A j • h A
  have ym : Y∈zeroSpace A 4 := (zeroSpace A 4).sub_mem (diag_zeroSpace A 3 hm)
    ((zeroSpace A 4).smul_mem _ (zeroSpace_mono A (by decide) hm))
  have yi : Y i=0 := by
    simp only [Y,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,O.h_first ha,mul_zero,sub_self]
  have yj : Y j=0 := by simp [Y]
  obtain ⟨eta,CY⟩ := vanish_at_two_implies_extra ha O F e3 e4 zi zj ym yi yj
  have ke : k A i=0 := causal_mat ha i _ (fun t ht =>
    causal_mat ha t _ (fun v hv=>O.earlier_defect v (hv.trans ht)))
  have kj : k A j=0 := causal_mat ha j _ F.earlier
  obtain ⟨kap,Ak⟩ := vanish_at_two_implies_extra ha O F e3 e4 zi zj
    (mat_zeroSpace_bounded A 3 hm) ke kj
  obtain ⟨alpha,mu,nu,q⟩ := rank_three_rep e3 e4 (mDef_mem A 3)
  have ae := coefficient_of_first_g ha O zi q
  subst alpha
  have Cn : diag (nodes A) (h A)=nodes A j • h A+eta • Z := by
    change diag (nodes A) (h A)-nodes A j • h A=eta • Z at CY
    rw [sub_eq_iff_eq_add,add_comm] at CY
    exact CY
  have prep (v : Fin s) (hv : v < j) : nodes A v=0 ∨ nodes A v=a := by
    rcases F.prefix_features v hv with z|z
    · exact Or.inl z.1
    · exact Or.inr z.1
  have ac : mat A (nodes A) j=(nodes A j)^2/2+g A j := by
    linear_combination (norm := eight_ring K) -(g_apply A j)
  have eq := congrFun q j
  rw [mDef_apply3,clock_power_action ha 2 prep,ac] at eq
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,zj,mul_zero,add_zero,
    Nat.reduceAdd,Nat.cast_ofNat] at eq
  refine ⟨eta,kap,mu,nu,Cn,Ak,q,?_,?_⟩
  · intro gj
    rcases F.alternative with ⟨_,_,hj,_⟩|e
    · apply mul_right_cancel₀ F.nonzero
      calc
        mu*h A j=a^2*((nodes A j)^2/2)-(nodes A j)^4/4 := by
          simpa [gj] using eq.symm
        _ = (((nodes A j)^2-2*a^2)/a)*h A j := by
          rw [hj]
          field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,O.a_ne]
          eight_ring K
    · exact (e.1 gj).elim
  · intro gj
    rcases F.alternative with e|⟨_,_,cj,hj,_⟩
    · exact (gj e.1).elim
    · rw [cj] at eq
      apply mul_right_cancel₀ F.nonzero
      linear_combination (norm := eight_ring K) -eq + a*hj

end RKResearch.Certified.Graded.OneOff.PaidProof
