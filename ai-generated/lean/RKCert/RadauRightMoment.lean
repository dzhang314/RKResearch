module

public import RKCert.RadauMomentRecursion
public import RKCert.RadauLeftGram

@[expose] public section

/-! # Fixed right Radau omitted-factor moments over characteristic zero -/
namespace RKCert.FixedPolynomial.Radau77569
open Polynomial RKCert.Paired RKCert.Paired.Signature RKCert.Endpoint
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R]

theorem map_factorMoment {S : Type*} [CommRing S] (φ : R→+*S)
    (u : R) (j : ℕ) (rs : List R) :
    φ (factorMoment u j rs)=factorMoment (φ u) j (rs.map φ) := by
  induction rs generalizing j with
  | nil => simp [factorMoment]
  | cons a rs ih => simp only [factorMoment,map_sub,map_mul,List.map_cons,ih]

theorem factorMoment_perm (u : R) (j : ℕ) {l r : List R} (h : l.Perm r) :
    factorMoment u j l=factorMoment u j r := by
  induction h generalizing j with
  | nil => rfl
  | cons _ _ ih => simp only [factorMoment,ih]
  | swap a b l =>
    simp only [factorMoment]
    ring
  | trans _ _ ih ih' => exact (ih j).trans (ih' j)

theorem factorMoment_scale (L u : R) (j : ℕ) (rs : List R) :
    factorMoment (L*u) j (rs.map (L*·))=L^(j+rs.length+1)*factorMoment u j rs := by
  induction rs generalizing j with
  | nil => simp only [List.map_nil,List.length_nil,Nat.add_zero,factorMoment,mul_pow]; ring
  | cons a rs ih =>
    simp only [List.map_cons,factorMoment,ih,List.length_cons]
    have e : j+1+rs.length+1=j+rs.length+1+1 := by omega
    have d : j+(rs.length+1)+1=j+rs.length+1+1 := by omega
    rw [e,d,pow_succ]
    ring

variable {K : Type*} [Field K] [CharZero K]

noncomputable def listFactor (rs : List K) : K[X] := (rs.map (fun a => X-C a)).prod

theorem factorMoment_agrees (u : K) (j : ℕ) (rs : List K) (hd : j+rs.length≤5) :
    factorMoment u j rs = (420:K)*paidMoment (listFactor rs) u j := by
  induction rs generalizing j with
  | nil =>
    have hj : j≤5 := by simpa only [List.length_nil,Nat.add_zero] using hd
    have hc : ((420/(j+1):ℕ):K)*((j+1:ℕ):K)=420 := by
      interval_cases j <;> norm_num
    have hn : ((j+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
    change ((420/(j+1):ℕ):K)*u^(j+1)=(420:K)*(formalPrimitive (X^j*1)).eval u
    rw [mul_one,←monomial_one_right_eq_X_pow,formalPrimitive_eq_treePrimitive,
      primitive_monomial,eval_monomial]
    field_simp [hn]
    linear_combination u^(j+1)*hc
  | cons a rs ih =>
    simp only [List.length_cons] at hd
    simp only [factorMoment,listFactor,List.map_cons,List.prod_cons]
    rw [ih (j+1) (by omega),ih j (by omega)]
    unfold listFactor
    rw [paidMoment_affine _ _ (natDegree_X_sub_C a).le]
    simp [coeff_X,coeff_C]
    ring

theorem radau_left_zero_ne : (radauLeft7 : K[X]).eval 0≠0 := by
  rw [←coeff_zero_eq_eval_zero]
  change (ofFn 8 (radauLeft7_coeff (K:=K))).coeff 0≠0
  rw [ofFn_coeff_eq_val_of_lt _ (by decide)]
  norm_num [radauLeft7_coeff]

private noncomputable def rightExpr (d : ℕ) : MvPolynomial (Option (Option (Fin d))) ℤ :=
  let L : MvPolynomial (Option (Option (Fin d))) ℤ := -51480
  factorMoment (L-MvPolynomial.X (some none)) 1
    ((List.finRange d).map (fun i => L-MvPolynomial.X (some (some i))))

private theorem rightExpr_eval {S : Type*} [CommRing S] {d : ℕ}
    (a : Option (Option (Fin d))→S) :
    (rightExpr d).eval₂ (Int.castRingHom S) a =
      factorMoment (((-51480:ℤ):S)-a (some none)) 1
        ((List.finRange d).map (fun i => ((-51480:ℤ):S)-a (some (some i)))) := by
  change MvPolynomial.eval₂Hom (Int.castRingHom S) a (rightExpr d)=_
  rw [rightExpr,map_factorMoment]
  simp only [map_sub,map_neg,map_ofNat,MvPolynomial.eval₂Hom_X',List.map_map,Function.comp_def,Int.cast_neg,Int.cast_ofNat]

private theorem scale_right_arg {S : Type*} [CommRing S] (L x : S) :
    L-L*(1-x)=L*x := by ring

/-- A product of up to four distinct right-Radau factors cannot have zero
first paid moment at an omitted right-Radau root. All roots and the pivot
are fixed polynomial data, not contracted RK coefficients. -/
theorem right_omitted_primitive_ne {d : ℕ} (hd : d≤4) (u : K) (a : Fin d→K)
    (inj : Function.Injective a) (omitRoot : ∀ i,a i≠u)
    (hu : (radauLeft7 : K[X]).eval (1-u)=0)
    (ha : ∀ i,(radauLeft7 : K[X]).eval (1-a i)=0) :
    paidMoment (∏ i : Fin d, (X-C (a i))) u 1≠0 := by
  classical
  intro zero
  let left : Option (Fin d)→K := fun x => 1-x.elim u a
  have hroots (i : Option (Fin d)) : (radauLeft7 : K[X]).eval (left i)=0 := by
    cases i with
    | none => exact hu
    | some i => exact ha i
  have ln (i : Option (Fin d)) : left i≠0 := fun e =>
    radau_left_zero_ne (by simpa only [e] using hroots i)
  obtain ⟨Lift⟩ := exists_grid_lift left (fun i => Or.inr (hroots i))
  let S := Lift.specialization
  let idx (i : Option (Fin d)) : Fin 7 := (Lift.index i).pred (Lift.nonorigin _ (ln i))
  have eq (i : Option (Fin d)) : (idx i).succ=Lift.index i := Fin.succ_pred _ _
  have idxInj : Function.Injective idx := by
    intro i j e
    by_contra hne
    apply Lift.distinct i j _ ((eq i).symm.trans ((congrArg Fin.succ e).trans (eq j)))
    intro h
    have h' : i.elim u a=j.elim u a := by dsimp only [left] at h; linear_combination -h
    apply hne
    cases i <;> cases j
    · rfl
    · exact (omitRoot _ h'.symm).elim
    · exact (omitRoot _ h').elim
    · exact congrArg some (inj h')
  have eF : listFactor ((List.finRange d).map a)=∏ i : Fin d, (X-C (a i)) := by
    rw [listFactor,List.map_map,Fin.prod_univ_def]
    rfl
  have mz : factorMoment u 1 ((List.finRange d).map a)=0 := by
    rw [factorMoment_agrees _ _ _ (by simp only [List.length_map,List.length_finRange]; omega),
      eF,zero,mul_zero]
  have source : (rightExpr d).eval₂ (Int.castRingHom K) (scaledInput left)=0 := by
    rw [rightExpr_eval]
    change factorMoment (((-51480:ℤ):K)-((-51480:ℤ):K)*(1-u)) 1
      ((List.finRange d).map (fun i => ((-51480:ℤ):K)-((-51480:ℤ):K)*(1-a i)))=0
    simp only [scale_right_arg]
    have es := factorMoment_scale ((-51480:ℤ):K) u 1 ((List.finRange d).map a)
    rw [mz,mul_zero] at es
    simpa only [List.map_map,Function.comp_def] using es
  have target := S.preserves _ source
  rw [rightExpr_eval] at target
  change factorMoment (((-51480:ℤ):S.carrier)-S.image (some none)) 1
      ((List.finRange d).map (fun i => ((-51480:ℤ):S.carrier)-S.image (some (some i))))=0 at target
  simp only [S,Lift.decoded,←eq] at target
  have equalCast (j : Fin 7) : ((-51480:ℤ):S.carrier)-
        S.embed (scaledRoot j.succ)=S.embed (((-51480:ℤ):F)*rightRoots j) := by
    have g : leftGrid j.succ=leftRoots j := rfl
    simp only [scaledRoot,g,rightRoots,map_mul,map_intCast,map_sub,map_one]
    ring
  change factorMoment (((-51480:ℤ):S.carrier)-S.embed (scaledRoot (idx none).succ)) 1
    ((List.finRange d).map (fun i => ((-51480:ℤ):S.carrier)-S.embed (scaledRoot (idx (some i)).succ)))=0 at target
  simp only [equalCast] at target
  let u' := rightRoots (idx none)
  let rs := (List.finRange d).map (fun i => rightRoots (idx (some i)))
  let L : F := (-51480:ℤ)
  have target' : S.embed (factorMoment (L*u') 1 (rs.map (L*·)))=0 := by
    rw [map_factorMoment]
    simpa only [rs,u',L,List.map_map,Function.comp_def] using target
  have reduced : factorMoment (L*u') 1 (rs.map (L*·))=0 :=
    S.embed.injective (by simpa only [map_zero] using target')
  rw [factorMoment_scale] at reduced
  have actual := (mul_eq_zero.mp reduced).resolve_left (pow_ne_zero _ leading_mod_ne)
  let T : Finset (Fin 7) := Finset.univ.image (fun i : Fin d => idx (some i))
  obtain ⟨m,hm⟩ := mask_covers (fun i => decide (i∈T))
  have notin : idx none∉T := by
    intro h
    obtain ⟨i,_,e⟩ := Finset.mem_image.mp h
    cases idxInj e
  have hm0 : m.val.testBit (idx none).val=false := by simp [hm,notin]
  have perm : (selected m).Perm ((List.finRange d).map (fun i => idx (some i))) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange 7).filter _)
      ((List.nodup_finRange d).map (fun i j e => Option.some.inj (idxInj e)))).mpr
    intro j
    simp only [List.mem_filter,List.mem_finRange,true_and,hm,decide_eq_true_eq]
    simp [T]
  have len : (selected m).length≤4 := by
    rw [perm.length_eq,List.length_map,List.length_finRange]
    exact hd
  have eqM := factorMoment_perm (rightRoots (idx none)) 1 (perm.map rightRoots)
  rw [List.map_map] at eqM
  exact right_omitted_moment_rec _ _ hm0 len (eqM.trans actual)

end
end RKCert.FixedPolynomial.Radau77569
