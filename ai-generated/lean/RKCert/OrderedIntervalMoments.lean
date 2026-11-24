module
public import RKCert.OrderedMomentGram
public import RKCert.ERKFiniteMarkedMoments

@[expose] public section

/-! # Ordered Gram on actual intervals and actual graded RK moments -/
namespace RKCert.OrderedGram
open RKCert.Paired Polynomial

section Field
variable {K:Type*} [Field K] [CharZero K]

theorem derivative_treePrimitive (P:K[X]) :
    (Paired.primitive P).derivative=P := by
  ext n
  rw [coeff_derivative,primitive_coeff_succ]
  have hn : (((n+1:ℕ):K))≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  simpa only [Nat.cast_succ] using div_mul_cancel₀ (P.coeff n) hn

theorem derivative_moment (P:K[X]) :
    (Paired.primitive P.derivative).eval 1=P.eval 1-P.eval 0 := by
  let Q:=P-C (P.eval 0)
  have h0 : Q.coeff 0=0 := by rw [coeff_zero_eq_eval_zero];simp [Q]
  have hd : Q.derivative=P.derivative := by simp [Q]
  have e:=primitive_derivative Q h0
  rw [hd] at e
  rw [e]
  simp [Q]

/-- Polynomial substitution over a formal oriented interval, without any topology. -/
theorem affine_substitution (P:K[X]) (u v:K) :
    (Paired.primitive P).eval v-(Paired.primitive P).eval u=
      (v-u)*(Paired.primitive (P.comp (C (v-u)*X+C u))).eval 1 := by
  let L : K[X]:=C (v-u)*X+C u
  let F := (Paired.primitive P).comp L
  have hfd : F.derivative=(v-u)•(P.comp L) := by
    rw [show F=(Paired.primitive P).comp L from rfl,derivative_comp,derivative_treePrimitive]
    have hd : L.derivative=C (v-u) := by simp [L]
    rw [hd,C_mul']
  have l0 : L.eval 0=u := by simp [L]
  have l1 : L.eval 1=v := by simp [L]
  have h:=derivative_moment F
  rw [hfd,map_smul,eval_smul,smul_eq_mul] at h
  simpa only [F,eval_comp,l0,l1] using h.symm

omit [CharZero K] in
theorem affine_comp_ne_zero {P:K[X]} (hP:P≠0) (u d:K) (hd:d≠0) :
    P.comp (C d*X+C u)≠0 := by
  have dm : (C d*X:K[X]).natDegree=1 := by
    rw [natDegree_mul (C_ne_zero.mpr hd) X_ne_zero,natDegree_C,natDegree_X,zero_add]
  have de : (C d*X+C u:K[X]).natDegree=1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [dm,natDegree_C];decide),dm]
  apply leadingCoeff_ne_zero.mp
  rw [leadingCoeff_comp (by rw [de];decide)]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
    (pow_ne_zero _ (leadingCoeff_ne_zero.mpr (by intro hz;rw [hz,natDegree_zero] at de;omega)))

end Field

section Ordered
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem interval_square_pos (P:K[X]) (hP:P≠0) {u v:K} (h:u<v) :
    0<(Paired.primitive (P^2)).eval v-(Paired.primitive (P^2)).eval u := by
  have vp:0<v-u := sub_pos.mpr h
  rw [affine_substitution]
  have eq : (P^2).comp (C (v-u)*X+C u)=(P.comp (C (v-u)*X+C u))^2 := by
    simp only [pow_two,mul_comp]
  rw [eq]
  have Qn := affine_comp_ne_zero hP u (v-u) vp.ne'
  have e := pow_square_pos 0 _ Qn
  rw [pow_zero,one_mul] at e
  exact mul_pos vp e

/-- Beyond the symmetric half-order cutoff, a polynomial profile still cannot
be a defect when its anchored square moment is affordable. -/
theorem ordered_anchored_separation {s p j:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (P:K[X])
    (dP:P.natDegree≤j) (pay:j+P.natDegree≤p) (hF:evalNodes A P∈zeroSpace A j) :
    P=0 := by
  by_contra pn
  have n0 : nodes A 0=0 := by unfold nodes;exact Finset.sum_eq_zero fun i _=>ha _ _ (Fin.zero_le i)
  have p0 : P.eval 0=0 := by
    have h : evalNodes A P (0:Fin (s+1))=0 := origin_zeroSpace A ha j hF
    simpa only [evalNodes_apply,n0] using h
  have dp : (X:K[X])∣P := by
    simpa using (dvd_iff_isRoot (a:=(0:K))).mpr p0
  obtain ⟨Q,he⟩:=dp
  have qn : Q≠0 := fun z=>pn (by rw [he,z,mul_zero])
  have eqDegree : P.natDegree=Q.natDegree+1 := by rw [he,natDegree_X_mul qn]
  have ev : evalNodes A (P*Q)=evalNodes A P*evalNodes A Q := by ext i;simp
  have pure : evalNodes A (P*Q)∈zeroSpace A (j+Q.natDegree) := by
    rw [ev]
    exact zeroSpace_mul_treeSpace ho (by omega) hF (evalNodes_mem_treeSpace A Q le_rfl)
  have zero := probe_zeroSpace ho (k:=0) (by omega) pure
  change probe A b 0 (evalNodes A (P*Q))=0 at zero
  have nd := natDegree_mul_le (p:=P) (q:=Q)
  rw [FiniteMidpoint.probe_eval_moment ho (P*Q) 0 (by omega)] at zero
  unfold FiniteMidpoint.scalarMoment at zero
  rw [pow_zero,one_mul,he,mul_assoc,←pow_two] at zero
  have pos := pow_square_pos 1 Q qn
  rw [pow_one] at pos
  exact pos.ne' zero

end Ordered
end RKCert.OrderedGram

