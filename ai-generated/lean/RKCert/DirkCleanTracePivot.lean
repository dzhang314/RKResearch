module
public import RKCert.DirkShortTrace
public import RKCert.DirkPolynomialMarked
@[expose] public section
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
variable {K : Type*} [Field K] [CharZero K] {s j p q : ℕ}
variable {A : Fin s → Fin s → K} {b θ : Vec K s} {F : K[X]}
noncomputable section
namespace OrdinaryTrace

/-- Polynomial support escape on the original weighted coordinates. If all
moments of FG may be tested, a nonzero trace F cannot be supported,
after multiplication by b, only on roots of a nonzero G. -/
theorem exists_weighted_active_outside_roots (h : OrdinaryTrace A j θ F)
    (ho : HasTreeOrderAtLeast A b p) (hF : F≠0) (G : K[X]) (hG : G≠0)
    (pay : j+G.natDegree+(F*G).natDegree+1≤p) :
    ∃ i, b i≠0 ∧ θ i≠0 ∧ G.eval (nodes A i)≠0 := by
  classical
  by_contra! only
  apply mul_ne_zero hF hG
  apply primitive_shift_detect (F*G) (k:=0) (d:=(F*G).natDegree) le_rfl 1 one_ne_zero
  intro k
  have dk : k.val≤(F*G).natDegree := by have:=k.isLt;omega
  have dn:=natDegree_mul_le (p:=G) (q:=(X^k.val:K[X]))
  rw [natDegree_X_pow] at dn
  have eqn:=h.pair_polynomial ho (G*X^k.val) (by omega)
  have vanish : row (weightedEval (nodes A) b (G*X^k.val)) θ=0 := by
    rw [row_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hb : b i=0
    · simp [weightedEval_apply,hb]
    by_cases hθ : θ i=0
    · simp [hθ]
    simp [weightedEval_apply,only i hb hθ]
  rw [vanish] at eqn
  rw [zero_add,show X^k.val*(F*G)=F*(G*X^k.val) by ring]
  exact eqn.symm

/-- A physically clean first support pivot pays its diagonal and one actual
primitive, independent of any global invertibility of A. -/
theorem primitive_zero_at_first_clean (h : OrdinaryTrace A j θ F)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (jp : j+2≤p) (jq : j+2≤q)
    {i : Fin s} (active : θ i≠0) (before : ∀ k < i, θ k=0)
    (clean : ∀ f∈zeroSpace A q, f i=0) :
    A i i=0 ∧ (Paired.primitive F).eval (nodes A i)=0 := by
  have mem : commutatorR (mat A) (diag (nodes A)) θ ∈ zeroSpace A (j+2) :=
    commutator_mem_zeroSpace ho j jp h.stage
  have hz:=clean _ (zeroSpace_mono A jq mem)
  rw [commutatorR_leading ha before] at hz
  have d : A i i=0 := sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right active))
  have matz : mat A θ i=0 := by simpa only [d,zero_mul] using causalDiag_mat ha i θ before
  have eqn:=clean _ (zeroSpace_mono A (show j+1≤q by omega) h.primitive.pure)
  refine ⟨d,?_⟩
  simpa only [Pi.sub_apply,matz,evalNodes_apply,zero_sub,neg_eq_zero,formalPrimitive_eq_treePrimitive] using eqn

end OrdinaryTrace
end
end RKCert.Paired
