module
public import RKCert.ERKOddLocalOrthogonal
public import RKCert.ERKEvenThinTrace

@[expose] public section
/-! # Actual relative traces for a localized linear adjoint seed
All shifts are paid into Ann(E8). We do not equate low contextual spaces
with full annihilators and we do not declare a thin flag at grade nine. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ f:Vec K 26}{r j:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem weighted_X_clock_shift (y v:Vec K 26)(a:ℕ):
    weightedEval y v (X^a)=(fun i=>y i^a*v i):=by
  ext i
  simp only [weightedEval_apply,eval_pow,eval_X]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem ordinary_weight_shift (ho:HasTreeOrderAtLeast A b 17)
    (hf:f∈zeroSpace A j)(a:ℕ)(pay:j+a≤8):
    weightedEval (mirror A) (b*f) (X^a)∈annih (treeSpace A 8):=by
  apply mem_annih.mpr
  intro v hv
  have Z:=zeroSpace_mul_treeSpace ho (by omega:a+1≤17)
      (zeroSpace_mul_treeSpace ho (by decide:8+1≤17) hf hv) (mirror_power_tree (A:=A) (k:=a))
  have e:=probe_zeroSpace ho (k:=0) (by omega:0+(j+8+a)+1≤17) Z
  change probe A b 0 _=0 at e
  have E:row b (f*v*(fun i=>mirror A i^a))=0:=by simpa only [probe,pow_zero,mul_one] using e
  rw [row_apply] at E ⊢
  convert E using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply,Pi.mul_apply,eval_pow,eval_X]
  ring

/-- The true b-weighted defect needs the lower reverse cap only after
subtracting an actual vector of the early invariant reverse band. -/
theorem LocalLinearBand.weight_trace (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17)(hf:f∈zeroSpace A j)(cap:j≤8):
    ∃u∈U,∃P:K[X],(P=0∨P.natDegree+(r+1)≤j)∧b*f=u+weightedEval (mirror A) τ P:=by
  let y:=mirror A
  have low:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have bg:(7-r)+1<(headSites y τ).card:=by
    have h:=B.sites
    change 9-r≤(headSites y τ).card at h
    omega
  have bw:b*f∈annih (treeSpace A 8):=by
    have z:=ordinary_weight_shift ho hf 0 (by omega)
    have e:weightedEval (mirror A) (b*f) (X^(0:ℕ))=b*f:=by ext i; simp
    rwa [e] at z
  obtain ⟨u,hu,Q,_,V⟩:=B.representation bw
  let w:=weightedEval y τ Q
  change b*f=u+w at V
  have w0:w∈annih U:=weightedEval_orthogonal B.clock B.orthogonal Q
  have bu:U≤annih (treeSpace A 8):=
    (B.base_annih ho).trans (annih_antitone_paired (treeSpace_mono A (by omega:8≤16-r)))
  have tests(a:ℕ)(al:a≤8-j):∃P:K[X],P.natDegree≤7-r∧
      weightedEval y τ P=(fun i=>y i^a*w i):=by
    have ou:weightedEval y u (X^a)∈U:=by
      rw [weighted_X_clock_shift]
      simpa only [eval_pow,eval_X] using Clock.poly_preserves B.clock ((X:K[X])^a) u hu
    have ow':weightedEval y w (X^a)∈annih U:=by
      rw [weighted_X_clock_shift]
      simpa only [eval_pow,eval_X] using
        Clock.poly_preserves (diag_annih_invariant B.clock) ((X:K[X])^a) w w0
    have eq:weightedEval y w (X^a)=weightedEval y (b*f) (X^a)-weightedEval y u (X^a):=by
      change b*f=u+w at V
      rw [V]
      ext i
      simp only [weightedEval_apply,Pi.add_apply,Pi.sub_apply]
      ring
    have ww:weightedEval y w (X^a)∈annih (treeSpace A 8):=by
      rw [eq]
      have w1:weightedEval y (b*f) (X^a)∈annih (treeSpace A 8):=ordinary_weight_shift ho hf a (by omega)
      have w2:weightedEval y u (X^a)∈annih (treeSpace A 8):=bu ou
      exact (annih (treeSpace A 8)).sub_mem w1 w2
    obtain ⟨P,pd,ee⟩:=B.representation_orthogonal ow' ww
    exact ⟨P,pd,ee.trans (weighted_X_clock_shift _ _ _)⟩
  obtain ⟨P,pd,pe⟩:=trace_degree_from_shifts (k:=8-j) bg tests
  refine ⟨u,hu,P,?_,?_⟩
  · rcases pd with z|d
    · exact Or.inl z
    · exact Or.inr (by omega)
  · rw [←pe] at V
    exact V

/-- A quadratic-or-higher detector is not used in this scalar extraction:
the degree of the τ trace is charged precisely to its earned grade. -/
theorem LocalLinearBand.head_trace (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17)(hf:f∈zeroSpace A j)(pay:j+r+1≤8):
    ∃Q:K[X],Q.natDegree≤j∧weightedEval (mirror A) τ Q=τ*f:=by
  let y:=mirror A
  have low:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have z:τ*f∈annih U:=B.mul_head_orthogonal ho (by omega) hf
  have bg:(7-r)+1<(headSites y τ).card:=by
    have h:=B.sites
    change 9-r≤(headSites y τ).card at h
    omega
  have tests(a:ℕ)(al:a≤7-r-j):∃Q:K[X],Q.natDegree≤7-r∧
      weightedEval y τ Q=(fun i=>y i^a*(τ*f) i):=by
    let w:=weightedEval y (τ*f) (X^a)
    have ow:w∈annih U:=by
      rw [show w=weightedEval y (τ*f) (X^a) from rfl,weighted_X_clock_shift]
      simpa only [eval_pow,eval_X] using
        Clock.poly_preserves (diag_annih_invariant B.clock) ((X:K[X])^a) (τ*f) z
    have paid:w∈annih (treeSpace A 8):=by
      apply mem_annih.mpr
      intro v hv
      have F:=treeSpace_mul (treeSpace_mul hv (zeroSpace_le_treeSpace A j hf))
        (mirror_power_tree (A:=A) (k:=a))
      have F':v*f*(fun i=>y i^a)∈treeSpace A (15-r):=treeSpace_mono A (by omega) F
      have eq:=mem_annih.mp B.paid _ F'
      rw [row_apply] at eq ⊢
      convert eq using 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [w,weightedEval_apply,Pi.mul_apply,eval_pow,eval_X]
      ring
    obtain ⟨Q,dQ,eQ⟩:=B.representation_orthogonal ow paid
    exact ⟨Q,dQ,eQ.trans (weighted_X_clock_shift _ _ _)⟩
  obtain ⟨Q,dQ,eQ⟩:=trace_degree_from_shifts (k:=7-r-j) bg tests
  refine ⟨Q,?_,eQ⟩
  rcases dQ with z|d
  · simp [z]
  · omega
end
end RKCert.Paired.ReverseHull

