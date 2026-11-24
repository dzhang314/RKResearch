module

public import RKCert.ReviewedNative.ERK17ScalarPorts
import RKCert.ReviewedNative.JacobiMomentBand
import RKCert.ERKOddPencilArithmetic
import RKCert.ERK17Norm.Pair

@[expose] public section

/-! # Exact exclusion of the two polynomial ports

Private backend imports contain old geometry, but the proof uses only fixed
polynomial results, not a conversion of rooted trees, stage data, or order.
All assertions below hold in an arbitrary characteristic-zero field. -/
namespace RKCert.ReviewedNative.ERK17.Scalar

open Polynomial RKCert.Endpoint RKCert.Paired RKCert.FixedPolynomial JacobiMoments
variable {K : Type*} [Field K] [CharZero K] {P N : K[X]} {a u : K}

theorem no_pencil_ports : ¬ PencilPorts P a u := by
  intro B
  apply ERKOddHidden.odd_pencil_impossible_of_pair ERK17.OddPencil7K5E0 P a u
  exact ⟨B.degree, B.clock_ne, B.omits, B.root, B.divides,
    (by simpa only [formalPrimitive_eq_treePrimitive] using B.first),
    (by simpa only [formalPrimitive_eq_treePrimitive] using B.second)⟩

theorem no_mesh_ports : ¬ MeshPorts P N u := by
  intro B
  have pn : P ≠ 0 := by
    intro z
    exact B.omits (by rw [z, eval_zero])
  have cap : (P*N).natDegree ≤ 8 := natDegree_mul_le.trans (add_le_add B.degree B.cofactor_degree)
  obtain ⟨v,w,e⟩ := signedSlope_band (r:=6) cap B.mesh
  change P*N = C v*signedSlope K 9 + C w*signedSlope K 8 at e
  by_cases vn : v = 0
  · rw [vn, map_zero, zero_mul, zero_add] at e
    have wn : w ≠ 0 := by
      intro z
      rw [z, map_zero, zero_mul] at e
      exact (mul_ne_zero pn B.cofactor_ne) e
    have pd : P ∣ signedSlope K 8 := cancel_nonzero_constant_factor wn ⟨N,e.symm⟩
    have fr : (signedSlope K 8).eval u = 0 := by
      have h := congrArg (eval u) e
      simp only [eval_mul,eval_C,B.cofactor_root,mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left wn
    have lob : Terminal.lobatto (K:=K) 8 = X*signedSlope K 8 := by
      unfold Terminal.lobatto signedSlope
      ring
    apply (RKCert.FixedFactor.lobatto8_first_moment
      (by rw [lob]; exact dvd_mul_of_dvd_right pd X) B.degree B.clock_ne
      (by rw [lob,eval_mul,fr,mul_zero]))
    simpa only [formalPrimitive_eq_treePrimitive] using B.first
  · have scale : C v * C (w/v) = C w := by
      rw [←map_mul,mul_comm,div_mul_cancel₀ _ vn]
    have e' : P*N = C v * pencil (w/v) := by
      rw [e]
      change _ = C v * (signedSlope K 9 + C (w/v)*signedSlope K 8)
      rw [mul_add,←mul_assoc,scale]
    have normalized : pencil (w/v) = fieldPencil K 7 (w/v) :=
      ERKOddHidden.oddPencil_is_fieldPencil _
    have deg := congrArg natDegree e'
    rw [natDegree_mul pn B.cofactor_ne, natDegree_C_mul vn, normalized, fieldPencil_degree] at deg
    have df : P.natDegree = 5 := by have := B.degree; have := B.cofactor_degree; omega
    have pd : P ∣ pencil (w/v) := cancel_nonzero_constant_factor vn ⟨N,e'.symm⟩
    have fr : (pencil (w/v)).eval u = 0 := by
      have h := congrArg (eval u) e'
      simp only [eval_mul,eval_C,B.cofactor_root,mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left vn
    exact no_pencil_ports (P:=P) (a:=w/v) (u:=u) ⟨B.toLocalPaid,df,fr,pd⟩

end RKCert.ReviewedNative.ERK17.Scalar
