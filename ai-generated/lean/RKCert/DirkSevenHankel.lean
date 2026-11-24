module
public import RKCert.PortMomentMatrix
public import RKCert.RootTupleSpecialization
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
@[expose] public section
namespace RKCert.SevenPort
open Polynomial Matrix RKCert.PortRank RKCert.FixedFactor
noncomputable section
variable {R S:Type*} [CommRing R] [CommRing S]
/-- Coefficients of (x-1)(15x-t) times the integer normalized
exceptional quartic. Here t=15a and a is the dimensionless pivot ratio. -/
def ec (t:R) (i:Fin 7):R:=match i.val with
  | 0=>6*t*(4*t-25)
  | 1=> -6*(34*t^2-90*t-375)
  | 2=>30*(18*t^2+77*t-450)
  | 3=> -15*(38*t^2+715*t-750)
  | 4=>15*(14*t^2+885*t+2625)
  | 5=> -2625*(2*t+27)
  | _=>31500

theorem map_ec (φ:R→+*S) (t:R)(i:Fin 7):φ (ec t i)=ec (φ t) i:=by
  fin_cases i <;> simp [ec,map_ofNat]

def entry (t u:R) (n:ℕ):R:=
  ∑i:Fin 7,(12252240/(n+i.val+2):ℕ)*ec t i*u^(6-i.val)

def matrix (t u:R) (k:ℕ):Matrix (Fin 5) (Fin 5) R:=
  fun i j=>entry t u (k+i.val+j.val)

def d5 (t u:R) (k:ℕ):R:=(matrix t u k).det

theorem map_entry (φ:R→+*S) (t u:R)(n:ℕ):φ (entry t u n)=entry (φ t) (φ u) n:=by
  simp [entry,map_ec]

theorem map_d5 (φ:R→+*S) (t u:R)(k:ℕ):φ (d5 t u k)=d5 (φ t) (φ u) k:=by
  rw [d5,φ.map_det,d5];congr 1;ext i j;exact map_entry φ t u _

def minPoly (t:R)(k:ℕ):R[X]:=d5 (C t) X k

theorem eval_minor (t u:R)(k:ℕ):(minPoly t k).eval u=d5 t u k:=by
  have h:=map_d5 (evalRingHom u) (C t) X k
  simpa only [minPoly,coe_evalRingHom,eval_C,eval_X] using h

theorem map_minPoly (φ:R→+*S) (t:R)(k:ℕ):(minPoly t k).map φ=minPoly (φ t) k:=by
  have h:=map_d5 (mapRingHom φ) (C t) X k
  simpa [minPoly] using h

theorem degree_minor (t:R)(k:ℕ):(minPoly t k).natDegree≤30:=by
  classical
  have coeffs (i:Fin 7):ec (C t) i=C (ec t i):=(map_ec C t i).symm
  have each(i j:Fin 5):((matrix (C t) (X:R[X]) k) i j).natDegree≤6:=by
    apply natDegree_sum_le_of_forall_le
    intro v _
    rw [coeffs,←Polynomial.C_eq_natCast,←C_mul]
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  rw [minPoly,d5,Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le;intro σ _
  have z:(↑↑(Equiv.Perm.sign σ):R[X]).natDegree=0:=by
    rw [←Polynomial.C_eq_intCast,natDegree_C]
  apply natDegree_mul_le.trans
  rw [z,zero_add]
  have deg:=natDegree_prod_le (s:=Finset.univ) (f:=fun i=>(matrix (C t) X k) (σ i) i)
  exact deg.trans ((Finset.sum_le_sum fun i _=>each _ _).trans (by simp))

def res (t:R):R:=resultant (minPoly t 0) (minPoly t 1) 30 30

theorem map_res (φ:R→+*S)(t:R):φ (res t)=res (φ t):=by
  rw [res,←resultant_map_map,map_minPoly,map_minPoly];rfl

def witness : MvPolynomial (Fin 1) ℤ:=res (MvPolynomial.X 0)

theorem eval_witness {V:Type*} [CommRing V] (v:Fin 1→V):zEval witness v=res (v 0):=by
  let φ:=MvPolynomial.eval₂Hom (Int.castRingHom V) v
  change φ (res (MvPolynomial.X 0))=_
  rw [map_res];simp [φ]

theorem padded_resultant_zero {K:Type*} [Field K] (f g:K[X]) (x:K)
    (df:f.natDegree≤30) (dg:g.natDegree≤30) (fz:f.eval x=0) (gz:g.eval x=0):
    resultant f g 30 30=0:=by
  by_cases both:f=0 ∧ g=0
  · obtain ⟨rfl,rfl⟩:=both
    exact resultant_eq_zero_of_lt_lt _ _ _ _ (by simp) (by simp)
  have one:f≠0 ∨ g≠0:=by tauto
  have dead:¬IsCoprime f g:=by
    rintro ⟨a,b,eqn⟩
    have h:=congrArg (eval x) eqn
    simp [fz,gz] at h
  have exactZ:=resultant_eq_zero_iff.mpr ⟨one,dead⟩
  calc
    _=resultant f g (f.natDegree+(30-f.natDegree)) (g.natDegree+(30-g.natDegree)):=by rw [Nat.add_sub_of_le df,Nat.add_sub_of_le dg]
    _=0:=by rw [resultant_add_left_deg _ _ _ _ _ le_rfl,resultant_add_right_deg _ _ _ _ _ le_rfl,exactZ,mul_zero,mul_zero]

end
end RKCert.SevenPort
