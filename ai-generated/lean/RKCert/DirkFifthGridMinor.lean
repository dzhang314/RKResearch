module
public import RKCert.DirkFifthFastMinorCheck
@[expose] public section
namespace RKCert.PaidFifth
open RKCert.FixedFactor RKCert.DirkQuintic Polynomial RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]
/-- The homogeneous obstruction is already nonzero for every ordered distinct
triple of points of the fixed Lobatto-10 closed grid, even one involving 0.
Only roots of one fixed monic integral polynomial are specialized. -/
theorem grid_minor (w:Fin 3→K) (roots:∀i,((X-1)*lobatto 10).eval (w i)=0) (inj:Function.Injective w):
    minor (w 0) (w 1) (w 2)≠0:=by
  have r(i:Fin 3):(integral10.map (Int.castRingHom K)).eval (16796*w i)=0:=by
    have e:=scale_eqn10 (w i)
    rw [roots i,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have D:=split_prime_root_tuple 15727 integral10 monic_scaled10 grid10 split_scaled10
    (fun z hz=>by rw [split_scaled10];exact simple_product_of_nodup grid10 (by decide) hz)
    test (fun i j:Fin 3=>i≠j) mod_minor (fun i=>16796*w i) r
    (fun i j ij e=>ij (inj (mul_left_cancel₀ (by norm_num : (16796:K)≠0) e)))
  rw [eval_test,homogeneous] at D
  exact (mul_ne_zero_iff.mp D).2
end RKCert.PaidFifth

