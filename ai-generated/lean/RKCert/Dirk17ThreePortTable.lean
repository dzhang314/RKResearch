module
public import RKCert.Dirk17RadauLift
@[expose] public section
namespace RKCert.RadauEight.EarlyPort
open Polynomial RKCert.FixedFactor

/-- The two remaining ordinary degree-six through nine moment denominators
are cleared uniformly by 2520. Scaling the earlier pivot matches homogeneous
integral basis polynomials in each column. -/
def coeff : Fin 3→Fin 6→ℤ :=
  ![![-4,30,-60,35,0,0],![-3,20,-30,0,14,0],![-12,75,-100,0,0,42]]

def colDegree (j:Fin 3) : ℕ := j.val+3

def basisLead (j:Fin 3) : ℤ := coeff j ⟨colDegree j,by have:=j.isLt;unfold colDegree;omega⟩

def rowDegree (i:Fin 3) : ℕ := if i=0 then 3 else 4

def moment {R:Type*} [CommRing R] (j:Fin 6) (k:ℕ) (z:R) : R :=
  ((2520/(j.val+k+1):ℕ):R)*z^(j.val+k+1)

def remaining {R:Type*} [CommRing R] (u v z:R) (i:Fin 3) (j:Fin 6) : R :=
  if i=0 then moment j 2 v-u*moment j 1 v
  else if i=1 then moment j 3 v-u*moment j 2 v
  else moment j 3 z-(u+v)*moment j 2 z+(u*v)*moment j 1 z

def portMatrix {R:Type*} [CommRing R] (u v z:R) (i k:Fin 3) : R :=
  ∑ j:Fin 6, ((coeff k j:ℤ):R)*u^(colDegree k-j.val)*remaining u v z i j

def det3 {R:Type*} [CommRing R] (M:Fin 3→Fin 3→R) : R :=
  M 0 0*(M 1 1*M 2 2-M 1 2*M 2 1)-
  M 0 1*(M 1 0*M 2 2-M 1 2*M 2 0)+
  M 0 2*(M 1 0*M 2 1-M 1 1*M 2 0)

def test {R:Type*} [CommRing R] (v:Fin 3→R) : R := det3 (portMatrix (v 0) (v 1) (v 2))

noncomputable def universal : MvPolynomial (Fin 3) ℤ := test MvPolynomial.X

theorem map_test {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (v:Fin 3→R):
    f (test v)=test (f ∘ v):=by
  simp [test,det3,portMatrix,remaining,moment]

theorem eval_universal {R:Type*} [CommRing R] (v:Fin 3→R) : zEval universal v=test v:=by
  let f:=MvPolynomial.eval₂Hom (Int.castRingHom R) v
  change f (test MvPolynomial.X)=test v
  rw [map_test];congr 1;funext i;simp [f]

/-- Away from the true zero root the fixed scaled polynomial still has a
complete simple split grid. Omitting zero here avoids any inference that an
arbitrary nonzero characteristic-zero scalar stays nonzero under reduction. -/
noncomputable def scaledNonzero : ℤ[X] := intHorner scaled.tail

theorem factor_scaled : scaledGrid=X*scaledNonzero:=by
  change intHorner (0::scaled.tail)=_
  simp only [intHorner,C_0,zero_add,scaledNonzero]

theorem nonzero_monic : scaledNonzero.Monic:=by
  have m:=scaled_monic
  rw [factor_scaled,Monic,leadingCoeff_mul,leadingCoeff_X,one_mul] at m
  exact m

theorem split_nonzero : scaledNonzero.map (Int.castRingHom (ZMod 293177))=linearProduct id gridp.tail:=by
  have h:=split_scaled
  rw [factor_scaled,Polynomial.map_mul,Polynomial.map_X] at h
  have g:linearProduct (id:ZMod 293177→ZMod 293177) gridp=X*linearProduct id gridp.tail:=by
    change linearProduct id (0::gridp.tail)=_
    simp only [linearProduct,id_eq,C_0,sub_zero]
  rw [g] at h
  exact mul_left_cancel₀ X_ne_zero h

def check (a:ℤ) : Bool :=
  integers.tail.all (fun b=>integers.tail.all (fun c=>
    decide (a=b) || decide (a=c) || decide (b=c) || decide (test (![a,b,c]:Fin 3→ℤ)%293177 ≠0)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
theorem check_all : integers.tail.all check=true:=by decide +kernel

theorem tested_prime (v:Fin 3→ZMod 293177) (inside:∀i,v i∈gridp.tail)
    (apart:∀i j:Fin 3,i≠j→v i≠v j):zEval universal v≠0:=by
  have rep (i:Fin 3):∃z∈integers.tail,(Int.castRingHom (ZMod 293177)) z=v i:=by
    have ee:gridp.tail=integers.tail.map (Int.castRingHom (ZMod 293177)):=by decide +kernel
    have m:=inside i
    rw [ee] at m
    exact List.mem_map.mp m
  choose z hz zd using rep
  have inj (a b:Fin 3) (h:a≠b):z a≠z b:=fun e=>apart a b h (by rw [←zd,←zd,e])
  have t:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp check_all (z 0) (hz 0))
    (z 1) (hz 1)) (z 2) (hz 2)
  have d0:z 0≠z 1:=inj 0 1 (by decide)
  have d1:z 0≠z 2:=inj 0 2 (by decide)
  have d2:z 1≠z 2:=inj 1 2 (by decide)
  simp only [d0,d1,d2,decide_false,Bool.false_or,decide_eq_true_eq] at t
  have vec:(![z 0,z 1,z 2]:Fin 3→ℤ)=z:=by ext i;fin_cases i <;> rfl
  rw [vec] at t
  rw [eval_universal]
  intro fail
  have h:=map_test (Int.castRingHom (ZMod 293177)) z
  rw [show Int.castRingHom (ZMod 293177) ∘ z=v from funext zd,fail] at h
  exact t (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))

variable {K:Type*} [Field K] [CharZero K]

theorem test_at_scaled_roots (u v z:K)
    (un:u≠0) (vn:v≠0) (zn:z≠0) (vu:v≠u) (zu:z≠u) (zv:z≠v)
    (ur:(grid K).eval u=0) (vr:(grid K).eval v=0) (zr:(grid K).eval z=0) :
    test (![24310*u,24310*v,24310*z]:Fin 3→K)≠0:=by
  let a:Fin 3→K:=![u,v,z]
  have an (i:Fin 3):a i≠0:=by fin_cases i <;> assumption
  have ar (i:Fin 3):(grid K).eval (a i)=0:=by fin_cases i <;> assumption
  have ainj:Function.Injective a:=by
    intro i j e
    fin_cases i <;> fin_cases j <;> simp_all [a,ne_comm]
  have nr (i:Fin 3):(scaledNonzero.map (Int.castRingHom K)).eval (24310*a i)=0:=by
    have e:=scale_eqn (a i)
    rw [ar i,mul_zero,factor_scaled,Polynomial.map_mul,Polynomial.map_X,eval_mul,eval_X] at e
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) (an i))
  have testNe:=split_prime_root_tuple 293177 scaledNonzero nonzero_monic gridp.tail split_nonzero
    (fun t ht=>by rw [split_nonzero];exact simple_product_of_nodup gridp.tail (by decide) ht)
    universal (fun i j:Fin 3=>i≠j) tested_prime (fun i=>24310*a i) nr
    (fun i j ij e=>ij (ainj (mul_left_cancel₀ (by norm_num:(24310:K)≠0) e)))
  rw [eval_universal] at testNe
  have e:(fun i=>24310*a i)=(![24310*u,24310*v,24310*z]:Fin 3→K):=by ext i;fin_cases i <;> rfl
  rwa [e] at testNe
end RKCert.RadauEight.EarlyPort
