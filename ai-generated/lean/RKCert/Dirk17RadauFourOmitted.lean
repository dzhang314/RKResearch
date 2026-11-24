module
public import RKCert.Dirk17RadauNative
public import RKCert.Dirk17RadauLift
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired RKCert.Sextic
variable {K:Type*} [Field K] [CharZero K]
theorem radau8_minor (v:Fin 5→K) (roots:∀i,(grid K).eval (v i)=0)
    (inj:Function.Injective v) : tupleFour v≠0 := grid_tupleFour_of_check checked v roots inj

/-- An arbitrary quintic vanishing on four of the nine fixed Radau
knots and with two zero primitives at a fifth distinct nonzero knot
vanishes identically. This is a scalar gate, not a tableau floor. -/
theorem radau8_four_omitted (a:Fin 4→K) (u:K) (Q:K[X])
    (ai:Function.Injective a) (ga:∀i,(grid K).eval (a i)=0)
    (gu:(grid K).eval u=0) (fresh:∀i,u≠a i) (nu:u≠0)
    (dQ:Q.natDegree≤5) (qa:∀i,Q.eval (a i)=0)
    (j₁:(primitive (X*Q)).eval u=0) (j₂:(primitive (X^2*Q)).eval u=0) : Q=0 := by
  let v:Fin 5→K:=Fin.snoc a u
  have inj:Function.Injective v:=Fin.snoc_injective_of_injective ai (by
    rintro ⟨i,e⟩;exact fresh i e.symm)
  have rr (i:Fin 5):(grid K).eval (v i)=0:=
    Fin.lastCases (by simpa only [v,Fin.snoc_last] using gu)
      (fun j=>by simpa only [v,Fin.snoc_castSucc] using ga j) i
  exact native_of_nonsingular v inj (by simpa only [v,Fin.snoc_last] using nu)
    Q dQ (fun i=>by simpa only [v,Fin.snoc_castSucc] using qa i)
    (by simpa only [v,Fin.snoc_last] using j₁) (by simpa only [v,Fin.snoc_last] using j₂)
    (radau8_minor v rr inj)

end RKCert.RadauEight
