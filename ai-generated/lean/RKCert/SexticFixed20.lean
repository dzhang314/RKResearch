module
public import RKCert.SexticGridTable
public import RKCert.SexticResidueBridge
public import RKCert.SexticNative
@[expose] public section
namespace RKCert.Sextic
open Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]

/-- The normalized fixed-grid Hankel determinant is nonzero in every
characteristic-zero field, even if the sixth original knot is zero. -/
theorem lobatto10_minor (v:Fin 6→K) (roots:∀i,((X-1)*lobatto 10).eval (v i)=0)
    (inj:Function.Injective v) : tuple v≠0 := grid_tuple_of_check table_checked v roots inj

/-- An arbitrary sextic vanishing on five of the eleven fixed Lobatto
knots and with two zero primitives at a sixth distinct nonzero knot
vanishes identically. This is a scalar gate, not a tableau floor. -/
theorem lobatto10_five_omitted (a:Fin 5→K) (u:K) (Q:K[X])
    (ai:Function.Injective a) (ga:∀i,((X-1)*lobatto 10).eval (a i)=0)
    (gu:((X-1)*lobatto 10).eval u=0) (fresh:∀i,u≠a i) (nu:u≠0)
    (dQ:Q.natDegree≤6) (qa:∀i,Q.eval (a i)=0)
    (j₁:(primitive (X*Q)).eval u=0) (j₂:(primitive (X^2*Q)).eval u=0) : Q=0 := by
  let v:Fin 6→K:=Fin.snoc a u
  have inj:Function.Injective v:=Fin.snoc_injective_of_injective ai (by
    rintro ⟨i,e⟩;exact fresh i e.symm)
  have rr (i:Fin 6):((X-1)*lobatto 10).eval (v i)=0:=
    Fin.lastCases (by simpa only [v,Fin.snoc_last] using gu)
      (fun j=>by simpa only [v,Fin.snoc_castSucc] using ga j) i
  exact native_of_nonsingular v inj (by simpa only [v,Fin.snoc_last] using nu)
    Q dQ (fun i=>by simpa only [v,Fin.snoc_castSucc] using qa i)
    (by simpa only [v,Fin.snoc_last] using j₁) (by simpa only [v,Fin.snoc_last] using j₂)
    (lobatto10_minor v rr inj)

end RKCert.Sextic
