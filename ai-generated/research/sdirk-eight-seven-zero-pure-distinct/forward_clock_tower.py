"""Degree-three second-zero and degree-four diagonal equations for the pure chart."""
from sympy.polys.rings import ring
import sympy as S
from time import monotonic
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)

u0,b0,z0=S.symbols("u b z")
Q0=S.Poly(4*u0**3-12*u0**2+3*u0+2,u0).monic()
assert Q0.is_irreducible
K0=S.QQ.algebraic_field((Q0,u0));U0=K0.unit
R0,B0=ring('b',K0)
C0=lambda a,b=1:K0.convert(S.Rational(a,b))
def sf(c):return S.Rational(str(c))
def norm_to_expr(g,par):
    return sum(sf(a)*par**i for i,a in enumerate(g.to_list()[::-1]))
def make_tower(side):
 d0=1+side*U0;a0=1+2*U0
 P=(B0-a0)*(B0-d0)
 J=lambda k:sum((z*C0(1,n+k+1)*B0**(n+k+1) for (n,),z in P.items()),R0.zero)
 J0=J(0);J1=J(1)
 U=J0.evaluate(B0,a0);V=J1.evaluate(B0,a0)
 assert U and V and a0 and d0 and a0!=d0
 F=V*(P-J0)-U*(B0*P-J1)
 q,r=divmod(F,B0-a0);assert not r and q.degree()==3
 h=q.monic()
 assert [(g.degree(),np) for g,np in h.factor_list()[1]]==[(3,1)]
 hsym=sum(norm_to_expr(z,u0)*b0**i for (i,),z in h.items())
 g=S.Poly(S.resultant(Q0,hsym.subs(b0,z0-u0),u0),z0).monic()
 assert g.degree()==9 and g.is_irreducible
 def vec(p):
    return S.Matrix([sf((p.get((j,),K0.zero).to_list()[::-1]+[0]*3)[i])
                       for j in range(3) for i in range(3)])
 t=R0(U0)+B0
 C=S.Matrix.hstack(*(vec(t**i%h) for i in range(9)))
 CC=C.inv()
 uv=CC*vec(R0(U0));bv=CC*vec(B0)
 def polish(f):return sum((R0(C0(b))*t**i%h for i,b in enumerate(f)),R0.zero)%h
 assert polish(uv)==R0(U0) and polish(bv)==B0 and not polish(g.all_coeffs()[::-1])
 K=S.QQ.algebraic_field((g,z0));Z=K.unit
 U=sum((K.convert(c)*Z**i for i,c in enumerate(uv)),K.zero)
 B=sum((K.convert(c)*Z**i for i,c in enumerate(bv)),K.zero)
 assert U+B==Z
 a=1+2*U;d=1+side*U
 assert B!=a
 J0a=a*a*(3*d-a)*K.convert(S.Rational(1,6))
 J0b=B**3*K.convert(S.Rational(1,3))-(a+d)*B*B*K.convert(S.Rational(1,2))+a*d*B
 Cb=(B-a)*(B-d)-J0b
 assert J0a and Cb
 S0,D=ring('D',K)
 L=lambda t:70*t**4-140*D*t**3+90*D**2*t*t-20*D**3*t+D**4
 pol=Cb*L(a)+J0a*L(B)
 assert pol.degree()>0
 fs=pol.factor_list()[1]
 now("side",side,"first field degree",g.degree(),"diagonal degree",pol.degree(),"factor degrees",[(x.degree(),e) for x,e in fs])
 return K,g,U,B,a,d,S0,D,fs

if __name__=="__main__":
 for side in (0,1):make_tower(side)
