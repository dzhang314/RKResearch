"""Arithmetic front leading drop: u=1 or u=2 and fixed monomial profile."""
from sympy.polys.rings import ring
import sympy as S
v=S.symbols('v')
h=S.Poly(v*v-2*v-1,v)
assert h.is_irreducible
K=S.QQ.algebraic_field((h,v));V=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
T,X=ring('X',K)
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
for u in (1,2):
    a=C(2 if u==1 else 1)
    P=[K.zero,K.one] if u==1 else [K.one]
    for i in range(3):
      D=C(2+i*u)
      for rear in ('star','arith'):
        W=2-V if rear=='star' else 2*V
        s=D-1-W;t=D-1-V
        assert len({a,s,t})==3
        p=(2*W*V+1+2*W-W*W)/(2*V)
        def I(P):return sum((q*D**k*C(1,k+1) for (k,),q in P.items()),K.zero)
        A0=(X-a)*(X-s)*(X-t)
        M0=[I(A0*X**j) for j in range(5)]
        R0=p*(A0//(X-s))-V*(A0//(X-t))
        R1=[I(R0*X**j) for j in range(4)]
        M=[[M0[0],M0[1],M0[2]],[M0[1],M0[2],M0[3]],[R1[0],R1[1],R1[2]]]
        E=det(M)
        print(u,i,rear,'ordinary linear pivot',bool(E),flush=True)
        rhs=[-M0[3],-M0[4],-R1[3]]
        Ns=[]
        for k in range(3):
            N=[z[:] for z in M]
            for j in range(3):N[j][k]=rhs[j]
            Ns.append(det(N))
        if not E:
            assert any(Ns)
            continue
        Ns=[q/E for q in Ns]
        q=X**3+Ns[2]*X*X+Ns[1]*X+Ns[0]
        P6=A0*q
        Bpoly=T.zero
        for (ell,),c in P6.items():
            for j in range(ell):
                Bpoly+=c*D**(ell-1-j)*C(1,ell-j)*X**j
        Rback=(X-s)*(X-t)
        J0=sum((c*C(1,n+1)*X**(n+1) for (n,),c in Rback.items()),T.zero)
        rev=lambda y:J0.evaluate(X,D)-J0.evaluate(X,y)
        F=(Rback-(J0.evaluate(X,D)-J0))*Bpoly+rev(t)*I(P6//(X-t))
        gg=q.gcd(F)
        print("raw reverse gcd",gg.degree(),flush=True)
        assert gg.degree()==0
