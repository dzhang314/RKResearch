"""Seven virtual ordinary clocks at the six-zero one-physical-off-clock boundary."""
from itertools import product
import sympy as S
from sympy.polys.rings import ring
u=S.symbols("u")
f=S.Poly(u*u-2*u-1,u)
assert f.is_irreducible
K=S.QQ.algebraic_field((f,u));U=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
A,t=ring('lambda',K)
R,X=ring('X',A.to_domain())
x=lambda z:R(A(z))
def I(P):
    return sum((q*2**k*C(1,k+1) for (k,),q in P.items()),A.zero)
def det(M):
    x,y,z=M
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
for rel,front,rear in product((0,1),("star","arith"),("star","arith")):
    V=U if rel==0 else 2-U
    Wf=2*U if front=="arith" else 2-U
    Wr=2*V if rear=="arith" else 2-V
    a,b,s,l,d=1+U,1+Wf,1-Wr,1-V,K.one # physical rows 2,3,8,9, plus off clock
    assert len({a,b,s,l,d})==5
    pf=(2*Wf*U+1+2*Wf-Wf*Wf)/(2*U)
    pr=(2*Wr*V+1+2*Wr-Wr*Wr)/(2*V)
    assert pf and pr
    F0=(X-x(d))*(X-x(s))*(X-x(l))
    m=[I(F0*X**i) for i in range(5)]
    H=det([[m[i+j] for j in range(3)] for i in range(3)])
    assert H, (rel,front,rear,'both front zero weights could vanish')
    P0=F0*(X-x(a))*(X-x(b))
    m0,m1,m2=[I(P0*X**i) for i in range(3)]
    D=m0*m2-m1*m1
    print('frame',rel,front,rear,'free roots pivot',bool(D),flush=True)
    assert D
    if m0:
        k=t;q=-(m2+t*m1)/m0[(0,)]
    else:
        assert m1
        q=t;k=-m2/m1[(0,)]
    p=X*X+R(k)*X+R(q)
    P=P0*p
    assert not I(P)
    # Cardinal-weight numerators at the fixed anchors.
    ba,bb,bs,bl,bd=[I(P//(X-x(w))) for w in (a,b,s,l,d)]
    ny=(pf*bb-U*ba)/(b-a)
    nx=U*ba-ny*a
    n=lambda w:nx+ny*w
    G=V*n(s)*bl-pr*n(l)*bs
    print('framed reverse polynomial degree',G.degree(), 'active anchor weights',*[bool(y) for y in (ba,bb,bs,bl,bd)],flush=True)
    assert G.degree()==2
    for F,e in G.factor_list()[1]:
        print('candidate degree',F.degree(),flush=True)
        assert e==1 and F.degree() in (1,2)
        assert (bs*bl*bd*n(s)*n(l)).gcd(F).degree()==0
        assert (k*k-4*q).gcd(F).degree()==0
        assert all((z*z+k*z+q).gcd(F).degree()==0 for z in (a,b,s,l,d))
        sa=not ba%F;sb=not bb%F
        print('pass elementary guards with front silent',sa,sb,flush=True)
        assert not sa and not sb
        def red(poly):
            return R.from_dict({m:c%F for m,c in poly.items() if c%F})
        PP=red(P)
        BP=R.zero
        for (j,),c in PP.items():
            for ell in range(j):
                BP+=X**ell*x(c*C(2**(j-1-ell), j-ell))
        BP=red(BP)
        def freduce(a,b):return red(a*b%PP)
        cols=[freduce(BP,X**i) for i in range(7)]
        M=[[cols[j].get((i,),A.zero) for j in range(7)] + [A.one if i==0 else A.zero] for i in range(7)]
        nodal_pivot=True
        for i in range(7):
            cand=next((j for j in range(i,7) if M[j][i]%F),None)
            if cand is None:
                nodal_pivot=False
                break
            M[i],M[cand]=M[cand],M[i]
            xx,yy,zz=(M[i][i]%F).gcdex(F)
            assert zz==A.one and xx*(M[i][i]%F)+yy*F==A.one
            M[i]=[(xx*q0)%F for q0 in M[i]]
            for j in range(7):
                if j!=i:
                    c=M[j][i]
                    M[j]=[(x0-c*y0)%F for x0,y0 in zip(M[j],M[i])]
        assert nodal_pivot
        inv=R.from_dict({(i,):M[i][-1] for i in range(7) if M[i][-1]})
        assert freduce(inv,BP)==R.one
        seed=x(nx)+x(ny)*X
        rs=[freduce(inv,seed*seed*X**i).get((6,),A.zero) for i in (0,1)]
        print("forward pure-square moments vanish?",[not z for z in rs],flush=True)
        assert all(rs), "A genuine projected square mode remains"
