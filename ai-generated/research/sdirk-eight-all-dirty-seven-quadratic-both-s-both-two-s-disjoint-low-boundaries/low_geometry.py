import sympy as S
"""Low/low S tap law disjoint rank-loss charts: one exact parameter."""
from sympy import QQ
from sympy.polys.fields import field
from sympy.polys.rings import ring
F,a=field('a',QQ)
T,y=ring('y',F.to_domain())
def D(x):return -2+x+4*x*x-x**3
def k(x):return 1+2*x-x*x
def N(x):return (1+4*x-4*x*x)*D(x)+4*x*x*(3*x-2)
def off(mode,a):return 2*a if mode=='A3' else 2-a
def pairs(mode,a):
    if mode=='S':return k(a)/2,[a,a-1,a-2,k(a)]
    return N(a)/(2*D(a)),[a,a-2,k(a),D(a),N(a),3*a-2]
def strip(p,g):
    for z in g:
        while (d:=p.gcd(z.numer)).degree()>0:p=p.exquo(d)
    return p
def graph(mode,case):
    fwd,rev=mode[:1] if mode.startswith('S') else mode[:2],None
    rev=mode[len(fwd):]
    if case=='half':
        H=F(2);b=(12-5*a)/(5-2*a);G=[5-2*a]
    elif case=='curve':
        b=a;H=2/(a-2);G=[a-2]
    else:
        assert mode=='A3S' and case in ('pcenter','qcenter')
        b=a;H=4*a if case=='pcenter' else 4-2*a;G=[]
    h=H/2;m=1+h
    p=off(fwd,a);q=H-off(rev,b);s=a;t=H-b
    f,g=pairs(fwd,a);r,j=pairs(rev,b)
    fs,rs=k(a)/2,k(b)/2
    Z=F.zero
    from itertools import combinations
    guards=[H,m]+[x-y0 for x,y0 in combinations((Z,H,p,q,s,t),2)]+g+j
    assert all(guards)
    assert all(strip(z.denom,G).degree()==0 for z in guards)
    G+=guards
    z=y-T(h)
    L3=z**3-T(3*m*m/5)*z
    L4=z**4-T(6*m*m/7)*z*z+T(3*m**4/35)
    def ev(Q,w):
        q=F.zero
        for c in Q.to_dense():q=q*w+c
        return q
    L0=ev(L4,Z);Lp,Lq=ev(L4,p),ev(L4,q)
    assert Lp and Lq and all(strip(v.denom,G).degree()==0 for v in (Lp,Lq))
    G += [Lp,Lq]
    K0=[Z,2*L0];KH=[2*L0,Z]
    Ks=[Z,ev(L4,s)/fs];Kt=[ev(L4,t)/rs,Z]
    aK,bK=[s*(s-H)*(H*Kt[i]-(H-t)*K0[i]-t*KH[i])-
            t*(t-H)*(H*Ks[i]-(H-s)*K0[i]-s*KH[i]) for i in (0,1)]
    assert all(strip(v.denom,G).degree()==0 for v in (aK,bK))
    if case=='half':
        assert bK
        G.append(bK)
        lam=-aK/bK
    else:
        assert not (aK+bK)
        lam=F.one
    assert lam
    assert strip(lam.denom,G).degree()==0
    G+=[lam]
    R2=(fs-(H-s+s*lam)/(2*H))/(s*(s-H))
    R1=(lam-1)/(2*H)-H*R2
    assert (F.one/2+R1*t+R2*t*t)==lam*rs
    assert R2
    Fp=ev(L3,p)/Lp;Fq=ev(L3,q)/Lq
    b0=(Fq-Fp)/(q-p)
    assert b0
    M=(L3-(T(Fp)+T(b0)*(y-T(p)))*L4).exquo((y-T(p))*(y-T(q)))
    assert M.degree()==3
    m0,m1,m2,m3=[M.get((i,),Z) for i in range(4)]
    assert m0
    assert all(strip(v.denom,G).degree()==0 for v in (R2,b0,m0))
    G += [R2,b0,m0]
    l1=2*m1-4*m0*R1
    E=m2-2*m0*R2-l1*R1
    Q=m3-l1*R2
    assert all(strip(x.denom,G).degree()==0 for x in G+[aK,bK,R1,R2,E,Q])
    z=E.numer.gcd(Q.numer)
    if case in ('pcenter','qcenter'):
        lp=ev(L4,p);lq=ev(L4,q)
        def K(y0):
            out=F.zero
            for h1,v1 in [(Z,2*L0),(s,ev(L4,s)/fs),(H,2*L0)]:
                n=v1
                for h2,v2 in [(Z,2*L0),(s,ev(L4,s)/fs),(H,2*L0)]:
                    if h1!=h2:n*= (y0-h2)/(h1-h2)
                out+=n
            return out
        def R(y0):return F.one/2+R1*y0+R2*y0*y0
        Dgate=(lp-f*K(p))*r*(r-R(q))-(lq-r*K(q))*f*(f-R(p))
        assert strip(Dgate.denom,G).degree()==0
        zy=z.gcd(Dgate.numer)
        print(mode,case,'graph vs paid D',z.degree(),zy.degree(),flush=True)
        z=zy
    assert z
    z1=strip(z,G)
    print(mode,case,'graph gcd',z.degree(),'paid trimmed',z1.degree(),flush=True)
    return S.Poly(z1.as_expr(),S.Symbol('a'),domain=S.QQ).monic()
