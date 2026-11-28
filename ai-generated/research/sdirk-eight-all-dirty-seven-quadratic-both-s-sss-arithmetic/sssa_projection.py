"""Both-S true SSS arithmetic, with forced literal opposite SDD."""
from disjoint_projection import F,H,d,CZ,ip,strip
from collections import defaultdict
import sympy as S
u=d;m=(H+2)/2
one=F(1)
def ev(a,x):
    out=F()
    for e in reversed(a):out=out*x+e
    return out
def qrem(a,q0,q1):
    aa=list(a);b=[F() for _ in range(max(0,len(aa)-2))]
    for i in reversed(range(2,len(aa))):
        c=aa[i];b[i-2]=c
        aa[i-1]-=q1*c;aa[i-2]-=q0*c
    return b,aa[:2]
def mul(a,b):
    c=[F() for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
      for j,y in enumerate(b):c[i+j]+=x*y
    return c
def compose_lin(P,a,b):
    out=[F()]
    for v in reversed(P):
        out=mul(out,[b,a]);out[0]+=v
    while out and not out[-1]:out.pop()
    return out
def K(v):return 1+2*v-v*v
def D(v):return -2+v+4*v*v-v*v*v
def N(v):return (1+4*v-4*v*v)*D(v)+4*v*v*(3*v-2)
def frame():
    g={'front_taps':[u,u-2,D(u),N(u),K(u),3*u-2],
       'distinct':[m,H,H-u,H-2*u]}
    ell=(3*u-2)/D(u)
    a=1-ell*u;b=ell-one/2
    R=lambda v:one/2+a*v+b*v*v
    q0=one/(2*b);q1=a/b
    # Evaluate X=y-H/2 in the two centered Legendre modes.
    x=[-H/2,one]
    x2=mul(x,x);x3=mul(x,x2);L4=mul(x2,x2)
    for i in range(3):L4[i]-=6*m*m*x2[i]/7
    L4[0]+=3*m**4/35
    L3=x3[:]
    for i in range(2):L3[i]-=3*m*m*x[i]/5
    S4=mul(mul([F(),one],[-u,one]),mul([-2*u,one],[-H,one]))
    _,(a4,b4)=qrem(L4,q0,q1)
    _,(aS,bS)=qrem(S4,q0,q1)
    E=a4*bS-b4*aS
    adj=[a4-b4*q1,-b4]
    det=a4*adj[0]+b4*b4*q0
    _,FF=qrem(mul(L3,adj),q0,q1)
    v=mul(FF,L4)
    for i,f in enumerate(L3):v[i]=det*f-v[i]
    for i in range(len(L3),len(v)):v[i]=-v[i]
    P,rem=qrem(v,q0,q1)
    assert not any(rem) and len(P)==4
    aa,bb,cc,dd=P
    g['pivots']=[b,R(H),det,dd]
    aux=sum(g.values(),[])
    assert all(aux)
    base=[ip(a.n) for a in aux]
    assert all(strip(ip(a.d),base).total_degree()==0 for a in aux)
    g={k:[ip(a.n) for a in z] for k,z in g.items()}
    g['denominators']=[ip(a.d) for a in aux]
    guard=sum(g.values(),[])
    assert all(strip(ip(a.d),guard).total_degree()==0 for a in [E,*P])
    eq=lambda f:strip(ip(f.n),guard)
    return E,P,guard,g,eq,(a,b,R,L4,S4,q0,q1)
def univariate_pairs():
    z,a,b,c,d=S.symbols('z a b c d')
    p=a*z**3+b*z*z+c*z+d
    q=7*a*z*z+3*b*z+c
    ans=S.factor(p.as_poly(z).resultant(q.as_poly(z)))
    ans=S.cancel(ans/a)
    return S.Poly(ans,a,b,c,d)
ARITH=univariate_pairs()
def necessary(mode):
    E,P,gg,groups,eq,data=frame()
    d,c,b,a=P
    if mode=='S':
        # If the first two D roots add to 2H-2, the third equals -b/a-(2H-2).
        w=-b-a*(2*H-2)
        q=d*a*a+c*w*a+b*w*w+w**3
    else:
        PP=compose_lin(P,one,H)
        q=F()
        for ex,v in ARITH.terms():
            T=F(int(v))
            for p,e in zip(reversed(PP),ex):T*=p**e
            q+=T
    assert all(strip(ip(a.d),gg).total_degree()==0 for a in [E,q])
    E,Q=map(eq,[E,q])
    print(mode,'factors before projection',[a.degrees() for a in (E,Q)],flush=True)
    uh=[a for a in gg if not a.degrees()[0]]
    return E,Q,uh,groups
def project(mode):
    E,Q,uh,groups=necessary(mode)
    raw=E.resultant(Q,'H')
    R=strip(raw,uh)
    print(mode,'u projection raw/guarded',raw.total_degree(),R.total_degree(),flush=True)
    factors=R.factor()[1]
    print(mode,'u factors',[(p.total_degree(),n) for p,n in factors],flush=True)
    return factors,E,Q,groups
