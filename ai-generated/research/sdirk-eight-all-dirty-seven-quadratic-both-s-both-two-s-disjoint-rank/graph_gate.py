from sympy.polys.rings import ring
from projection_rank import phases
from number_field import gcd
def paid(ph,z):
    k=lambda x:1+2*x-x*x
    if ph=='S':return 2-z,k(z)/2,k(z)/2
    a=z if ph=='A2' else z/2
    D=-2+a+4*a*a-a**3
    N=(1+4*a-4*a*a)*D+4*a*a*(3*a-2)
    return (2*z,k(a)/2,N/(2*D)) if ph=='A2' else (z/2,N/(2*D),k(a)/2)
def graph(K,u,H,mode):
    left,rt=phases(mode)
    s,f,fs=paid(left,u)
    t=s*(H-s)/(H-s-2*H*fs)
    o=H-t
    v=o/2 if rt=='A2' else (2*o if rt=='A3' else 2-o)
    q=H-v
    _,r,rs=paid(rt,v)
    assert fs*t*t==rs*(H-s)**2
    Y,y=ring('y',K)
    z=y-H/2;m=1+H/2
    L3=z**3-3*m*m*z/5
    L4=z**4-6*m*m*z*z/7+3*m**4/35
    ev=lambda f,w:f.evaluate(y,w)
    P=ev(L3,u)/ev(L4,u)
    Q=ev(L3,q)/ev(L4,q)
    M=(L3-(P+(Q-P)*(y-u)/(q-u))*L4).exquo((y-u)*(y-q))
    assert M.degree()==3 and M[(0,)]
    m0,m1,m2,m3=(M[(i,)] for i in range(4))
    A,l=ring('l',K)
    r2=(fs-((H-s)+s*l)/(2*H))/(s*(s-H))
    r1=(l-1)/(2*H)-H*r2
    r0=A(K.one/2)
    L1=2*m1-4*m0*r1
    g2=m2-2*m0*r2-L1*r1
    g3=m3-L1*r2
    G=gcd(g2,g3)
    return G.degree()
