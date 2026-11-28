"""Exact signed-first projections for star front, cubic fifth, actual hole seven."""
from flint import fmpq, fmpq_mpoly_ctx, fmpq_poly
from itertools import combinations
from functools import lru_cache

C=fmpq_mpoly_ctx.get(("u","r","gamma"),ordering="lex")
v,r,g=C.gens()
PI=1400*g**4-840*g**3+180*g*g-20*g+1
d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
ell0=fmpq(4,3)*(1-2*d0)
ell1=8*(d2-70*g**4)
G=fmpq_poly([0,1])
D2=fmpq_poly([1,-20,180,-840,1680])/1680
J3=[(0,1),(0,2),(1,2)]


def mul(a,b):
    out=[C.constant(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out


def ev(P,x):
    return sum(a*x**i for i,a in enumerate(P))


def integral(P,j=0):
    return sum(a/(i+j+1) for i,a in enumerate(P))


def co(P,k):
    return C.from_dict({(0,j,l):a for (i,j,l),a in P.to_dict().items() if i==k})


def exact(a,b):
    q,rem=divmod(a,b)
    assert not rem
    return q


def guard(P,guards):
    assert P!=0
    e=[]
    for z in guards:
        a=0
        while True:
            q,t=divmod(P,z)
            if t:
                break
            P=q
            a+=1
        e.append(a)
    return P,e


def det3(rows):
    a,b,c=rows
    return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3])
               for i in range(3))


@lru_cache(None)
def generic():
    E2=[2*g*g,-4*g,C.constant(1)]
    C3=[6*g**3,-18*g*g,9*g,C.constant(-1),C.constant(0)]
    moment=lambda P,j:integral(P,j+1)-r*integral(P,j)
    M=[[moment(E2,i+j) for j in range(3)] for i in range(3)]
    rhs=[-moment(C3,i) for i in range(3)]
    h=det3(M)
    A,B,L=[det3([[rhs[i] if j==k else M[i][j] for j in range(3)] for i in range(3)])
           for k in range(3)]
    abc=[A,B,L]
    H=[h*a+b for a,b in zip(C3,mul(E2,abc))]
    assert H[-1]==L
    P=L*g*g*d0-d2*A
    W1=8*P-9*g*g*L*ell1
    W0=g*(-56*P-9*g*g*L*ell0)+72*g*g*h*d2
    hr=ev(H,r)
    beta=integral(H)
    lr=70*r**4-140*r**3+90*r*r-20*r+1
    gs=(g,h,exact(L,g*g),PI,d2,W1,P,hr,beta,lr)
    S,e=guard(d2*B-g*d1*L,gs)
    assert S.degrees()==(0,3,6) and e==[0,0,0,1,0,0,0,0,0,0]
    return H,E2,abc,W0,W1,S,gs


def signed(H,D,gs):
    hr,beta=gs[-3:-1]
    J=lambda P,k:hr*integral(P,k)-beta*r**k*ev(P,r)
    h4,h5=[J(H,j) for j in (4,5)]
    D0,D1=J(D,0),J(D,1)
    if len(D)==9:
        return (D[8]*h4-H[-1]*D0, D[7]*h4+D[8]*h5-H[-2]*D0-H[-1]*D1)
    assert len(D)==8
    return (D0,D[7]*h4-H[-1]*D1,D[6]*h4+D[7]*h5-H[-2]*D1-H[-1]*J(D,2))


def raws(P,gs,sizes,powers):
    G=[guard(X,gs) for X in P]
    assert [x.degrees() for x,e in G]==sizes
    assert [e for x,e in G]==[list(row)+[0]*6 for row in powers]
    return [x for x,e in G]


def star():
    H,E2,abc,W0,W1,S,gs=generic()
    x=1-g
    t=x-g
    c,d=t-g*v,t+g*v
    k=2-v*v
    tail=exact((1-v)*ev(H,c)-(1+v)*ev(H,d)+2*v*k*ev(H,x),v*(1-v*v))
    a,b=co(tail,0),co(tail,2)
    assert tail==a+b*v*v and b==2*g**4*H[-1]
    two=[b*t*t+g*g*a,-2*t*b,b]
    D=mul(mul(mul(mul(E2,abc),[W0,W1]),[-x,C.constant(1)]),two)
    B=raws(signed(H,D,gs),gs,[(0,13,22),(0,16,26)],[(9,1,1,1),(9,1,0,1)])
    m=gamma_projection(S,B,[138,165])
    assert m==G**3*D2**3
    print("ordinary star: single-gamma exact degrees 138,165; only gamma^3 d2^3",
          flush=True)


def arithmetic():
    H,E2,abc,W0,W1,S,gs=generic()
    x=1-g
    c,d=x-g*v,x-2*g*v
    k=1+2*v-v*v
    J=2+3*v-12*v*v+4*v**3
    Hrear=-2+v+4*v*v-v**3
    F=exact(Hrear*ev(H,d)+2*J*ev(H,c)-k*J*ev(H,x),v*v)
    assert F.degrees()[0]==5 and co(F,5)==-8*g**4*H[-1]
    D=mul(mul(mul(mul(mul(E2,abc),[W0,W1]),[-x,C.constant(1)]),
                  [-d,C.constant(1)]),[-c,C.constant(1)])
    B=raws((*signed(H,D,gs),F),gs,[(2,10,17),(2,13,21),(5,3,7)],
           [(5,1,1,1),(5,1,0,1),(2,0,0,0)])
    P=pair_projection(B,gs,[(0,46,68),(0,56,95),(0,71,115)],4)
    m=gamma_projection(S,P,[462,600,735])
    assert m==G**12*D2**12
    print("ordinary arithmetic: single-gamma exact degrees 462,600,735;",
          "only gamma^12 d2^12",flush=True)


def silent8():
    H,E2,abc,W0,W1,S,gs=generic()
    x=1-g
    c=v
    D=mul(mul(mul(mul(E2,abc),[W0,W1]),[-x,C.constant(1)]),[-c,C.constant(1)])
    B=raws(signed(H,D,gs),gs,[(1,10,15),(1,10,15),(1,13,19)],
           [(3,1,0,1),(5,1,1,1),(5,1,0,1)])
    P=pair_projection(B,gs,[(0,20,30),(0,23,34),(0,23,33)],0)
    m=gamma_projection(S,P,[204,231,228])
    f,rem=divmod(m,G**6*D2**6)
    assert not rem and f.degree()==54 and f.leading_coefficient()==1
    print("actual silent eighth: single-gamma exact degrees 204,231,228;",
          "true gamma,d2 powers removed, full degree 54",flush=True)
    return f,S,P,B


def pair_projection(P,gs,degs,n):
    A=[guard(P[i].resultant(P[j],0),gs) for i,j in J3]
    assert [z.degrees() for z,e in A]==degs
    assert all(e==[n]+[0]*9 for z,e in A)
    return [z for z,e in A]


def gamma_projection(S,P,ds):
    A=[S.resultant(T,1) for T in P]
    assert [q.degrees() for q in A]==[(0,0,d) for d in ds]
    A0=A[0]
    for q in A[1:]:
        A0=A0.gcd(q)
    assert A0!=0
    terms=A0.to_dict()
    Q=fmpq_poly([terms.get((0,0,i),0) for i in range(A0.degrees()[2]+1)])
    return Q/Q.leading_coefficient()
