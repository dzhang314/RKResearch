#!/usr/bin/env python3
"""Fixed-limb dyadic enclosures and small modular tests for prescribed pairs."""
from dataclasses import dataclass
from math import isqrt
from time import monotonic

BITS=288
SCALE=1<<BITS
Q=2147483647
began=monotonic()


def need(b, what):
    if not b:
        raise AssertionError(what)


def ceildiv(a,b):
    return -((-a)//b)


@dataclass(frozen=True)
class I:
    l:int
    u:int

    def __post_init__(self):
        need(self.l<=self.u and max(abs(self.l).bit_length(),abs(self.u).bit_length())<=BITS+64,
             "fixed dyadic endpoint bit-cap")
        need(monotonic()-began<10,"foreground wall guard")

    @classmethod
    def c(cls,a,b=1):
        need(b>0,"positive literal denominator")
        return cls(a*SCALE//b,ceildiv(a*SCALE,b))

    def __add__(x,y):
        return I(x.l+y.l,x.u+y.u)

    def __neg__(x):
        return I(-x.u,-x.l)

    def __sub__(x,y):
        return x+(-y)

    def __mul__(x,y):
        z=[x.l*y.l,x.l*y.u,x.u*y.l,x.u*y.u]
        return I(min(z)//SCALE,ceildiv(max(z),SCALE))

    def __truediv__(x,y):
        need(y.l>0 or y.u<0,"nonzero dyadic divisor")
        rec=I(SCALE*SCALE//y.u,ceildiv(SCALE*SCALE,y.l))
        return x*rec

    def __pow__(x,n):
        r=I.c(1)
        for _ in range(n):
            r=r*x
        return r

    def positive(x):
        return x.l>0

    def negative(x):
        return x.u<0

    def between(x,l,u):
        return x.l>l.u and x.u<u.l

    def bracket(x,d=10**6):
        return (x.l*d//SCALE,ceildiv(x.u*d,SCALE))


@dataclass(frozen=True)
class F:
    x:int

    @classmethod
    def c(cls,a,b=1):
        return cls(a*pow(b,-1,Q)%Q)

    def __add__(x,y):return F((x.x+y.x)%Q)
    def __neg__(x):return F(-x.x%Q)
    def __sub__(x,y):return x+(-y)
    def __mul__(x,y):return F(x.x*y.x%Q)
    def __truediv__(x,y):return F(x.x*pow(y.x,-1,Q)%Q)
    def __pow__(x,n):return F(pow(x.x,n,Q))


def nodal(roots,R):
    P=[R.c(1)]
    for z in roots:
        T=[R.c(0) for _ in range(len(P)+1)]
        for j,c in enumerate(P):
            T[j]=T[j]-z*c
            T[j+1]=T[j+1]+c
        P=T
    return P


def moment(P,R,shift=0,centered=False):
    s=R.c(0)
    for j,c in enumerate(P):
        if not centered or (j+shift)%2==0:
            s=s+c*R.c(1,j+shift+1)
    return s


def c_data(xs,R,centered=False):
    h=moment(nodal(xs,R),R,2,centered)
    C=[moment(nodal(xs[:j]+xs[j+1:],R),R,0,centered) for j in range(len(xs))]
    return h,C


def cubic_parameters(xs,labels,R,ulabel,vlabel,centered=False):
    ui,vi=labels.index(ulabel),labels.index(vlabel)
    u,v=xs[ui],xs[vi]
    h,C=c_data(xs,R,centered)
    ell=v-u
    a,b=h/(C[ui]*ell**3),-h/(C[vi]*ell**3)
    return u,v,ell,a,b


def triple(R,u,ell,a,b):
    o=R.c(1)
    return [u+ell*a*(b+o)/(a-b), u+ell*(a-b)/(a+o), u+ell*(a+o)/(b+o)]


def reconstruct(R):
    labels=["m1","m2","m3","p1","p2","p3","m","p"]
    xs=[R.c(-1)]*3+[R.c(1)]*3+[R.c(-1,3),R.c(1,3)]
    for j,(ul,vl) in enumerate((("p","p1"),("1c","p2"),("m1","1a"),("m2","2b")),1):
        ui,vi=labels.index(ul),labels.index(vl)
        u,v,d,a,b=cubic_parameters(xs,labels,R,ul,vl,centered=True)
        out=triple(R,u,d,a,b)
        xs=[x for i,x in enumerate(xs) if i not in (ui,vi)]+out
        labels=[n for i,n in enumerate(labels) if i not in (ui,vi)]+[f"{j}{k}" for k in "abc"]
    return labels,[(R.c(1)+y)*R.c(1,2) for y in xs]


def ec_cert(R,a,b):
    o,k=R.c(1),R.c
    need(((a+b-o)**3+k(27)*a*b).x!=0,"smooth elliptic model modulo q")
    aa,bb=b-a-o,a*(k(2)*b+o)
    eta,theta=k(4)*a*b*(a-b),-k(4)*a*a*b*(b+o)
    A,B,C=aa*aa-k(4)*bb,k(2)*aa*eta-k(4)*theta,eta*eta
    disc=A*A*B*B-k(4)*B**3-k(4)*A**3*C-k(27)*C*C+k(18)*A*B*C
    need(disc.x!=0,"good reduction")
    y=-eta
    X,Y=k(0),y
    found={}
    for i in range(2,13):
        m=B/(k(2)*y) if i==2 else (Y-y)/X
        NX=m*m-A-X
        NY=m*(X-NX)-Y
        need(NY*NY==NX**3+A*NX*NX+B*NX+C,"exact affine curve check")
        X,Y=NX,NY
        if i in (6,9,12):
            found[i]=(X.x,Y.x)
    return (A.x,B.x,C.x,y.x,disc.x),found


labels,xs=reconstruct(I)
one,zero=I.c(1),I.c(0)
u,v,d,a,b=cubic_parameters(xs,labels,I,"m3","p3")
need(a.between(I.c(7,1000),I.c(9,1000)) and b.between(I.c(13,1000),I.c(15,1000)),
     "explicit endpoint parameter bounds")
print("Endpoint pair (0,1): 10^6-scaled enclosing integers for a,b =",a.bracket(),b.bracket())
def G(u,v,ru,rv,t,X):
    return (X-t)*(X-u)*(X-v)+ru*(X-v)+rv*(X-u)
cuts=[zero,I.c(1,4),I.c(3,4),one]
values=[G(u,v,a,b,I.c(1,2),x) for x in cuts]
need(len(values)==4 and all((g.negative() if j%2==0 else g.positive()) for j,g in enumerate(values)),
     "four endpoint-pair cuts prove genuine interior-root real open")
print("Endpoint pair at tau=1/2: signs -,+,-,+ at 0,1/4,3/4,1; 10^6 buckets",
      [g.bracket() for g in values])
print("Seed cofactor signs along labels:", " ".join(f"{l}:{'+' if c.positive() else '-' if c.negative() else '?'}"
      for l,c in zip(labels,c_data(xs,I)[1])))
ul,vl="m","2a"
u,v,d,a,b=cubic_parameters(xs,labels,I,ul,vl)
ru,rv=d*d*a,d*d*b
print(f"Interior pair {ul},{vl}: 10^6 buckets a,b and R_u,R_v",
      a.bracket(),b.bracket(),ru.bracket(),rv.bracket())
interval_gate=one+ru/(u*(one-u))+rv/(v*(one-v))
print("Interior pair F(1)-F(0) bucket:",interval_gate.bracket())
coords=triple(I,u,d,a,b)
print("Interior pair rank-free coordinates buckets:",[x.bracket() for x in coords])
print("Interior pair negative-pole real-window gate:",
      bool(ru.negative() and rv.negative() and interval_gate.positive()))
need(all(Q%p for p in range(3,isqrt(Q)+1,2)),"fixed large prime certified")
labelsF,xsF=reconstruct(F)
need(labelsF==labels and len({s.x for s in xsF})==12,"same verified seed labels mod q")
_,_,_,af,bf=cubic_parameters(xsF,labels,F,ul,vl)
print("Interior pair (A,B,C,D_y,disc), [6],[9],[12]D mod q:",ec_cert(F,af,bf))

def real_window(R,u,v,ru,rv):
    o=R.c(1)
    return -ru/u-rv/v, o+ru/(o-u)+rv/(o-v)


def interval_replace(R,labels,xs,ul,vl,j):
    indices=labels.index(ul),labels.index(vl)
    u,v,d,a,b=cubic_parameters(xs,labels,R,ul,vl)
    new=triple(R,u,d,a,b)
    out=[x for i,x in enumerate(xs) if i not in indices]+new
    names=[l for i,l in enumerate(labels) if i not in indices]+[f"{j}{l}" for l in "abc"]
    return names,out,new


def exact_checks(R,xs):
    P=nodal(xs,R)
    h,C=c_data(xs,R)
    need(len(set(z.x for z in xs))==len(xs) and h.x and all(c.x for c in C),
         "q-local distinct sites, nonzero exact defect and cofactors")
    need(moment(P,R).x==0 and moment(P,R,1).x==0, "residue sanity for exactly paid rows")
    return h.x


need(u.between(zero,one) and v.between(zero,one) and ru.negative() and rv.negative()
     and interval_gate.positive(),"whole circle split with nonempty interior window")
need(all(x.between(zero,one) for x in coords),"literal first interval rank-free move")
f0,f1=real_window(I,u,v,ru,rv)
k=moment(nodal(xs,I),I,3)
h,_=c_data(xs,I)
t0=k/h-u-v
need(t0.between(f0,f1),"zero-defect parameter is inside the real window")
print("First negative-pole window and zero-defect parameter buckets:",f0.bracket(),f1.bracket(),t0.bracket())

labI,xsI,newI=interval_replace(I,labels,xs,ul,vl,5)
labM,xsM,newM=interval_replace(F,labelsF,xsF,ul,vl,5)
need(labI==labM and all(x.between(zero,one) or n in ("m3","p3") for n,x in zip(labI,xsI)),
     "all interval sites, endpoints retained")
h1=exact_checks(F,xsM)
need(h1==621252393,"literal order-15 first defect")
print("Explicit exact order 15: 13 contributing interval sites; first defect mod q =",h1)
hn=c_data(xsI,I)[0]
delta=hn/h
need(delta.positive() or delta.negative(), "defect-ratio sign resolved")
need(newI[1].u < u.l and u.u < newI[2].l and newI[2].u < v.l and v.u < newI[0].l,
     "fresh labels are right, left, middle in this prescription")
ul2,vl2=("5c","5a") if delta.positive() else ("5b","5c")
u2,v2,d2,a2,b2=cubic_parameters(xsI,labI,I,ul2,vl2)
ru2,rv2=d2*d2*a2,d2*d2*b2
f02,f12=real_window(I,u2,v2,ru2,rv2)
need(ru2.negative() and rv2.negative(),"automatic adjacent negative-pole signs")
print(f"Next adjacent pair {ul2},{vl2}: delta, F(1)-F(0) buckets",
      delta.bracket(),(f12-f02).bracket())
test2=triple(I,u2,d2,a2,b2)
print("Second prescribed rank-free coordinates buckets:",[j.bracket() for j in test2])
need(ul2=="5b" and vl2=="5c" and (f12-f02).positive(),"second named adjacent pair/window")
need(all(x.between(zero,one) for x in test2),"literal second interval rank-free move")
labM2,xsM2,_=interval_replace(F,labM,xsM,ul2,vl2,6)
need(len(xsM2)==14 and all(l in labM2 for l in ("m3","p3")),"retained endpoints and width 14")
h2=exact_checks(F,xsM2)
need(h2==1366411467,"literal order-16 first defect")
print("Explicit exact order 16: 14 contributing interval sites; first defect mod q =",h2)
_,_,_,a2m,b2m=cubic_parameters(xsM,labM,F,ul2,vl2)
print("Second adjacent pair nontorsion model/group residues:",ec_cert(F,a2m,b2m))
print("PASS: two prescribed interval moves, exact signs and modular certificates; no higher-order scan.")
