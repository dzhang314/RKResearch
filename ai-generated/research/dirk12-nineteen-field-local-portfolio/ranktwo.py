"""Exact early reverse rank-two compatibility for 20-stage DIRK12 splice."""
from fractions import Fraction as Q
from math import prod
from probe import pmul,ev,prim,cardinals,vecmul

def padd(a,b):
    n=max(len(a),len(b))
    return tuple((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n))

def sc(a,s):
    return tuple(s*x for x in a)

def psum(ls):
    v=(Q(0),)
    for z in ls: v=padd(v,z)
    return v

def const(x):
    return (x,)

def conv(v,w):
    return psum(pmul(a,b) for a,b in zip(v,w,strict=True))

def dot(v,w):
    return psum(sc(a,b) for a,b in zip(v,w,strict=True))

def poles(x,w):
    return [0]+[Q(1)/(w[i]*x[i]*prod(x[i]-x[j] for j in range(1,len(x)) if j!=i))
                for i in range(1,len(x))]

def early(x,w):
    # x[0]=1; first 3 nonzero reflected clocks are x[1],x[2],x[3].
    y=tuple(1-z for z in x)
    f=poles(x,w)
    g1=y[1]**3/6
    # t=1/(x[1]-root); t=0 includes the constant numerator.
    gs=[(Q(0),)]+[sc((Q(1),x[i]-x[1]),g1*f[i]/f[1]) for i in range(1,len(x))]
    row1=tuple(map(const,(y[1]/2,y[1]/2)))
    h1=conv(row1,gs[:2]); j1=const(y[1]**4/4)
    ell2=cardinals(y[:3])
    row2=[padd(const(ev(prim(p),y[2])),sc(gs[2],p[2])) for p in ell2]
    h2=conv(row2,gs[:3])
    j2=padd(dot(row2,[a**3 for a in y[:3]]),const(-y[2]**4/4))
    a=(x[2]-x[3])/(x[2]-x[1]); b=1-a
    # Both target values below are multiplied by gs[2].
    tarH=pmul(gs[3],padd(sc(pmul(h1,gs[2]),a/g1),sc(h2,b)))
    tarJ=pmul(gs[3],padd(sc(pmul(j1,gs[2]),a/g1),sc(j2,b)))
    ell3=cardinals(y[:4])
    row3=[padd(pmul(padd(const(ev(prim(p),y[3])),sc(gs[3],p[2])),gs[2]),
               sc(tarJ,p[3])) for p in ell3]
    gate=padd(conv(row3,gs[:4]),sc(tarH,-1))
    return gate,(gs,h1,h2,j1,j2)

def f6(u,z):
    return tuple((Q(0),)*i+(Q(0),u*z,-u-z,Q(1))+(Q(0),)*(3-i)
                 for i in range(4))

def lift(x,w,W,seed):
    y=[1-z for z in x]
    _,(G,H1,H2,J1,J2)=early(x,w)
    g=[ev(a,seed) for a in G]
    if g[2]==0:
        return None
    def affine(a,b):
        va,vb=ev(a,seed)/g[1],ev(b,seed)/g[2]
        return [g0*(va+(xx-x[1])*(vb-va)/(x[2]-x[1]))
                for xx,g0 in zip(x,g,strict=True)]
    h=affine(H1,H2); j=affine(J1,J2)
    G4=[g,vecmul(g,x)]
    n=len(x)
    inds=[(i,j) for i in range(n) for j in range(i+1)]
    M=[];b=[]
    def add(a,z):
        M.append(a);b.append(z)
    def power(v,k):
        return [a**k for a in v]
    def row(vec,target):
        for i in range(n):
            add([vec[j] if ii==i else 0 for ii,j in inds],target[i])
    def ann(vec,target,functional):
        add([w[i]*functional[i]*vec[j] for i,j in inds],
            sum(w[i]*functional[i]*target[i] for i in range(n)))
    row([1]*n,y)
    row(y,[a**2/2 for a in y])
    row(power(y,2),[a**3/3+v for a,v in zip(y,g,strict=True)])
    row(power(y,3),[a**4/4+v for a,v in zip(y,j,strict=True)])
    row(g,h)
    for f in W:
        fun=[ev(f,z) for z in x]
        ann(power(y,4),[a**5/5 for a in y],fun)
        for v in G4:
            ann(v,[0]*n,fun)
    return M,b,inds
