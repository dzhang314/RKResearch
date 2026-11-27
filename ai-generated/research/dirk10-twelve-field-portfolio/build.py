"""Exact standard-library parameterized constructor and modular chart scout."""
from fractions import Fraction as Q
from itertools import permutations
from functools import reduce
from math import lcm
import argparse,operator,json

class Split:
    """Prime field arithmetic for scouting only; no modular proof assumptions."""
    __slots__=("v","p")
    def __init__(self,a,p):
        a=Q(a); self.p=p; self.v=a.numerator*pow(a.denominator,-1,p)%p
    def f(self,a):
        return a.v if isinstance(a, Split) else a%self.p if isinstance(a,int) else Split(a,self.p).v
    def out(self,v):
        o=object.__new__(Split);o.p=self.p;o.v=v%self.p;return o
    def __add__(self,b): return self.out(self.v+self.f(b))
    def __sub__(self,b): return self.out(self.v-self.f(b))
    def __mul__(self,b): return self.out(self.v*self.f(b))
    def __truediv__(self,b): return self.out(self.v*pow(self.f(b),-1,self.p))
    def __rsub__(self,b): return self.out(self.f(b)-self.v)
    def __rtruediv__(self,b): return self.out(self.f(b)*pow(self.v,-1,self.p))
    def __pow__(self,k): return self.out(pow(self.v,k,self.p))
    def __bool__(self): return self.v!=0
    def __neg__(self): return self.out(-self.v)
    def __eq__(self,b): return self.v==self.f(b)
    def __hash__(self): return hash(self.v)
    def __repr__(self): return str(self.v)
    __radd__=__add__
    __rmul__=__mul__

def mul(V,W):
    out=[0]*(len(V)+len(W)-1)
    for i,a in enumerate(V):
        for j,b in enumerate(W):
            out[i+j]+=a*b
    return out
def product(seq):
    return reduce(operator.mul,seq,1)
def hull(nodes):
    return reduce(mul,([-v,1] for v in nodes),[1])
def scale(f,a):
    return [a*v for v in f]
def val(f,v):
    return reduce(lambda hi,lo:v*hi+lo,reversed(f),0)
def integ(f,v):
    z=0
    for i,a in enumerate(f,1):
        z+=a*v**i/i
    return z
def interp(nodes):
    return [scale(hull([v for j,v in enumerate(nodes) if j!=i]),
                  1/product(u-v for j,v in enumerate(nodes) if j!=i))
             for i,u in enumerate(nodes)]
def quad(nodes,v):
    return [integ(f,v) for f in interp(nodes)]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def matrix_vec(M,v):return [dot(r,v) for r in M]
def solve(M,b, one):
    # All casts stay in the chosen ring. Divisions apply only to a nonzero pivot.
    n=len(b); assert len(M)==n and all(len(r)==n for r in M)
    T=[list(r)+[z] for r,z in zip(M,b)]
    for j in range(n):
        i=next((i for i in range(j,n) if T[i][j]),None)
        if i is None: raise ValueError("singular solve")
        T[i],T[j]=T[j],T[i]; t=one/T[j][j]
        T[j]=[z*t for z in T[j]]
        for i in range(n):
            if i!=j and T[i][j]:
                k=T[i][j];T[i]=[a-k*c for a,c in zip(T[i],T[j])]
    return [r[-1] for r in T]
def add(a,b):return [u+v for u,v in zip(a,b)]
def diff(a,b):return [u-v for u,v in zip(a,b)]

H=[0,1,-14,56,-84,42]
def construct(a,c,tail_perm,early_perm=(0,1,2),inner=None,prime=None,words=False):
    F=(lambda z: Split(z,prime)) if prime else Q
    zero,one=F(0),F(1)
    a,c=F(a),F(c)
    b=(3*c*c-2)/(6*c*c-3)
    early=[(one+a)/2,(one-a)/2,(one+b)/2]
    tail=[one/2,(one-b)/2,(one+c)/2,(one-c)/2]
    early=[early[i] for i in early_perm]
    e,r,q,u=[tail[i] for i in tail_perm]
    x=[one]+early+[e,r,q,u]
    if len(set([zero]+x))!=9:
        raise ValueError("colliding scalar nodes")
    hq,hu,hr=[val(H,v) for v in (q,u,r)]
    if not (hu and hr): raise ValueError("no live h on required port")
    def causal(p):
        poly=hull([zero,u,p,q])
        return hu*integ(poly,q)-hq*integ(poly,u)
    p=-causal(zero)/(causal(one)-causal(zero))
    ai=u/2
    opts=[inner] if inner is not None else [Q(1,k) for k in (7,8,9,10,12,13,14,15,16,18,20,21,22,23,25,26,27,31,32,33)]+[Q(2)]
    d=next((F(d) for d in opts if F(d)!=0 and F(d)!=ai),None)
    if d is None or len(set([zero,ai,u,p,q,r]))!=6: raise ValueError("singular forward grid")
    cc=[zero,d,ai,u,p,q,r]
    A=[[zero]*7 for _ in range(7)]
    for i,idx in [(1,[0,1]),(2,[0,1,2]),(3,[0,2,3]),(4,[0,2,3,4])]:
        for j,v in zip(idx,quad([cc[j] for j in idx],cc[i])):
            A[i][j]=v
    ix=[0,3,4,5,6]
    P=[[] for _ in range(7)]
    for j,f in zip(ix,interp([cc[i] for i in ix])):P[j]=f
    Jrow=lambda v:[integ(f,v) for f in P]
    Erow=lambda v:[val(f,v) for f in P]
    sig=[v/hu for v in diff(A[3],Jrow(u))]
    A[5]=add(Jrow(q),scale(sig,hq))
    A[6]=add(Jrow(r),scale(sig,hr))
    assert not A[5][6]
    assert all(sum(row)==cc[i] for i,row in enumerate(A))
    # Half-order reverse word payment, identical space as in the original 12 fixture.
    w0,*w=quad([zero]+x,one)
    if not all([w0]+w): raise ValueError("unusable scalar weight")
    eta=[val(H,z) for z in x]
    eta[0]-=integ(H,one)/w[0]
    y=[1-z for z in x]
    g=[zero]+[1/(wi*xi*product(xi-xj for j,xj in enumerate(x) if j and j!=i))
               for i,(wi,xi) in enumerate(zip(w,x)) if i]
    g=scale(g,y[1]**3/(6*g[1]))
    assert all(not dot(w,[gi*xi**k for gi,xi in zip(g,x)]) for k in range(1,7))
    L=[[zero]*8 for _ in range(8)]
    L[1][:2]=[y[1]/2]*2
    yk=[[z**k for z in y] for k in range(5)]
    for i in range(2,8):
        L[i][:3]=solve([v[:3] for v in yk[:3]],[y[i],y[i]**2/2,y[i]**3/3+g[i]],one)
    test=lambda f,v:dot(w,[val(f,z)*vi for z,vi in zip(x,v)])
    hh=lambda: diff(matrix_vec(L,yk[3]),scale(yk[4],one/4))
    kk=lambda: matrix_vec(L,g)
    f0=hull([zero,u,q,r])
    fstar=mul(f0,[-e,one])
    delta=-test(fstar,hh())/(w[3]*val(fstar,x[3]))
    L[3][:4]=add(L[3][:4],solve([v[:4] for v in yk[:4]],[zero,zero,zero,delta],one))
    if test(fstar,hh()) or test(fstar,kk()): raise ValueError("mixed scalar compatibility failed")
    testM=[[w[i]*val(f,x[i]) for i in (4,5)] for f in (f0,H)]
    changes=list(zip(*(solve(testM,[-test(f,z) for f in (f0,H)],one) for z in (hh(),kk()))))
    for i,(ch,ck) in enumerate(changes,4):
        M=[v[:5] for v in yk[:4]+[g]]
        L[i][:5]=add(L[i][:5],solve(M,[zero,zero,zero,ch,ck],one))
    assert all(not test(f,v) for f in (fstar,f0,H) for v in (hh(),kk()))
    if words:
        W=[[one]*8]
        for grade in range(5):
            assert all(not dot(w,[a*b for a,b in zip(eta,v)]) for v in W)
            W=[z for v in W for z in (matrix_vec(L,v),[a*b for a,b in zip(y,v)])]
    T=[[w[7-j]*L[7-j][7-i]/w[7-i] if j<=i else zero for j in range(8)] for i in range(8)]
    AA=[row+[zero]*8 for row in A]
    xf=x[::-1]
    for i,clock in enumerate(xf):
        row=add(Jrow(clock), scale(sig, eta[7-i]))
        for j,tap in enumerate(T[i]):
            if tap: row=diff(row,scale(Erow(xf[j]),tap))
        AA.append(row+T[i])
    bw=[w0]+[zero]*6+w[::-1]
    assert all(AA[new]==AA[old] for old,new in ((3,7),(5,8),(6,9)))
    keep=tuple(i for i in range(15) if i not in (7,8,9))
    for old,new in ((3,7),(5,8),(6,9)):
        for row in AA: row[old]+=row[new]
        bw[old]+=bw[new]
    mat=[[AA[i][j] for j in keep[:k+1]] for k,i in enumerate(keep)]
    assert all(not AA[i][j] for k,i in enumerate(keep) for j in keep[k+1:])
    bv=[bw[i] for i in keep]
    clocks=cc+xf[3:]
    assert list(map(sum,mat))==clocks
    return mat,bv,clocks

def denominator(A,b):
    return lcm(*(a.denominator for r in A for a in r),*(v.denominator for v in b))

def scout(prime,max_results=5):
    hits=[]
    reasons={}
    for c in range(2,(prime+1)//2):
        for a in range(2,prime-1):
            if a in (c,prime-c):continue
            for tail in permutations(range(4)):
                try:
                    out=construct(a,c,tail,prime=prime)
                except (ZeroDivisionError,ValueError) as err:
                    key=str(err); reasons[key]=reasons.get(key,0)+1;continue
                A,b,x=out
                bush=11*dot(b,[v**10 for v in x])-1
                print("modular chart",prime,"a,c",a,c,"tail",tail,"bush",bush)
                hits.append((a,c,tail))
                if len(hits)>=max_results:return hits
    print("no further modular charts",prime,reasons)
    return hits

PARAMETERS={
    "base": (Q(1,3),Q(1,2),(0,3,2,1)),
    "alternate": (Q(1,2),Q(1,4),(2,3,1,0)),
}

def literal(which):
    A,b,x=construct(*PARAMETERS[which],inner=Q(1,7),words=True)
    delta=dot(b,[v**10 for v in x])-Q(1,11)
    return dict(schema="rational-lower-triangular-runge-kutta-tableau-v1",stages=12,order=10,
      A=[[str(a) for a in row] for row in A],b=[str(v) for v in b],c=[str(v) for v in x],
      eleventh_bush_defect=str(delta))

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--scout",type=int,nargs="+",help="optional prime-field chart search")
    p.add_argument("--which",choices=PARAMETERS,default="alternate")
    p.add_argument("--emit",help="output literal JSON here")
    args=p.parse_args()
    if args.scout:
        for p in args.scout:scout(p)
    if args.emit:
        from pathlib import Path
        t=literal(args.which)
        A,b=[[Q(z) for z in row] for row in t["A"]],list(map(Q,t["b"]))
        Path(args.emit).write_text(json.dumps(t,indent=2)+"\n")
        print(args.which, "three complete row merges and 31 reflected word tests passed")
        print("literal denominator",denominator(A,b))
        print("eleventh-bush raw defect",t["eleventh_bush_defect"])
