"""Replay the actual p and p^2 literals and unit pivots for archived q9 seeds."""
from pathlib import Path
from functools import cache
from math import prod, isqrt
import importlib.util,json,sys

base=Path(sys.argv[1])
source=Path(sys.argv[2])
out=Path(sys.argv[3])
def load(name):
    spec=importlib.util.spec_from_file_location(name,base/'erk10-fifteen-17-power'/f'{name}.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
C=load('chart')
G=load('geometry')

@cache
def grade(t): return 1+sum(map(grade,t))
@cache
def forests(n,t):
    if n==0:return ((),)
    return tuple((j,)+u for k in range(grade(t),n+1) for j in trees(k)
                 if k>grade(t) or j>=t for u in forests(n-k,j))
@cache
def trees(n):return forests(n-1,())
@cache
def density(t):return grade(t)*prod(map(density,t))

def independent(mod,A,b):
    assert len(A)==len(b)==15
    assert all(len(r)==i and all(0<=a<mod for a in r) for i,r in enumerate(A))
    assert all(0<=w<mod for w in b)
    @cache
    def phi(t):
        a=(read(u)for u in t)
        y=[1]*15
        for row in a:
            y=[u*v%mod for u,v in zip(y,row)]
        return y
    @cache
    def read(t):
        x=phi(t)
        return [sum(a*z for a,z in zip(row,x))%mod for row in A]
    for n,c in enumerate((1,1,2,4,9,20,48,115,286,719),1):
        assert len(trees(n))==c
        for t in trees(n):
            assert density(t)*sum(w*z for w,z in zip(b,phi(t)))%mod==1
    return (11*sum(w*z for w,z in zip(b,phi(((),)*10)))-1)%mod

class Local(C.F):
    def __init__(self,p,m):self.base,self.p=p,m
    def inv(self,x):
        assert x%self.base
        return pow(x,-1,self.p)
    def integ(self,q):
        return sum(x*self.inv(i+1) for i,x in enumerate(q))%self.p
    def solve(self,A,b,n=None):
        m,p=self.p,self.base
        M=[[z%m for z in row]+[y%m] for row,y in zip(A,b)]
        n=n or len(M[0])-1
        piv=[]
        for j in range(n):
            i=len(piv)
            k=next((k for k in range(i,len(M)) if M[k][j]%p),None)
            if k is None:continue
            piv.append(j);M[i],M[k]=M[k],M[i]
            M[i]=self.scale(self.inv(M[i][j]),M[i])
            for k in range(i+1,len(M)):
                a=M[k][j]
                if a:
                    M[k][j:]=[(x-a*y)%m for x,y in zip(M[k][j:],M[i][j:])]
        if any(row[-1] for row in M[len(piv):]):return None
        y=[0]*n
        for j,row in reversed(list(zip(piv,M))):
            y[j]=(row[-1]-self.dot(row[:-1],y))%m
        assert all(self.dot(r,y)==v%m for r,v in zip(A,b))
        return y,len(piv)

def reconstruct(T,F,s,q):
    a,c,d,e,f,g=T;m=F.p;p=F.base;I=F.inv
    b=2*a%m
    eq,(mu,donor,*_)=G.system(T,m,True)
    assert not any(eq) and donor%p
    W={z:mu[z]*I(prod(z-u for u in mu if z!=u))%m for z in mu}
    assert len(W)==9 and all(v%p for v in W.values())
    ch=C.Chart(a,b,c,(d,e,f,g),W,mu,F)
    L=ch.terminal((d,e,f,g))
    assert L is not None and (ch.h[4]-ch.h[3])%p
    ys=ch.y+[d,e,f,g]
    xs=[(1-y)%m for y in reversed(ys)]
    ws=list(reversed(ch.w+[W[z] for z in (d,e,f,g)]))
    B=[[ws[j]*L[9-j][9-i]*I(ws[i])%m for j in range(i)] for i in range(10)]
    forms=[[(F.dot(B[i],[pow(z,k,m) for z in xs])-pow(t,k+1,m)*I(k+1))%m
            for k in (1,2,3)] for i,t in enumerate(xs)]
    v,u=F.solveUni([r[:2] for r in forms[:2]],[-r[2] for r in forms[:2]])
    assert all(F.dot(r,[v,u,1])==0 for r in forms)
    P=lambda x:(x**3+u*x*x+v*x)%m
    rough=1
    sl=s*s*I(2*rough)%m
    newp=s*v*I(3*s*s+2*s*u+2*v)%m
    al=newp*newp*(3*s-2*newp)*I(s**3)%m
    be=P(q)*I(P(s))%m
    js=(newp*newp-al*s*s)*I(2*s)%m
    B1=(q*q*I(2)-be*sl*rough)%m
    B2=(q**3*I(3)-be*sl*2*rough*s*I(3))%m
    qs=(newp*B1-B2)*I(s*(newp-s))%m
    qp=(B2-s*B1)*I(newp*(newp-s))%m
    A=[[],[rough],[(s-sl)%m,sl],[(newp-al*sl-js)%m,al*sl%m,js],
       [(q-be*sl-qs-qp)%m,be*sl%m,qs,qp]]
    Q=[[1,0,0],[1-al,newp-al*s,newp*newp-al*s*s],[1-be,q-be*s,q*q-be*s*s]]
    rows=[[1,0,0],[0,0,0],[0,-al,-be],[0,1,0],[0,0,1]]
    Pi=[F.solveUni(Q,z) for z in rows]
    for i,x in enumerate(xs):
        r=[(x**(k+1)*I(k+1)-F.dot(B[i],[pow(z,k,m)for z in xs]))%m for k in range(3)]
        A.append([F.dot(t,r) for t in Pi]+B[i])
    # The following observer matrix detects the full cubic-kernel residual.
    xR=list(reversed(xs));wR=list(reversed(ws));hR=ch.h+[ch.hu[z] for z in (d,e,f,g)]
    uR=ch.u+[0]*4
    Obs=[[wt*pow(x,j,m)%m for x,wt in zip(xR,wR)]for j in range(5)]
    Obs += [[wt*x%m for wt,x in zip(wR,row)] for row in (uR,hR,[y*h for y,h in zip(ys,hR)])]
    Obs += [[int(i==j) for i in range(10)] for j in (9,8)]
    F.solveUni(Obs,[0]*10)
    return A,[W[1],0,0,0,0]+ws

lifts=[]
items=json.loads(source.read_text())
for rec in items:
    p=rec['p'];m=p*p;T=rec['geometry'];_,rough,s,pp,q=rec['low_clocks']
    assert p>11 and all(p%q for q in range(2,isqrt(p)+1)) and rough==1
    assert independent(p,rec['A'],rec['b'])==rec['defect']!=0
    assert (reconstruct(T,Local(p,p),s,q))==(rec['A'],rec['b'])
    res=G.system(T,m)
    assert all(v%p==0 for v in res)
    M=[[r[j] for j in (0,1,3,4,5)] for r in G.jac(T,p)]
    digit=Local(p,p).solveUni(M,[-v//p for v in res])
    TT=[x+p*k for x,k in zip(T,digit[:2]+[0]+digit[2:])]
    assert G.system(TT,m)==[0]*5
    A,b=reconstruct(TT,Local(p,m),s,q)
    assert [[x%p for x in row]for row in A]==rec['A'] and [x%p for x in b]==rec['b']
    def2=independent(m,A,b)
    assert def2%p==rec['defect']
    lifts.append({'p':p,'geometry':TT,'A':A,'b':b,'defect':def2})
    print(f'{p}: all rooted conditions and unit defect {rec["defect"]}/{def2} at p and p^2',flush=True)
out.write_text(json.dumps(lifts,indent=2)+'\n')
print(f'{len(items)*2} literal rooted-order replays passed; unit Hensel and reconstruction guards at each')
