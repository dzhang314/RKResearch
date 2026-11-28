#!/usr/bin/env python3
"""Characteristic-zero finite-profile proof using degree-bounded rank.

All ordinary projections are exact. The residue matrices give nonzero minors
of the specified degree-bounded polynomial maps over the exact clock algebra.
"""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import permutations
from types import SimpleNamespace
from math import comb
from flint import nmod_mat
from pathlib import Path
from runpy import run_path
import sympy as S
V,B,Y=S.symbols('V B Y')
def J4(x):return 42*x**4-84*x**3+56*x*x-14*x+1
def J5(x):return 132*x**5-330*x**4+300*x**3-120*x*x+20*x-1
T=S.Poly(J5(Y)*J4(V)-J5(V)*J4(Y),Y).exquo(S.Poly(Y-V,Y))
D=T.LC()
F=S.Poly(T.as_expr().subs(Y,B),B)
C2=T.nth(3)+B*D
C1=T.nth(2)+B*C2
C0=T.nth(1)+B*C1
P2=S.Poly(C2,B);P1=S.Poly(C1,B);Pc0=S.Poly(6*C0*D-5*C1*C2,B)
co,Pc=S.Poly(12*C0*C0*D*D+8*C0*C1*C2*D-6*C0*C2**3+C1*C1*C2*C2,B).prem(F).primitive()
assert S.Poly(co,V).monic()==S.Poly(J4(V)**3,V).monic()
assert Pc.degree()==3

def rat(c):
    t=S.Rational(c);return Fraction(int(t.p),int(t.q))
def ev(f,x):
    out=x.r.to(0)
    for c in reversed(f):out=out*x+c
    return out
def mul(f,g):
    out=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,x in enumerate(f):
        for j,y in enumerate(g):out[i+j]+=x*y
    return out
def add(f,g):
    if len(f)<len(g):return add(g,f)
    return [*(a+b for a,b in zip(f,g)),*f[len(g):]]
def scale(f,h):return [h*x for x in f]
def prim(f):return [f[0].r.to(0),*(a/(i+1)for i,a in enumerate(f))]
def wedge(u,v):return u[0]*v[1]-u[1]*v[0]
def checked(k,res,mod,prime,lib):
    Ring,quot,det=(lib[q]for q in ('Ring','quot','det'))
    Fp=Ring('residue prime',prime=prime)
    base=Ring('ordinary V',Fp,[Fp.to(rat(mod.nth(i)))for i in range(mod.degree())])
    v=base.gen()
    def bz(p):return ev([rat(t)for t in reversed(S.Poly(p,globals()['V']).all_coeffs())],v)
    def cfs(P):return [bz(P.nth(i))for i in range(P.degree()+1)]
    b0=-bz(res.nth(0))/bz(res.nth(1))
    assert ev(cfs(F),b0)==0
    lam=-J5(v)/J4(v)
    T5=[(base.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    rr=quot(quot(T5,v),b0)
    c0,c1,c2,_=rr
    current=base
    if k in ('m1','Fn-loss'):assert c2==0
    if k=='mY2':assert c1==0
    if k=='Fn-loss':
        s=-c1/6
        current=Ring('lost Fn D in r',base,[-3*s,4*s*s/c0])
        r=current.gen();s=current.to(s)
    v,b0=current.to(v),current.to(b0)
    R=list(map(current.to,rr))
    c0,c1,c2,_=R
    o,z=current.to(1),current.to(0)
    old=Ring('cubic old',current,R[:-1])
    y=old.gen()
    if k=='m1':mm=old.to(1)
    elif k=='mY2':mm=y*y
    elif k=='contact':
        assert 12*c0*c0+8*c0*c1*c2-6*c0*c2**3+c1*c1*c2*c2==0
        mm=y*y+old.to((2*c0+c1*c2)/(c2*c2))*y+old.to(c0/c2)
    elif k=='r0':
        assert 6*c0==5*c1*c2
        mm=y*y+old.to(c0/c2)
    else:
        assert k=='Fn-loss'; mm=y*y+old.to(r)*y+old.to(s)
    Sring=current
    V,B,L=v,b0,o
    a,b=L-V,L-B
    c0,c1,c2,_=R
    zero,one=z,o
    R3=list(R);P0=[zero,*R3]
    m=list(mm.v)
    J4p=[current.to(i)for i in (1,-14,56,-84,42)]
    H=[zero,*J4p]
    def rem(f,g):
        S0=f[0].r
        n=len(g)-1
        f=list(f)
        for j in range(len(f)-1,n-1,-1):
            q=f[j]
            if q!=0:
                for i in range(n):f[j-n+i]-=q*g[i]
        return f[:n]+[S0.to(0)]*max(0,n-len(f))
    def cofact(f,x):
        g=quot(f,x)
        assert ev(f,x)==0
        return g
    pplus=add
    pscale=lambda f,b:[x*b for x in f]
    cols=lambda *C:list(zip(*C))
    L0=prim(P0)[1:];L1=prim([zero,*P0])[1:]
    def fit(f):return list((ev([old.to(x)for x in f],y)/mm).v)
    den=one
    M,W0,Q0=map(fit,(J4p,L0,L1))
    args=SimpleNamespace(extras=True)
    # Scalar quartic and quintic exact old quotients in the original gauge.
    def monic_div(f,monic):
        x=list(f)
        n=len(monic)-1
        assert monic[-1]==1
        y=[x[0].r.to(0)]*max(0,len(x)-n)
        for i in range(len(x)-1,n-1,-1):
            y[i-n]=c=x[i]
            for j in range(n):x[i-n+j]-=c*monic[j]
        assert all(g==0 for g in x[:n])
        return y
    d4=monic_div(pplus(mul(L0,M),pscale(mul(W0,J4p),-one)),R3)
    d5=monic_div(pplus(mul(L1,M),pscale(mul(Q0,J4p),-one)),R3)
    P=[zero,*m]
    IP=prim(P); I2P=prim(IP)
    el=fit(IP[1:]); to=fit(I2P[1:])
    u0,u1,u2=m
    if k in ('m1','mY2'):zp,zq=zero,one
    elif k=='r0':zp,zq=-5*c2,4*one
    else:zp=u1*u2*c0; zq=3*u0*u2*c2-4*u0*u1-3*u2*u2*c0

    # Polynomials in the carrier t. Distinguish them from all clock polynomials
    # and use full-size coefficient arc even when the induced t degree drops.
    class TPFactory:
        def to(self,c):return c if isinstance(c,TP) else TP([Sring.to(c)])
        def gen(self):return TP([zero,one])
    T=TPFactory()
    class TP:
        __slots__=('cs',)
        r=T
        def __init__(self,cs):
            cs=list(cs)
            while len(cs)>1 and cs[-1]==0:cs.pop()
            self.cs=tuple(cs)
        def __eq__(self,v):return self.cs==self.r.to(v).cs
        def __add__(self,v):
            v=self.r.to(v)
            return TP(pplus(self.cs,v.cs))
        __radd__=__add__
        def __neg__(self):return TP([-a for a in self.cs])
        def __sub__(self,v):return self+-self.r.to(v)
        def __rsub__(self,v):return self.r.to(v)+-self
        def __mul__(self,v):return TP(mul(self.cs,self.r.to(v).cs))
        __rmul__=__mul__
        def __pow__(self,n):
            assert n>=0
            r=self.r.to(1); a=self
            while n:
                if n&1:r=r*a
                a=a*a;n//=2
            return r
        def scale(self,c):return TP([x*c for x in self.cs])
        def __truediv__(self,d):return self.scale(Fraction(1,d))
        @property
        def degree(self):return -1 if self==0 else len(self.cs)-1

    def listT(f):return list(map(T.to,f))
    def et(a):return T.to(a)
    ts=T.gen()
    o,z=et(1),et(0)
    vr,br,ls,ar,bs=map(et,(V,B,L,a,b))
    Mt,Rt,L0t,L1t,Wt,Qt,J4t,Ht=map(listT,(M,R3,L0,L1,W0,Q0,J4p,H))
    UR=pplus(Mt,pscale(Rt,ts))
    def rev(f):
        return [(-1)**i*sum(comb(j,i)*f[j]*ls**(j-i) for j in range(i,len(f))) for i in range(len(f))]
    UF=rev(UR)
    U_V=ev(UR,vr)
    cv=ev(listT(d4),vr)+ts*ev(L0t,vr)
    jv=ev(J4t,vr)
    hv=vr*jv
    qr,pr=et(zq),et(zp)
    Adj=(pr-vr*qr)*((et(ev(el,V))*hv-et(ev(IP,V))*U_V)*U_V+
                     cv*(et(ev(P,V))*U_V-et(den)*hv)) - qr*(et(ev(I2P,V))*U_V-et(ev(to,V))*hv)*U_V
    ff=prim(mul([z,-bs,o],UF))
    Kf=pplus(pscale(ff,ev(Ht,bs)),pscale(Ht,-ev(ff,bs)))
    KbDiv=cofact(cofact(rev(Kf),ls),br)
    N=mul([-vr,o],Mt)
    Dr=mul([-vr,o],Rt)
    E6=det(cols(UR,N,rem([z,*N],Dr),rem(mul([-pr,qr],KbDiv),Dr)))
    assert Adj.degree<=2 and E6.degree<=2
    gates={'E6':E6,'Adj':Adj}

    if args.extras:
        d5v=ev(listT(d5),vr)+ts*ev(L1t,vr)
        B5=pplus(pscale(pplus(Qt,pscale(Wt,-vr)),jv),
                 pscale(Rt,d5v-vr*cv))
        def hom(f,x,d):return sum(f[i]*x**i*d**(len(f)-1-i)for i in range(len(f)))
        Uh=hom(UR,pr,qr)
        Q5=pplus(pscale(B5,Uh),pscale(UR,-hom(B5,pr,qr)))
        assert all(q.degree<=1 for q in Q5)
        J=prim([z,*UF])
        B2=ev(J,bs)**2*det(cols(Q5,rem([z,*Q5],Dr),UR,N))
        assert B2.degree<=5
        Jdiv=cofact(rev(J),ls)
        DR2=mul([-br,o],Dr)
        M2=mul(mul([-vr,o],[-br,o]),Mt)
        C0=rem(mul([-pr,qr],Jdiv),DR2)
        C1=rem([z,*C0],DR2)
        # These five columns live in degree-at-most-four coefficients.
        WW=[UR+[z],[z,*UR],M2,rem([z,*M2],DR2)]
        g1,g0=(det(cols(*WW,f))for f in (C0,C1))
        assert g1.degree<=3 and g0.degree<=3
        q0,q1,q2,q3=Q5
        dd=[qr*qr*q1+pr*qr*q2+pr*pr*q3,qr*qr*q2+pr*qr*q3,qr*qr*q3]
        B1=hom(dd,g0,g1)
        assert B1.degree<=7
        gates.update(B1=B1,B2=B2,UatV=U_V,UatB=ev(UR,br),UatO=ev(UR,ls),UatZ=Uh)
        # Live reciprocity/cubic contact guards:
        guard_t=ts*U_V*ev(UR,br)*ev(UR,ls)*Uh
        def tighten(e):
            # Exact removal of common t powers at a live cubic leader.
            cc=list(e.cs)
            while len(cc)>1 and cc[0]==0:cc.pop(0)
            return TP(cc)
    else:
        B1=B2=None

    def bas(r):
        if r is Fp:return [Fp.to(1)]
        return [r.to(a)*r.gen()**i for i in range(r.d)for a in bas(r.base)]
    def flat(x):
        if x.r is Fp:return [x.v]
        return sum((flat(j)for j in x.v),[])
    basis=bas(current)
    D=9
    for beta,es in ((1,[(Adj,2),(E6,2),(B1,7)]),(2,[(Adj,2),(E6,2),(B2,5)])):
        columns=[]
        for f,upper in es:
            assert f.degree<=upper
            for j in range(D-upper+1):
                for u in basis:
                    column=[current.to(0)]*j+[c*u for c in f.cs]
                    column += [current.to(0)]*(D+1-len(column))
                    columns.append(sum((flat(c)for c in column),[]))
        rank=nmod_mat(list(map(list,zip(*columns))),prime).rank()
        print('finite',k,'beta',beta,'d',len(basis),'p',prime,
              'Macaulay rank',rank,'/',len(basis)*(D+1),
              'degrees',[f.degree for f,_ in es],flush=True)
        assert rank==len(basis)*(D+1)

def main():
    p=ArgumentParser();p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--branch',choices=('m1','mY2','contact','Fn-loss','r0','all'),default='all')
    args=p.parse_args()
    lib=run_path(str(args.research/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    for name,G,deg,exp in [('m1',P2,12,2),('mY2',P1,12,3),('contact',Pc,48,7),('Fn-loss',P2,12,2),('r0',Pc0,24,5)]:
        if args.branch not in ('all',name):continue
        zz=S.factor_list(S.Poly(S.resultant(F,G,B),V))[1]
        assert sorted((f.degree(),e)for f,e in zz)==[(4,exp),(deg,1)]
        assert next(f for f,e in zz if f.degree()==4).monic()==S.Poly(J4(V),V).monic()
        q=next(f for f,e in zz if f.degree()==deg).monic()
        seq=S.subresultants(F,G,B)
        s1=S.Poly(seq[-2],B)
        assert s1.degree()==1
        checked(name,s1,q,101 if name=='contact' else 103,lib)
if __name__=='__main__':main()
