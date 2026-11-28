"""Exact degree-24 ordinary field, then genuinely paid commutator and zero-d_B certificates."""
import argparse
from pathlib import Path
from fractions import Fraction
from math import comb
from runpy import run_path
import sympy as S
A=run_path(str(Path(__file__).with_name('ordinary.py')))
Y,V,B=A['Y'],A['V'],A['B']
J4,J5=A['J4'],A['J5']
J4cs=[1,-14,56,-84,42]
def rat(a):
    t=S.Rational(a);return Fraction(int(t.p),int(t.q))
def ev(cs,x):
    ans=x.r.to(0)
    for c in reversed(cs):ans=ans*x+c
    return ans
def mul(f,g):
    c=[f[0].r.to(0)]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):c[i+j]+=a*b
    return c
def plus(f,g):
    if len(f)<len(g):return plus(g,f)
    return [*(a+b for a,b in zip(f,g)),*f[len(g):]]
def scale(f,d):return [x*d for x in f]
def prim(f):return [f[0].r.to(0),*(a/(i+1)for i,a in enumerate(f))]
def refl(f):return [(-1)**i*sum(comb(j,i)*f[j]for j in range(i,len(f)))for i in range(len(f))]
def pc(f,x):
    return ev([rat(a)for a in reversed(S.Poly(f,V).all_coeffs())],x)
def rem(f,g):
    r=f[0].r;n=len(g)-1;f=list(f)
    assert g[-1]==1
    for i in range(len(f)-1,n-1,-1):
        for j in range(n):f[i-n+j]-=f[i]*g[j]
    return f[:n]+[r.to(0)]*max(0,n-len(f))
def main(args):
    G,seq,fs=A['projection']()
    assert sorted((f.degree(),e)for f,e in fs)==[(4,2),(4,9),(8,1),(24,1)]
    f24=next(f for f,e in fs if f.degree()==24).monic()
    G1=S.Poly(seq[-2],B)
    assert G1.degree()==1
    for d,e,form in [(4,9,J4(V)),(4,2,(J5(V)-J4(V))/(2*(V-1))),
                     (8,1,(S.diff(J5(V),V)*J4(V)-J5(V)*S.diff(J4(V),V))/2)]:
        assert next(f for f,k in fs if f.degree()==d and k==e).monic()==S.Poly(S.cancel(form),V).monic()
    lib=run_path(str(args.research/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    Ring,quot,det=(lib[n]for n in ('Ring','quot','det'))
    p=args.prime
    assert S.isprime(p) and p>11
    F=Ring('prime',prime=p)
    K=Ring('ordinary V',F,[F.to(rat(f24.nth(i)))for i in range(24)])
    v=K.gen();o,z=(K.to(i)for i in (1,0))
    def coeff(poly):
        return [pc(poly.nth(i),v)for i in range(poly.degree()+1)]
    bb=-pc(G1.nth(0),v)/pc(G1.nth(1),v)
    assert ev(coeff(A['F']),bb)==0 and ev(coeff(G),bb)==0
    a,b=o-v,o-bb
    lam=-J5(v)/J4(v)
    tf=[(K.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    R3=quot(quot(tf,v),bb)
    assert mul([-v,o],mul([-bb,o],R3))==tf
    c0,c1,c2,_=R3
    L0=prim([z,*R3])[1:]
    L1=prim([z,z,*R3])[1:]
    J=[K.to(i)for i in J4cs]
    j,l0,yl0,l1=(rem(k,R3)for k in (J,L0,[z,*L0],L1))
    d3=lambda *c:det(list(zip(*c)))
    # A and D are the two coefficients of the affine Q5/W0, i.e.
    # L1 - V L0 = theta J4 + A L0 + D YL0 on the old sites.
    N=plus(l1,scale(l0,-v))
    live3=d3(j,l0,yl0)
    th=d3(N,l0,yl0)/live3
    a0=d3(j,N,yl0)/live3
    a1=d3(j,l0,N)/live3
    xx=-a0/a1
    assert ev(L1,v)-v*ev(L0,v)-th*J4(v)==(a0+a1*v)*ev(L0,v)
    # Extra three-late actual commutator gate from pure old+V interpolation.
    RV=mul([-v,o],R3)
    CR=mul([-xx,o],L0)
    Cdet=d3(*(rem(q,RV)for q in (J,[z,*J],CR,[z,*CR])))
    Cdet.inv()
    print('pure ordinary commutator determinant unit in full degree24 residue algebra',p,flush=True)
    vv=ev(L0,v)
    vv.inv()
    c1.inv(); c2.inv()
    contact=12*c0*c0+8*c0*c1*c2-6*c0*c2**3+c1*c1*c2*c2
    contact.inv()
    print('c1, c2 and mixed c2s=c0 contact are all units on exact degree24 ordinary algebra',p,flush=True)
    Fn=[-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2]
    def first_b(Ur,B):
        # Direct forward primitive and independent reverse-endpoint primitive.
        r=Ur[0].r; oo,zz=r.to(1),r.to(0)
        Jb=ev(prim([zz,*refl(Ur)]),oo-B)
        Qr=prim(mul([oo,-oo],Ur))
        assert Jb==ev(Qr,oo)-ev(Qr,B)
        return Jb
    J0=first_b(R3,bb)
    def direct():
        # Fn regular leader and ratio are not divided without unit checks.
        fn=Fn[-1].inv()
        T=Ring('profile s',K,[r*fn for r in Fn[:-1]])
        ss=T.gen()
        cs0,cs1,cs2,vs,bs,vvT,J0T=(T.to(c)for c in (c0,c1,c2,v,b,vv,J0))
        rr=6*cs2*ss/(cs1+6*ss)
        rr3=list(map(T.to,R3))
        old=Ring('old clocks',T,rr3[:-1]);y=old.gen()
        m=y*y+old.to(rr)*y+old.to(ss)
        M=(J4(y)/m).v
        W=(ev([old.to(c)for c in L0],y)/m).v
        Q=plus(mul(list(map(T.to,L0)),M),scale(mul(W,list(map(T.to,J))),-T.to(1)))
        # (L0 M - W J4) / R, strict exact monic division.
        D=[T.to(0)]*(len(Q)-3)
        for i in range(len(Q)-1,2,-1):
            q=Q[i];D[i-3]=q
            for j in range(3):Q[i-3+j]-=q*rr3[j]
        assert Q[:3]==[0,0,0]
        JMb=first_b(M,T.to(bb))
        test=vvT*JMb-ev(D,vs)*J0T
        t=-ev(D,vs)/vvT
        assert test==vvT*first_b(plus(M,scale(rr3,t)),T.to(bb))
        test.inv()
        print('F_n direct: forced zero forward J(b) has a unit eliminant in full rank72',p,flush=True)
    def singular():
        # Restore unscaled A1 directly from the symbolic old census,
        # not from any earlier projected coefficient file.
        old=run_path(str(args.research/'dirk11-thirteen-invisible-six-early-profile-census/project.py'))
        p0,p1,p2,sym_s=(old[x]for x in ('c0','c1','c2','s'))
        terms=S.Poly(S.cancel(-10*p0*old['A1']),p0,p1,p2,sym_s).terms()
        assert all(S.denom(n)==1 for _,n in terms)
        F1=[-75*c0*c0,75*c0*c2,-80*c1,K.to(96)]
        F2=[-c0*c0,c0*c2,-c1,K.to(1)]
        for name,ff in (('F1',F1),('F2',F2),('Fn',Fn)):
            T=Ring('profile',K,[r/ff[-1]for r in ff[:-1]])
            ss=T.gen(); k0,k1,k2=(T.to(c)for c in (c0,c1,c2))
            a1=sum(rat(n)*k0**i*k1**j*k2**k*ss**h for (i,j,k,h),n in terms)
            a1.inv()
            print(name,'singular pivot forbidden by unit A1 in full rank72',p,flush=True)
    if args.mode in ('direct','all'):direct()
    if args.mode in ('singular','all'):singular()
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--prime',type=int,default=103)
    ap.add_argument('--mode',choices=('pure','direct','singular','all'),default='all')
    main(ap.parse_args())
