#!/usr/bin/env python3
from arith_model import *
import json
from flint import fq_default_ctx, fq_default_poly_ctx, nmod_poly,fmpz_mod_poly_ctx
from pathlib import Path

store=json.loads(Path(__file__).with_name('resultant_factors.json').read_text())
sels=[(a,b,cs) for a,b,ls in store for cs,e in ls if len(cs)-1==172]
assert len(sels)==1
indexF,indexG,coeffs=sels[0]
Ftop=K(fs[indexF]).numer;Gtop=K(gs[indexG]).numer
componentDegree=172;fdeg=15;gdeg=27
class Bad(Exception):pass

def reffail(b,diag):
    if not b:raise Bad(diag)

def check_case(m0,u0,E,R):
    t=R.gen();one=E.one()
    def fail(b,ss):
        if not b:raise Bad(ss)
    def ce(c):
        return E(int(c.numerator))/E(int(c.denominator))
    mp=[m0**i for i in range(32)]
    up=[u0**i for i in range(64)]
    def ev0(x):
        return sum((ce(c)*mp[i]*up[j] for (i,j),c in x.items()),start=E.zero())
    def ev(x):
        return ev0(x.numer)/ev0(x.denom)
    scalars=[m,u,k,q,rt,ht,delta,H,B,g4,g4-h,C0]
    a,b,k0,q0,r0,hh,dd,H0,B0,g40,_,c0=[ev(t0) for t0 in scalars]
    fail(all(x0!=0 for x0 in [a,b,k0,q0,r0,hh,dd,H0,B0,g40,g40-one/2]),'parameter guard')
    rows=[[ev(w) for w in rr] for rr in (r1,r2,r3)]
    piv=None
    for i in range(1,3):
        for j in range(i):
            x,y,z=rows[i];a1,b1,c1=rows[j]
            D=x*b1-y*a1
            if D!=0:
                l=(z*b1-y*c1)/D;e=(x*c1-z*a1)/D
                fail(all(x*l+y*e==z for x,y,z in rows),'inconsistent V scalar pair')
                piv=(l,e)
                break
        if piv:break
    fail(piv is not None,'singular V scalar pivot')
    l,e=piv
    t0=1-a;b0=3-a
    x1=a-1;x2=x1-b;x3=x1-2*b
    known=[b0,b0+2,x1,x2,x3]
    fail(all(x!=t0 and all(x!=y for y in known[:i]) for i,x in enumerate(known)),'clock collisions')
    u4=t**4-6*a*a/7*t*t+3*a**4/35
    v3=t**3-3*a*a/5*t
    P3=(t-b0)*((t-b0)**2-4)
    A=ev(s0)-B0/2+ev(s1)*t+ev(s2)*t*t
    F=c0+e*(t-t0)
    D=2*(v3-l*P3)-F/2
    W=B0*D-F*A;Q=B0*v3-F*u4
    WW,R0=divmod(W,t-t0);QQ,R1=divmod(Q,t-t0)
    fail(not R0 and not R1,'nonliteral first vertical')
    fail(WW.gcd(QQ).degree()==0,'another vertical')
    N=u4*WW**2-A*QQ*WW-B0*QQ**2
    fail(N.degree()==8 and N(t0)!=0,'clock projection grade')
    Known=R.one()
    for x in known:Known*=t-x
    cubic,Rem=divmod(N,Known)
    fail(cubic.degree()==3 and not Rem and cubic.gcd(WW).degree()==0,'middle cubic')
    # Actual normalized reflected fourth from the three early reverse profiles.
    y=a-t
    s=(k0-1)/(2*b);r=(q0-1)/(4*b)
    T2=(r-s)/b;T1=s-T2*(2+b);T0=one/2-T1-T2
    v0=-T0-T1*y-T2*y*y+T0*y+T1*y*y/2+T2*y**3/3
    v1=1-(1+(y-1)/k0)+T1+T2*(4*one/3+2*(k0+1)*(y-1)/(3*k0))
    gg=2*H0*WW*v0+QQ*v1
    G=cubic.gcd(gg)
    fail(G.degree()==0,'reduced chronology has candidate')

def check(p):
    Li=nmod_poly([int(fmpq(x).numerator)*pow(int(fmpq(x).denominator),-1,p)%p for x in coeffs],p)
    reffail(Li.degree()==componentDegree,'projection degree')
    ff=Li.factor()[1]
    reffail(all(e==1 for a,e in ff),'inseparable m reduction')
    out=[]
    for z,_ in ff:
        if z.degree()==1:
            F=fq_default_ctx(p);a=F(-int(z[0])*pow(int(z[1]),-1,p)%p)
        else:
            F=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)(list(map(int,z.coeffs()))))
            a=F.gen()
        R=fq_default_poly_ctx(F);u=R.gen()
        A=[a**i for i in range(32)]
        def evM(pp):
            v=R.zero()
            for (i,j),c in pp.items():
                v+=A[i]*(F(int(c.numerator))/F(int(c.denominator)))*u**j
            return v
        f,g=evM(Ftop),evM(Gtop)
        reffail(f.degree()==fdeg and g.degree()==gdeg,'a projective infinity pivot')
        U=f.gcd(g)
        if U.degree()==0:continue
        reffail(U.degree()==1,'gap is not simple linear')
        gap=-U[0]/U[1]
        check_case(a,gap,F,R)
        out.append(z.degree())
    return sorted(out)


if __name__=='__main__':
    assert check(43)==[2,3,5,60,102]
    print('modulo 43 all five residue components of the dominant degree-172 factor exclude the reflected fourth')
