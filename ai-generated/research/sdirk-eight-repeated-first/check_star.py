from star_model import *
from rational_field import E,poly_eval,poly_gcd,divmod_coeff
from collections import Counter

def flp(p):
    return fmpq_poly([fmpq(str(c)) for c in p.to_dense()[::-1]])

from sympy.polys.fields import field as fld
from sympy.polys.rings import ring as rng
KK,mm=fld('m',QQ)
def ev0(q,M):
    return poly_eval([E(a) for a in flp(q).coeffs()],M,E)
def maps(z,M,V):
    def zf(ff):
        return sum((E(c)*M**i*V**j for (i,j),c in ff.items()),start=E(0))
    return zf(z.numer)/zf(z.denom)

def proceed(M,V,e):
    if M==0 or V in (0,1,2):return 'invalid m, reverse gap or residual'

    read=lambda f:maps(f,M,V)
    sp_r=read(sp)
    if not sp_r:return 'singular left subtraction (separate proof)'
    H=read(globals()['H'])
    if not H:return 'zero terminal residual'
    Bp=read(globals()['B'])
    if not Bp:return 'bad quartic leading coefficient'
    d=read(g4)
    if not d or d==E(1)/2:return 'fourth residual is zero or unchanged'
    c0=1-M
    if (M-1)==c0 or (c0-(M-2))**2==V:
        return 'an additional corner is forced to the exhausted vertical clock'
    h=E(1)/2
    L0=[E(0),-3*M*M/5,E(0),E(1)]
    a4=[3*M**4/35,E(0),-6*M*M/7,E(0),E(1)]
    bb=3-M;tu=1-M
    n=3*M*M/5
    ra=[[read(z) for z in q] for q in [r1,r2,r3]]
    piv=None
    for i in range(1,3):
        for j in range(i):
            D=ra[i][0]*ra[j][1]-ra[i][1]*ra[j][0]
            if D:
                L=(ra[i][2]*ra[j][1]-ra[j][2]*ra[i][1])/D
                C=(ra[i][0]*ra[j][2]-ra[j][0]*ra[i][2])/D
                assert all(a*L+b*C==c for a,b,c in ra)
                piv=(L,C)
                break
        if piv:break
    assert piv is not None
    Lam,C1=piv
    c0=read(C0)-C1*tu
    up=[read(s0)-Bp*h,read(s1),read(s2)]
    pp=[-bb**3+4*bb,3*bb**2-4,-3*bb,E(1)]
    vp=[(L0[j]-Lam*pp[j])*2-(E(1)/2)*([c0,C1,E(0),E(0)][j]) for j in range(4)]
    Fc=[c0,C1]
    if vp[3]==0 and C1==0:return 'V loses total degree five'
    if C1:
        q=-vp[3]/C1
        if 1-up[2]*q-Bp*q*q==0:return 'common weighted point at infinity'
    def mul(x,y):
        xx=[E(0)]*(len(x)+len(y)-1)
        for j,b in enumerate(x):
            for i,a in enumerate(y):xx[i+j]=xx[i+j]+a*b
        return xx
    def polyadd(x,y):
        q=[(x[i] if i<len(x) else E(0))+(y[i] if i<len(y) else E(0)) for i in range(max(len(x),len(y)))]
        while q and not q[-1]:q.pop()
        return q
    def polsub(x,y):return polyadd(x,[-t for t in y])
    d0=polsub([Bp*d for d in vp],mul(Fc,up))
    q0=polsub([Bp*d for d in L0],mul(Fc,a4))
    assert poly_eval(d0,tu,E)==poly_eval(q0,tu,E)==0
    d0,rem=divmod_coeff(d0,[-tu,E(1)]);assert not rem
    q0,rem=divmod_coeff(q0,[-tu,E(1)]);assert not rem
    assert len(poly_gcd(d0,q0))==1
    U=polsub(polsub(mul(a4,mul(d0,d0)),mul(up,mul(q0,d0))),[Bp*z for z in mul(q0,q0)])
    assert len(U)==9
    assert poly_eval(U,tu,E)!=0
    # Literal nonvertical physical choices: no earlier/reverse pair at t=t0.
    known=mul(mul(mul([-bb,E(1)],[-(bb+2),E(1)]),[-(M-1),E(1)]),[(M-2)**2-V,-2*(M-2),E(1)])
    remset=poly_gcd(known,[-tu,E(1)])
    assert len(remset)==1
    def deriv(x):return [i*z for i,z in enumerate(x) if i]
    if len(poly_gcd(known,deriv(known)))>1:return 'nonvertical corner collision'
    o,rem=divmod_coeff(U,known);assert not rem
    assert len(o)==4
    assert len(poly_gcd(o,d0))==1
    # Reflected fourth row in the right star. The normalized reflected clock is M-t.
    xx=[M,-E(1)]
    x2=mul(xx,xx);x3=mul(x2,xx)
    Nr=polyadd(polyadd(x3,[-9*z for z in x2]),[18*M-6,-E(18)])
    k=2-V
    Nr=[k*z for z in Nr]
    Dr=[2*(4*k-(k+4)*(M-1)),2*(k+4)]
    required=polsub(mul(Dr,q0),[2*H*z for z in mul(Nr,d0)])
    k0=poly_gcd(o,required)
    assert len(k0)==1
    return 'no actual reverse-fourth clock'

if __name__=='__main__':
    seen=[];counts=Counter()
    for f1 in fs:
        zf=KK(s.Poly(f1,s.Symbol('v')).coeff_monomial(1))
        wf=KK(s.Poly(f1,s.Symbol('v')).coeff_monomial(s.Symbol('v')))
        for g1 in gs:
            re=s.resultant(f1,g1,s.Symbol('v'))
            z=fmpq_poly([fmpq(str(c)) for c in s.Poly(re,s.Symbol('m')).all_coeffs()[::-1]])
            for p,e in z.factor()[1]:
                if (f1,str(p)) in seen:continue
                seen.append((f1,str(p)));E.P=p
                M=E([0,1])
                assert ev0(wf.numer,M)!=0
                V=-ev0(zf.numer,M)/ev0(wf.numer,M)
                assert maps(K(f1),M,V)==0
                ans=proceed(M,V,p.degree())
                counts[ans]+=1
                print('M factor degree',p.degree(),'constant term',p[0],ans)
    assert sum(counts.values())==15
    assert counts['no actual reverse-fourth clock']==1
    print(dict(counts))
