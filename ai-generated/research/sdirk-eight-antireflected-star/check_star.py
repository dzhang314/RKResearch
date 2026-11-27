#!/usr/bin/env python3
"""Exact exclusion for the nowhere-zero, chronology anti-reflected, star-opening chart."""
from sympy import ring,QQ
from sympy.polys.fields import field
from flint import fmpq,fmpq_poly
from arithmetic import E as Ext,Q,solve,poly_gcd,poly_eval

K,m=field('m',QQ)
R,w=ring('w',K)
S,x=ring('x',K)
vden=2*m**4-20*m**3+80*m**2-140*m+70
vnum=14*m**4-140*m**3+420*m**2-420*m+105
v=-vnum/vden
k=2-v
a0=1-m;b0=2-m
g0=K(1)/2;g1=k/2
n=3*m*m/5
L=w*w-6*m*m*w/7+3*m**4/35
A=(4*b0*(b0*b0+v)-12*m*m*b0/7)/g1
B=(L(a0*a0)/g0-A*a0)/g0
C=(b0*b0-v)+a0*a0-2*b0*g0*a0/g1
Ch=a0*(a0*a0-n)/g0+2*b0*(b0*b0-v)/g1-g0*a0*(3*b0*b0+v-n)/g1**2
E=Ch/C
F=((3*b0*b0+v-n)/g1-2*E*b0)/g1
D=(E-2*b0/g1)*(b0*b0-v)
K0=B*(w-n)-F*L
D0=B*(D+E*w)-F*A*w
VW=(w-n)*D0**2-K0*D0*(D+E*w)-F*w*K0**2
Known=(w-a0*a0)*(w*w-2*(b0*b0+v)*w+(b0*b0-v)**2)
W=VW.exquo(Known).monic()
N4=k*(x**3-9*x*x+18*x-6)
D4=2*(4*k-(k+4)*(x-1))
xc=x-m
U4=(xc**4-6*m*m*xc*xc/7+3*m**4/35)*D4**2-N4*(A*xc*D4+B*N4)
V4=(xc**3-n*xc)*D4**2-N4*((D+E*xc**2)*D4+F*xc*N4)
opening=(x-1)*((x-2)**2-v)
Ured=U4.exquo(opening)
Vred=V4.exquo(opening)
res=Ured.resultant(Vred)

def flp(p):
    return fmpq_poly([fmpq(str(c)) for c in p.to_dense()[::-1]])

def sp(z):
    return Ext(flp(z.numer))/Ext(flp(z.denom))

def spel(poly):
    a=[sp(poly.get((j,),K.zero)) for j in range(poly.degree()+1)]
    while a and not a[-1]:
        a.pop()
    return a

def ev(f,x):
    return poly_eval(spel(f),x,Ext)

def factors(z):
    return flp(z.numer).factor()[1]

def e2(x,g):
    return [Q(1),x,x*x,g]

def fifth_exclusion(x4,g4,w5,r5):
    """The two rational-field norms of the pure discrepancies at either fifth sign."""
    M=Ext([0,1]);Q.v=sp(v)
    pts=[(Q(1),Q(1)/2),(Q(2,1),Q(sp(k))/2),(Q(2,-1),Q(sp(k))/2),
         (Q(x4),Q(g4))]
    mat=[e2(*p) for p in pts]
    solved=[]
    for typ in (0,1):
        rh=[c**3 if typ==0 else c*g for c,g in pts]
        h=solve(mat,rh,Q)
        assert h is not None
        jt=lambda c: (c**4/4 if typ==0 else 0)-h[0]*c-h[1]*c**2/2-h[2]*c**3/3
        q=solve(mat,[-jt(c)/g for c,g in pts],Q)
        assert q is not None
        assert all(not x.b for x in h+q)
        solved.append((typ,[x.a for x in h],[x.a for x in q]))
    Q.v=w5
    c=Q(M,1);g=Q(0,r5);row=e2(c,g)
    for typ,h,q in solved:
        val=c**3 if typ==0 else c*g
        jp=(c**4/4 if typ==0 else 0)-c*h[0]-c**2*h[1]/2-c**3*h[2]/3
        dis=val-sum(x*y for x,y in zip(row,h))-jp-g*sum(x*y for x,y in zip(row,q))
        assert dis.norm()
    print('degree 28: both signed fifth rows fail each of the two independent grade-three gates')

def main():
    assert flp(vden.numer).gcd(flp(vnum.numer)).degree()==0
    assert sorted((p.degree(),e) for p,e in factors(C))==[(2,1),(4,1),(4,1)]
    types=set()
    for p,_ in factors(C):
        Ext.P=p
        assert not sp(C)
        if sp(Ch):
            types.add('inconsistent')
        elif sp(v)==1:
            types.add('excluded normalized second/third opener')
        else:
            M=Ext([0,1])
            assert 2*M*M-6*M+3==0 and sp(v)==3 and sp(k)==-1
            assert (2*M-3)**2==sp(v)
            types.add('reflected first row occurs within opener')
    assert len(types)==3
    print('all exceptional opener V fits:',sorted(types))

    pc=factors(N4.resultant(D4))
    assert sorted((p.degree(),e) for p,e in pc)==[(4,1),(12,1)]
    for p,_ in pc:
        Ext.P=p
        if p.degree()==4:
            assert not sp(k)
        else:
            gg=poly_gcd(spel(D4),spel(N4))
            assert len(gg)==2
            t=-gg[0];M=Ext([0,1])
            assert not ev(opening,t) and ev(D0,(t-M)**2)
    print('fourth scalar denominator zero: excluded by k=0 or unique earlier pair')

    fs=factors(res)
    assert res.numer.degree()==61 and res.denom.degree()==40
    assert sorted((p.degree(),e) for p,e in fs)==[(5,1),(12,1),(16,1),(28,1)]
    for p,_ in fs:
        Ext.P=p;M=Ext([0,1])
        rr=poly_gcd(spel(Ured),spel(Vred))
        assert len(rr)==2
        x4=-rr[0]
        f=ev(D4,x4)
        if p.degree()==12:
            assert not f and not ev(N4,x4)
            assert any(q==p for q,_ in pc)
            continue
        assert f
        g4=ev(N4,x4)/f
        w4=(x4-M)**2
        assert g4 and ev(D0,w4)
        if p.degree()!=28:
            assert not ev(Known,w4) and ev(opening,x4)
            print('degree',p.degree(),': already-used reflected opener orbit')
            continue

        assert sp(B) and sp(D) and sp(F)
        assert w4 and ev(Known,w4)
        assert len(poly_gcd(spel(Known),spel(Known.diff(w))))==1
        assert len(poly_gcd(spel(Known*W),spel(D0)))==1
        assert not ev(W,w4)
        q=spel(W)
        assert len(q)==3 and q[-1]==1
        w5=-q[1]-w4
        assert w5 and w5!=w4 and ev(Known,w5)
        r5=ev(K0,w5)/ev(D0,w5)
        assert r5
        fifth_exclusion(x4,g4,w5,r5)
    print('no nowhere-zero opposite-residual chronological reflection with star opening in characteristic zero')

if __name__=='__main__':
    main()
