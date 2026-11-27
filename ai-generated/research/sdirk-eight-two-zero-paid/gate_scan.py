#!/usr/bin/env python3
"""Search the two-live-Gauss-zero chart for paid-characteristic finite branches."""
from flint import fq_default_ctx,fq_default_poly_ctx,nmod_poly

def phase(u):
    s2=1+2*u-u*u
    if u==0 or s2==0:return []
    out=[]
    if u!=1 and u!=2:out.append(('S',2-u,s2,0))
    h=-2+u+4*u*u-u**3
    if h!=0:
        r=2*u*(3*u-2)/h
        if r!=0:out.append(('A',2*u,1+4*u-4*u*u+2*r*u,r))
    return out

def twozero(F,a,b):
    o=F.one(); z=F.zero()
    k=a+b-2
    q=(a+b)*k-a*b+9*o/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    jx=lambda x:x**4/4+k*x**3/3+q*x*x/2
    g=(j(o)-j(b))/r(b)
    if g==0:return None
    D=j(a)-g*r(a);N=jx(a)-g*a*r(a)
    if D==0:
        return ('rim-mass',g,D,N) if N==0 else None
    d=N/D
    R=r(g)
    if d==g or R==0:
        return ('silent-first-or-null-graph',g,d,R,a,b)
    ud=d/g-1
    out=[]
    for sid,w,kg,t in phase(ud):
        if kg!=0 and R*kg==r(g*(1+w)):
            out.append((2,sid,ud,w,t))
    d0=R+g*g;n0=2*R-g*(2*g+k)
    if d0==0:
        if n0==0:out.append(('free-second-gap',g,d,R,a,b,None))
    else:
        u=n0/d0
        for sid,w,kg,t in phase(u):
            if ud==w and kg!=0:out.append((3,sid,u,w,t))
            if kg!=0 and R*kg==r(g*(1+w)):
                out.append(('late',sid,u,w,t))
    if out:
        return ('rigid',g,d,R,a,b,out)
def three_two_clocks(F,a,b):
    o=F.one(); z=F.zero()
    k=a+b-2
    q=(a+b)*k-a*b+9*o/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x**3/3+k*x*x/2+q*x
    g=j(a)/r(a)
    if g==0:return None
    R=r(g)
    den=R+g*g;n=2*R-g*(2*g+k)
    if not all(x!=0 for x in (R,den)):
        return ('degenerate',g,R,a,b) if not den!=0 and n==0 else None
    u=n/den
    out=[]
    for sid,w,kg,t in phase(u):
        if kg!=0 and R*kg==r(g*(1+w)):
            out.append(('g3-nonzero',sid,u,w,t))
        if kg==0 and g*(1+w)==a:
            out.append(('first-zero-row3',sid,u,w,t))
    if out:return ('rigid',g,R,a,b,out)

def ctx(p):
    Q=nmod_poly([1,-20,90,-140,70],p)
    fs=Q.factor()[1];d=max(f.degree() for f,e in fs)
    F=fq_default_ctx(p,d,'u');R=fq_default_poly_ctx(F);x=R.gen()
    roots=[a for a,e in (70*x**4-140*x**3+90*x*x-20*x+1).roots()]
    assert len(roots)==4
    return F,R,d,roots
