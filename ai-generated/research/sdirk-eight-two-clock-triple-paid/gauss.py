#!/usr/bin/env python3
"""Search the two-live-Gauss-zero chart for paid-characteristic finite branches."""
from math import lcm
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

def ctx(p):
    Q=nmod_poly([1,-20,90,-140,70],p)
    fs=Q.factor()[1];d=lcm(*(f.degree() for f,e in fs))
    F=fq_default_ctx(p,d,'u');R=fq_default_poly_ctx(F);x=R.gen()
    roots=[a for a,e in (70*x**4-140*x**3+90*x*x-20*x+1).roots()]
    assert len(roots)==4
    return F,R,d,roots
