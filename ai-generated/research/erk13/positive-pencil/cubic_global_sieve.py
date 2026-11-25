#!/usr/bin/env python3
"""Discover behavior-uniform integer components for bare cubic coprimality."""
import sys,json
from pathlib import Path
from math import gcd
sys.path.insert(0,sys.argv[1])
from check_pencil_projection import cubic_pair,F,J
from quartic_global_sieve import Mod,Split
MOM=[[0,12,-15],[-18,-24,60],[60,-40,-50],[-45,60]]
def one(C,D):
 N=C.N;g=C.gg(D['R'],D['T'])
 if len(g)!=2:return ('zdegree',g)
 z=-g[0]%N
 if not C.nz(z) or not C.nz(z-1):return ('z0/1',)
 A,H=cubic_pair(z);h=C.gg(A,H)
 if len(h)!=2:return ('tdegree',h)
 t=-h[0]%N;u=t*z%N
 if not C.nz(t):return ('tzero',)
 f=C.ev(F,t); j=C.ev(J,t)
 if not C.nz(f) or not C.nz(j):return ('singular',)
 b=-j*pow(f,-1,N)%N;W=[(b*y+x)%N for x,y in zip(J,F)]
 if C.nz(C.ev(W,u)):return ('uNotRoot',)
 P=C.vp([C.ev(row,z)*pow(t,-i,N)%N for i,row in enumerate(MOM)])
 def mom(k,y):return C.ev([0]*(1+k)+[v*pow(1+k+i,-1,N)%N for i,v in enumerate(P)],y)
 cap=mom(3,t)*pow(t*j,-1,N)%N
 if any(C.nz(v) for v in [mom(1,t),mom(2,t),mom(2,u)-t*mom(1,u),mom(3,u)-t*mom(2,u)-cap*u*C.ev(J,u)]):return ('not5mom',)
 c=C.gg(W,P)
 if len(c)<=1:return ('coprime',)
 bplus=C.nz(b+1);p0=C.nz(P[0]);p1=C.nz(C.ev(P,t));p2=C.nz(C.ev(P,u));k=C.nz(cap)
 return ('accept',len(c)-1,bplus,p0,p1,p2,k,len(P)-1)
def split(N,D):
 C=Mod(N)
 try:r=one(C,D)
 except Split as e:
    a=e.args[0];r=N
    while gcd(r,a)>1:r//=gcd(r,a)
    if r==1:return split(a,D)
    return split(N//r,D)+split(r,D)
 print(r,N.bit_length(),str(N)[:45],flush=True)
 return [[N,r]]
def run(src,dst):
 d=json.loads((dst/'cubic_joint_norm.json').read_text());N=int(d['resid'],16)
 out=split(N,json.loads((dst/'exact_cubic_outer.json').read_text()))
 (dst/'cubic_global_components.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
if __name__=='__main__':run(Path(sys.argv[1]),Path(sys.argv[2]))
