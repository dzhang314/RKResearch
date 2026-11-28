"""Exact L0(V)=0 ordinary field exclusion inside the direct Fn dV=0 branch."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
from fractions import Fraction
from math import comb
import sympy as S
def rat(q):
 u=S.Rational(q);return Fraction(int(u.p),int(u.q))
def ev(q,x):
 ans=x.r.to(0)
 for a in reversed(q):ans=ans*x+a
 return ans
def ee(ce,x,var):
 return ev([rat(q)for q in reversed(S.Poly(ce,var).all_coeffs())],x)
def refl(f):
 return [(-1)**(len(f)-1+i)*sum(comb(j,i)*f[j]for j in range(i,len(f)))for i in range(len(f))]
def run(args):
 root=args.research
 Z=run_path(str(root/'dirk11-thirteen-invisible-six-cubic-zero-five/replay.py'))
 R=run_path(str(root/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
 Ring,det,cof=(R[n]for n in ('Ring','det','quot'))
 F,G,f24=Z['projection']()
 J4,J5,LC=(Z[n]for n in ('J4','J5','linear_cofactor'))
 A,B=Z['a'],Z['b']
 p=args.prime
 P=Ring('prime',prime=p)
 K=Ring('ordinary a',P,[P.to(rat(f24.nth(i)))for i in range(f24.degree())])
 aa=K.gen();oo,zz=K.to(1),K.to(0)
 def cfs(f,q):
    return [ee(S.Poly(f,B).nth(i),aa,A)for i in range(q+1)]
 c0,c1=LC(cfs(F,4),cfs(G,3),det)
 bb=-c0/c1
 assert ev(cfs(F,4),bb)==0 and ev(cfs(G,3),bb)==0
 lam=-J5(aa)/J4(aa)
 Q=[(K.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
 R3=refl(cof(cof(Q,aa),bb))
 c0,c1,c2,_=R3
 v=oo-aa
 l0=[zz,*(c/(i+2)for i,c in enumerate(R3))]
 assert ev(l0,v)==0
 Fn=[-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2]
 T=Ring('direct Fn',K,[c/Fn[-1]for c in Fn[:-1]])
 s=T.gen(); u1,u2,v=(T.to(c)for c in (c1,c2,v))
 r=6*u2*s/(u1+6*s)
 old=Ring('old cubic',T,[T.to(j)for j in R3[:-1]])
 Y=old.gen();m=Y*Y+old.to(r)*Y+old.to(s)
 W=ev([old.to(T.to(c))for c in l0],Y)/m
 signal=ev(W.v,v)
 signal.inv()
 print('W0(V) is a unit on the exact L0(V)=0 direct Fn rank72 algebra at',p)
if __name__=='__main__':
 p=ArgumentParser();p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent);p.add_argument('--prime',type=int,default=103)
 run(p.parse_args())
