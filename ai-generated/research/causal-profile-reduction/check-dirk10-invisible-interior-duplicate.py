#!/usr/bin/env python3
"""Independent exact fixed-clock replay for the two clean-duplicate charts."""

from itertools import permutations
import sys

def one_later(U,W,V,div):
 K=V*(V-U)*(V-div(U,2))
 dU=div(-U**3,6*V*(V-U))
 mu=div(V*(U-V)*(4*U*U-5*U*V-5*V*V),5)
 dV=div(V**3*(V-2*U),12*K)
 sv=div(-V**3,6*U*(U-V))
 mv=div(V**3*(4*V*V-5*U*V-5*U*U),30*dV)
 qU=div(V,2)+div(div(U*U,2)-V*dU,U)
 di=div(V,2)-div(U*sv,V)-dV
 qV=div(V,2)+di+div(dU*sv,dV)
 M=mu+div((mv-mu)*(W-U),V-U)
 den=M-(U+W+V)*K
 d=div(W**3*(3*W*W-5*(U+V)*W+10*U*V),60*den)
 m1,m2,m3=div(W*W,2),div(W**3,3),div(W**4,4)+K*d
 def tap(y,p,q):
  return div(m3-(p+q)*m2+p*q*m1,y*(y-p)*(y-q))
 aU,aW,tV=tap(U,W,V),tap(W,U,V),tap(V,U,W)
 qW=aW+div(dU*aU,d)+div(V,2)+dV*(div(tV,d)-1)
 err=(V-U)*(qW-qU)-(W-U)*(qV-qU)
 return err,d,den


def two_later(U,W,V,d):
 K=V*(V-U)*(V-d(U,2))
 du=d(-U**3,6*V*(V-U))
 dw=d(W**3*(2*U-W),6*(U-2*W)*V*(V-U))
 mu=d(V*(U-V)*(4*U*U-5*U*V-5*V*V),5)
 slope=d(3*V*(U-V)*(U-W)**2,5*(2*U-W))
 mv=mu+slope*(V-U)
 de=mv-(U+W+V)*K
 dz=d(V**3*(3*V*V-5*(U+W)*V+10*U*W),60*de)
 aUU=d(d(U*U,2)-V*du,U)
 rU=d(V,2)+aUU
 # W, both pair contributions represented by DW, with early duplicate earlier than W.
 m1=d(W*W,2)-V*dw
 m2=d(W**3,3)-V*V*dw
 aWU=d(m2-W*m1,U*(U-W))
 aWW=d(m2-U*m1,W*(W-U))
 rW=d(V,2)+d(du*aWU,dw)+aWW
 # Aggregate column pair lines at V, true output weight normalized to one.
 n1,n2,n3=d(V*V,2),d(V**3,3),d(V**4,4)+K*dz
 def tap(y,p,q):
  return d(n3-(p+q)*n2+p*q*n1,y*(y-p)*(y-q))
 aU,aW,tV=tap(U,W,V),tap(W,U,V),tap(V,U,W)
 di=tV-dz
 rV=d(V,2)+di+d(du*aU+dw*aW,dz)
 err=(W-U)*(rV-rU)-(V-U)*(rW-rU)
 return err,dz,de



def signed_square(U, W, R, d):
    J = R*U*U-4*R*U*W+R*W*W+U*U*W+U*W*W
    L = 3*R*R-5*R*(U+W)+10*U*W
    M = 4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W
    return d(-3*(R-U)*(R-W)*(U-W)*J*J, (U-2*W)*(2*U-W)*L*M)


def check(p):
    roots = tuple(x for x in range(p) if (42*x**4-84*x**3+56*x*x-14*x+1) % p == 0)
    assert len(roots)==4
    def d(a,b):
        assert b % p
        return a*pow(b%p,-1,p)%p
    for U,W,V in permutations(roots,3):
        assert (V-2*U) % p and (U-2*W) % p
        a, dw, den1 = one_later(U,W,V,d)
        b, dv, den2 = two_later(U,W,V,d)
        assert all(i % p for i in (a,b,dw,dv,den1,den2))
        assert a % p == -signed_square(U,V,W,d) % p
        assert b % p == -signed_square(U,W,V,d) % p
    print(f"mod {p}: all 24 one-later and 24 two-later affine defects nonzero")


if __name__=='__main__':
    for prime in map(int,sys.argv[1:]) if len(sys.argv)>1 else (419,719):
        check(prime)
