"""Exact zero-sixth-slope certificate for the corrected seventh-hole star chart."""
from flint import fmpq_mpoly_ctx,fmpq,fmpq_poly
from itertools import combinations
C=fmpq_mpoly_ctx.get(('r','g'),ordering='lex')
r,g=C.gens()

def coefs(g):
 d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
 d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
 d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
 l0=fmpq(4,3)*(1-2*d0)
 l1=8*(d2-70*g**4)
 return d0,d1,d2,l0,l1

def mul(L,M):
 z=[C.constant(0)]*(len(L)+len(M)-1)
 for i,a in enumerate(L):
  for j,b in enumerate(M):z[i+j]+=a*b
 return z

def model():
 d0,d1,d2,l0,l1=coefs(g)
 P=mul([2*g*g,-4*g,C.constant(1)],[g*g*(d0-fmpq(9,8)*l1),g*d1,d2])
 X=[6*g**3,-18*g*g,9*g,C.constant(-1),C.constant(0)]
 h=[g*(l0+7*l1)*a+8*b for a,b in zip(X,P)]
 h0=[sum(a/(j+i+1) for i,a in enumerate(h)) for j in range(4)]
 Js=[h0[j+1]-r*h0[j] for j in range(3)]
 return Js,(g,d2,l1,l0+7*l1),h0,h

def check():
    J,gs,H,z=model()
    assert [w.degrees() for w in J]==[(1,8)]*3
    R=[J[i].resultant(J[j],0) for i,j in combinations(range(3),2)]
    assert [w.degrees() for w in R]==[(0,16)]*3
    Q=R[0].gcd(R[1]).gcd(R[2])
    coeff=Q.to_dict()
    P=fmpq_poly([coeff.get((0,i),0) for i in range(Q.degrees()[1]+1)])
    Pi=fmpq_poly([1,-20,180,-840,1400])/1400
    assert P==Pi**2
    print("exact zero sixth slope: common degree-8 diagonal Pi^2, impossible by true D(s) != 0")


if __name__=="__main__":
    check()
