"""Scale-free literal rows 1--5 of the unequal invisible two-clock chart."""
import sympy as SY
from sympy.polys.rings import ring
from itertools import permutations
K=SY.QQ.algebraic_field(SY.sqrt(2)/2)
S,z,H=ring('z H',K);t=K.unit;g1=K.one/2
J,Z=ring('z',K)
def det(A):
 return sum((-1)**sum(p[i]>p[j] for i in range(len(A)) for j in range(i+1,len(A)))*
            prod(A[i][p[i]] for i in range(len(A))) for p in permutations(range(len(A))))
def prod(x):
 r=1
 for a in x:r*=a
 return r
def solve(A,b):
 d=det(A);return [det([[b[i] if j==k else w for j,w in enumerate(r)] for i,r in enumerate(A)])/d for k in range(len(A))]
def ps(a):
 return J.from_dict({(i,):v for (i,j),v in a.items() if not j})
def phases(front):
 u=1+2*t;w=2-u if front else 2*u;r=K.zero if front else 3*u/2-1
 a,b=1+u,1+w
 ha,hb=g1*u,g1*(w-r)
 U=[[1,1,1],[K.one,a,b],[K.one-K.one/3,a*a,b*b]]
 q=solve(U,[K.zero,K.one,4*K.one/3])
 sg=g1*q[0]
 assert sg
 tau_a=a**3+u-a**4/4
 tau_b=b**3+w-r+r*a**3-b**4/4
 TA,TB=tau_a/ha,tau_b/hb
 HA,HB=K.one,1+r*ha/hb
 V=[[1,1,1],[K.one,a,b],[K.one,a*a,b*b]]
 ss=solve(V,[z-1,z*z/2-z,z**3/3-z*z+2*H/3])
 T=ss[0]+a**3*ss[1]+b**3*ss[2]-z**4/4+z**3-(TA+(z-a)*(TB-TA)/(b-a))*H
 X=(S(1+sg-HA)-(z-a)*(HB-HA)/(b-a))*H-sg*g1*ss[0]+ha*ss[1]+hb*ss[2]
 A=ps(T);B=ps((T-S.from_dict({(i,0):v for (i,),v in A.items()})).exquo(H))
 C=ps(X);D=ps((X-S.from_dict({(i,0):v for (i,),v in C.items()})).exquo(H))
 L=(A*D-B*C).exquo((Z-a)*(Z-b)).monic()
 # A nonzero slope at the repeated front clock forces the literal twin.
 for y,h in ((a,ha),(b,hb)):
  assert not (A.evaluate(Z,y)+B.evaluate(Z,y)*h)
  assert not (C.evaluate(Z,y)+D.evaluate(Z,y)*h)
  assert B.evaluate(Z,y) or D.evaluate(Z,y)
 assert L.gcd(B).gcd(D).degree()==0
 print('front',front,'sigma',K.to_sympy(sg),'s-factor degrees',[(r.degree(),e) for r,e in L.factor_list()[1]],flush=True)
 print('exact s factor',L.as_expr(),flush=True)
 return a,b,ha,hb,sg,L,A,B,C,D
if __name__=='__main__':
 for p in (True,False):
  phases(p)
