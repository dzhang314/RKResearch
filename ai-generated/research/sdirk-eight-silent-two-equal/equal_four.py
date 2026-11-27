"""Equal invisible tags, undetected h, four active zero stages."""
import sympy as S
from itertools import product,permutations
p=1129
def inv(x):
 return pow(int(x)%p,-1,p)
def q(n,d):
 return n*inv(d)%p
def gauss3(x):return (20*x**3-30*x*x+12*x-1)%p
def gauss4(x):return (70*x**4-140*x**3+90*x*x-20*x+1)%p
def solve3(M,y):
 P=list(permutations(range(3)))
 def det(A):return sum((-1)**sum(v[i]>v[j] for i,j in ((0,1),(0,2),(1,2)))*A[0][v[0]]*A[1][v[1]]*A[2][v[2]] for v in P)%p
 d=inv(det(M))
 return [(det([[y[i] if j==k else M[i][j] for j in range(3)] for i in range(3)])*d)%p for k in range(3)]
def taps(nodes,ms):
 out=[]
 for i,v in enumerate(nodes):
  a=[1];den=1
  for j,w in enumerate(nodes):
   if i==j:continue
   b=[0]*(len(a)+1)
   for k,c in enumerate(a):b[k]-=c*w;b[k+1]+=c
   a=b;den*=v-w
  out.append(sum(c*x for c,x in zip(a,ms))*inv(den)%p)
 return out
def case(t,star,g,x,y=None):
 a=g*(2+2*t)%p;b=g*(2-2*t if star else 3+4*t)%p
 A21=(a-g)%p;A32=0 if star else (q(3,2)*(a-g)-g)%p
 A31=(b-g-A32)%p
 ha=q(A21*g*g,2);hb=q(A31*g*g,2)
 m=lambda u,j:(q(u**(j+1),j+1)-g*u**j)%p
 # k=2 (quadratic nodal) and k=3 (cubic nodal) coefficients.
 Q=[a*b,-(a+b),1]
 D=sum(Q[j]*m(x,j) for j in range(3))
 V=sum(Q[j]*m(x,j+1) for j in range(3))
 z=V*inv(D)%p
 ns=[a,b,z]
 assert len(set(ns))==3 and x not in ns
 # Literal row four gives its h using independently modified third scalar row.
 F=solve3([[1,1,1],[g,a,b],[q(2*g*g,3),a*a,b*b]],[m(z,j) for j in range(3)])
 hz=q(F[0]*g*g,2)
 T=taps(ns,[m(x,j) for j in range(3)])
 assert sum(T[i]*ns[i]**3 for i in range(3))%p==m(x,3)
 if y is None:
  assert sum(v*d for v,d in zip(T,[ha,hb,hz]))%p
  return
 U=taps(ns+[x],[m(y,j) for j in range(4)])
 C=[(a-g)*ha,(b-g)*hb,(z-g)*hz]
 read=lambda u,W,V:((g*u**4-q(u**5,5)+sum(w*v**4 for w,v in zip(W,V)))%p,sum(w*c for w,c in zip(W,C))%p)
 t1,h1=read(x,T,ns);t2,h2=read(y,U,ns+[x])
 l1,l2=gauss3(x),gauss3(y)
 assert l1 and l2
 assert ((l1*t2-l2*t1)%p or (l1*h2-l2*h1)%p)
def rank_one(f,star,g,s):
 a=g*(2+2*f)%p;b=g*(2-2*f if star else 3+4*f)%p
 m=lambda u,j:(q(u**(j+1),j+1)-g*u**j)%p
 T=solve3([[1,1,1],[g,a,b],[q(2*g*g,3),a*a,b*b]],[m(s,j) for j in range(3)])
 return T[0]%p
def main():
 assert S.isprime(p)
 tr=[t for t in range(p) if (2*t*t-1)%p==0]
 L=[r for r in range(p) if gauss4(r)==0]
 assert tr==[203,926] and L==[100,214,916,1030]
 count=0
 for t,f,g in product(tr,(True,False),L):
  assert ((1-g)%p) in L and ((1-g)%p)!=g
  for x,y in permutations([r for r in L if r!=(1-g)%p],2):
   case(t,f,g,x,y);count+=1
 print('Equal tag four-active: exact monic Gauss-site test',count)
 for t,f,g,x in product(tr,(True,False),L,L):
  assert rank_one(t,f,g,x)
  case(t,f,g,x)
 for g,c in product(L,L):
  x=(1-g)%p
  if c==x:continue
  u=(x-c)*inv(g)%p;k=(1+2*u-u*u)%p
  assert (2*(g-x)-g*k*(u-2))%p
 for t in tr:
  g=inv(2)
  assert gauss4(g)
  assert gauss4((1-g*(2+2*t))%p)
 print('Equal tag Gauss gates: literal row four, earliest active, invisible eighth, midpoint tail')
if __name__=='__main__':main()
