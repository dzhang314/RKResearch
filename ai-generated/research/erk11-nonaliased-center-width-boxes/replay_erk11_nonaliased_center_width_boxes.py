#!/usr/bin/env python3
import flint
F=flint.fmpq
P=flint.fmpq_poly
C=flint.fmpq_mpoly_ctx.get(('a','b','s'))
a,b,s=C.gens()
zero=C.from_dict({})
one=C.from_dict({(0,0,0):1})
d=1-b; Y=1-s
W=s*s*(s-a)**2
V=(1-s)**2*(s-d)**2
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def dot(l,r):return 210*sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
def prim(f):return C.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in f.to_dict().items()})
def it(f,shift=0):
 o={}
 for (i,j,k),c in f.to_dict().items():o[(i,j,0)]=o.get((i,j,0),0)+c/(k+shift+1)
 return C.from_dict(o)
def L(t):return [t**(j+1) for j in range(5)]
def R(t):return [(1-t)*t**j for j in range(5)]
def qdiv(p,g):
 q,r=divmod(p,g)
 assert r.is_zero()
 return q
def discriminant():
 p=prim(W);q=it(V)-prim(V)
 H=it(p*V);C1=it(p*V,1);C2=it(W*q,1);J=it(p*q)
 I0,I1,I2=[it(W*V,k) for k in range(3)]
 assert H==it(W*q) and J==C1-C2
 A=s*(s-a);B=(1-s)*(s-d)
 M=I1-s*I0;T=I2-2*s*I1+s*s*I0
 δ1=C1-H*s;δ2=C2-H*s
 l=[qdiv(a**5*f-30*p*g,A) for f,g in zip(L(s),L(a))]
 r=[qdiv(b**5*f-30*q*g,B) for f,g in zip(R(s),R(d))]
 la=[30*f for f in L(a)];ra=[30*g for g in R(d)]
 # Cleared A is J*a^5*b^5 times original A, C is original C/J.
 A0,A1,A2,A3=J*dot(l,r),J*dot(la,r),J*dot(l,ra),J*dot(la,ra)-a**5*b**5
 C0=J*A*B*(J*T-δ1*δ2)
 c1=J*B*(-H*T+δ2*M)
 c2=J*A*(-H*T+δ1*M)
 c3=H**2*I2-H*(C1+C2)*I1+I0*C1*C2
 E0=A0*c2-C0*A2
 E1=A0*c3+A1*c2-C0*A3-c1*A2
 E2=A1*c3-c1*A3
 Delta=E1**2-4*E0*E2
 assert Delta.degrees()==(26,26,12) and len(Delta)==5607
 print('cleared discriminant degrees (26,26,12); exact polynomial has 5607 terms')
 return Delta
def centered_coefficients(delta,a0,b0,l,r):
 base=delta.compose(a+a0,b+b0,s)
 P0=P([0,1])
 ph=[(l+r*P0)**k*(1+P0)**(12-k) for k in range(13)]
 out=[{} for i in range(13)]
 for (i,j,k),c in base.to_dict().items():
  for m,t in enumerate(ph[k].coeffs()):
   out[m][(i,j)]=out[m].get((i,j),0)+c*t
 return out
def signs(coeffs,da,db):
 top=[]
 for dct in coeffs:
  c0=dct[(0,0)]
  ab=sum(abs(v)*da**i*db**j for (i,j),v in dct.items() if i or j)
  top.append(c0+ab)
 return top
def replay():
    delta=discriminant()
    for ep,l,r,rho in (
        (F(1,100),F(71,100),F(37,50),F(93,100)),
        (F(1,200),F(7,10),F(3,4),F(43,100)),
    ):
        aa=F(1,5);bb=F(3,5)
        assert 0<aa-ep and aa+ep<1 and 0<bb-ep and bb+ep<1
        assert aa+ep<1-bb-ep and 1-bb+ep<l and r<1
        coeffs=centered_coefficients(delta,aa,bb,l,r)
        up=signs(coeffs,ep,ep)
        assert len(up)==13
        for co,upper in zip(coeffs,up):
            c0=co[(0,0)]
            assert c0<0 and upper<0
            assert (upper-c0)/(-c0)<rho<1
        print('radius',ep,'clock interval',l,r,'all 13 coefficients negative; '
              'off-center sum / central magnitude below',rho)
    print('both complete ordered boxes excluded by the necessary discriminant')

if __name__=='__main__':
    replay()
