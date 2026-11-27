#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx
from math import prod
C=fmpz_mpoly_ctx.get(('u','m','e','Y'),'lex');u,m,e,Y=C.gens()
A=35*e*(5*e**2-3);B=15*(3*e**2-1);C0=15*e*(5-7*e**2);E=9-15*e**2
G=A*(Y-m)**3+B*m*(Y-m)**2+C0*m*m*(Y-m)+E*m**3
Ak=[(u-3)*(2*u*u-10*u+11),(u-3)*(u-2)*(2*u-3),4*(u-2)**2*(u-1),6*(u-1)**2*(2*u-3)]
a,b,c,d=Ak
H=4*a*m**6+12*m**4*(b-m*a)*(Y-m)+5*m*m*(3*c-6*m*b+2*m*m*a)*(3*(Y-m)**2-m*m)+7*(5*d-15*m*c+12*m*m*b-2*m**3*a)*(5*(Y-m)**3-3*m*m*(Y-m))
coeff=lambda v,i:C.from_dict({(u,a,b,0):c for (u,a,b,k),c in v.to_dict().items() if k==i})
G=[coeff(G,i) for i in range(4)]
H=[coeff(H,i) for i in range(4)]
F=sum(a*g for a,g in zip(Ak,G))
M=u*u-4*u+2;T=u**3-7*u*u+10*u-2
K=(u-3)*(u-2)**2;Jq=(u-3)*(u-1)*(2*u-3)
gv=lambda w:sum(v*w**i for i,v in enumerate(G))
L1=M*gv(1)+gv(u)
L0=-M*u*gv(1)-gv(u)
kap=T*M*(u-1)*G[-1]-K*L1
E1=K*(1-M)+3*T
E0=3*M*Jq-2*M*K-E1
N=2*K*(u-1)**3*L0-kap*E0;D=-2*K*(u-1)**3*L1+kap*E1

gd=N.gcd(D)
assert gd==2*(u-1)*M
N,D=N//gd,D//gd
assert N.degrees()==D.degrees()==(7,3,3,0)
Hc=sum(a*N**i*D**(3-i) for i,a in enumerate(H))
Gc=sum(a*N**i*D**(3-i) for i,a in enumerate(G))
B=[h*Gc-a*Hc for h,a in zip(H,G)]
Q1=B[2]*D+B[3]*N
Q0=B[1]*D**2+B[2]*N*D+B[3]*N**2
disc=Q1**2-4*B[3]*Q0
R,r=divmod(disc,(60*m*m*D*D)**2)
assert not r and R.degrees()==(34,22,18,0)
assert [int(a(0,0,0,0))%5 for a in Ak]==[2,2,4,2]

def divide5(P,n):
    out={}
    for k,v in P.to_dict().items():
        a,b=divmod(int(v),5**n)
        assert not b
        out[k]=a
    return C.from_dict(out)

# All three indeterminates in each chart are integral at five.
# In A, m=5*m0 and eta=5*m0*(4+5*eta0).
A0=R.compose(5*u,5*m,5*m*(4+5*e),Y)
A1,rem=divmod(A0,m**4)
assert not rem
RA=divide5(A1,11)  # the factor 5^4 accompanies m^4.
assert RA.degrees()==(34,36,18,0)
assert {k:int(v)%5 for k,v in RA.to_dict().items() if int(v)%5}=={(0,0,0,0):2}

# In B, m=1+5*m0 and 1/eta=5*eta0.
B0=C.from_dict({(a,b,18-c,d):v for (a,b,c,d),v in R.to_dict().items()})
RB=divide5(B0.compose(5*u,1+5*m,5*e,Y),5)
assert RB.degrees()==(34,22,18,0)
assert {k:int(v)%5 for k,v in RB.to_dict().items() if int(v)%5}=={(0,0,0,0):3}

# If the removed site is fourth, the raw G polynomial is rootless
# projectively modulo 5 at every five-adic u with residue zero.
V=(u-2)*(u-1)**2
late=2*K*Y**3-6*(K+Jq)*Y*Y+12*(V+Jq)*Y-12*V
assert late(0,0,0,1)%5==4
assert all(int(late(0,0,0,y))%5==(y**3+y*y+3*y+4)%5!=0 for y in range(5))
assert int((2*K)(0,0,0,0))%5==1
if __name__=="__main__":
    print("arithmetic split core bidegrees (34,22,18) verified")
    print("u=0 modulo 5: chart A residue 2 after 5^7 and chart B residue 3 after 5^5")
    print("fourth-site arithmetic G projectively rootless modulo 5")
