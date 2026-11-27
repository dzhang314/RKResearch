#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx
from math import prod
C=fmpz_mpoly_ctx.get(('m','e','Y'),'lex');m,e,Y=C.gens()
A=35*e*(5*e**2-3);B=15*(3*e**2-1);C0=15*e*(5-7*e**2);E=9-15*e**2
g=A*(Y-m)**3+B*m*(Y-m)**2+C0*m*m*(Y-m)+E*m**3
H=4*m**6+12*m**4*(1-m)*(Y-m)+5*m*m*(6-6*m+2*m*m)*(3*(Y-m)**2-m*m)+7*(30-30*m+12*m*m-2*m**3)*(5*(Y-m)**3-3*m*m*(Y-m))
coeff=lambda v,i:C.from_dict({(a,b,0):c for (a,b,k),c in v.to_dict().items() if k==i})
g=[coeff(g,i) for i in range(4)]
H=[coeff(H,i) for i in range(4)]
F=g[0]+g[1]+2*g[2]+6*g[3]
D=2*g[2]+12*g[3]-g[0];N=-5*g[0]+6*g[2]+24*g[3]
Hc=sum(a*N**i*D**(3-i) for i,a in enumerate(H))
Gc=sum(a*N**i*D**(3-i) for i,a in enumerate(g))
B=[h*Gc-a*Hc for h,a in zip(H,g)]
Q1=B[2]*D+B[3]*N
Q0=B[1]*D**2+B[2]*N*D+B[3]*N**2
disc=Q1**2-4*B[3]*Q0

# Keep the exact positive square factor separate; never divide by a
# factor which could vanish on the stated degree-three, distinct chart.
rs=disc.factor()[1]
R,= [v for v,i in rs if i==1]
assert R.degrees()==(22,18,0)
square=240*m**2*D**2
assert disc==square*square*R
target=((-70*e**3+30*e**2+30*e-6)*m**3+
        (420*e**3-90*e**2-240*e+30)*m*m+
        (-1050*e**3+90*e**2+630*e-30)*m+1050*e**3-630*e)
assert F==target

# Exceptional zero slope and constant would make g proportional to the
# reflection Laguerre cubic. Compare coefficient ratios to eliminate m.
b=g[2]//m;d=g[1]//(m*m);v=g[0]//(m**3);a=g[3]
p=81*d*a-18*b*b
q=-729*v*a*a+6*b**3
def remove(poly,den):
    while (g:=poly.gcd(den)).total_degree()>0:
        poly,r=divmod(poly,g)
        assert not r
    return poly
assert remove(remove(p,a),b).gcd(remove(remove(q,a),b)).total_degree()==0
assert all((j**3-9*j*j+18*j-6)%5 for j in range(5))

# Chart A: e=m*k, m=5*v; remove the even power m^4 before
# dividing by the uniform odd factor 5^7.
S=fmpz_mpoly_ctx.get(('v','k'),'lex')
ra={}
for (i,j,_),c in R.to_dict().items():
    i=i+j-4
    assert i>=0
    a,b=divmod(int(c)*5**i,5**7)
    assert b==0
    ra[i,j]=a
RA=S.from_dict(ra)
assert RA.degrees()==(36,18)
modA={(i,j):n%5 for (i,j),n in ra.items() if n%5}
assert modA=={(0,4):3,(0,3):4,(0,2):2,(0,1):1,(0,0):3}
assert sum(z*4**j for (_,j),z in modA.items())%5==3

# Chart B: m=1+5*k and 1/e=5*t. The homogenizing power 18 is even.
k,t=S.gens()
src=S.from_dict({(i,18-j):c for (i,j,_),c in R.to_dict().items()})
src=src.compose(1+5*k,5*t)
rb={}
for ij,c in src.to_dict().items():
    a,b=divmod(int(c),5**5)
    assert b==0
    rb[ij]=a
RB=S.from_dict(rb)
assert RB.degrees()==(22,18)
assert {(i,j):n%5 for (i,j),n in rb.items() if n%5}=={(0,0):2}

print("exact reflection polynomial and nonzero rational slope checked")
print("discriminant numerator = (240 m^2 D^2)^2 × primitive (22,18) core")
print("mod-five rescaled split residues: chart A 3 after 5^7; chart B 2 after 5^5")
