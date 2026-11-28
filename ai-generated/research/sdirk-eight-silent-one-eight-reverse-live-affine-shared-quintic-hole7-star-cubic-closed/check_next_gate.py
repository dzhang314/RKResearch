"""Prospective true-sixth exceptional-clock identity; no seventh-hole exclusion."""
from flint import fmpq_mpoly_ctx,fmpq

C=fmpq_mpoly_ctx.get(("v","s","g","eta","lam"))
v,s,g,eta,lam=C.gens()
y=(3*s-1)/2
d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
ell0=(1-2*d0)*fmpq(4,3)
ell1=8*(d2-70*g**4)
ell=lambda v:ell0+ell1*v
D=d2*s*s+d1*s+d0
U=ell(y)+D*(5-s)*fmpq(4,3)
V=d2*(s+y)+d1
G=v**4-16*v**3+72*v*v-96*v+24
L4=70*(g*v)**4-140*(g*v)**3+90*(g*v)**2-20*g*v+1
H=(6-18*v+9*v*v-v**3)/8
E2=v*v-4*v+2
E3=E2*(v-s)
M=v**4/4-v**3-(s+4)*(v**3/3-v*v)+(4*s+2)*(v*v/2-v)-2*s*(v-1)
delta=2*v-(8*s+2)/3
assert M+delta*H==-E2/4
L1=D*(8-64*eta)-(9-8*eta)*ell1
L=D*(8*v-56-32*eta*delta)-(9-8*eta)*ell(v)
assert L==L1*(v-y)-(9-8*eta)*U
H6=H+E3*(eta+lam*(v-y))
full=(9-8*eta)*(L4-ell(v)*H6)+D*(G-32*eta*M+(8*v-56-32*eta*delta)*H6)
collapsed=((v-y)*((9-8*eta)*(d2-lam*U)+L1*(eta+lam*(v-y)))
           +(9-8*eta)*(V-eta*U))
assert full==E3*collapsed
print("verified true exceptional-sixth affine identity; no rank-drop removed")
