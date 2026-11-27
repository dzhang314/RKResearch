from rational_field import E
from flint import fmpq_poly
E.P=fmpq_poly([371,-224,32])
m=E([0,1]);v=E(21)/8;k=2-v;h=E(1)/2
t0=1-m;b=m-2;beta=3-m;t1=m-1;t5=5-m
n=3*m*m/5
L4=lambda t:t**4-6*m*m*t*t/7+3*m**4/35
L3=lambda t:t*(t*t-n)
P3=lambda t:(t-beta)*((t-beta)**2-4)
s0=2*(3*m**4/35+3*beta**4-12*beta*beta)
s1=-16*beta*(beta*beta-1)
s2=2*(-6*m*m/7+6*beta*beta+4)
S=lambda t:s0+s1*t+s2*t*t
assert s1+2*b*s2==0 and 4*b*(b*b+v)-12*m*m*b/7==0
den=S(t1)-2*L4(t5)/k
H=(L4(t1)-L4(t5)/k)/den
BB=-2*L4(t5)/(H*k)
d=-2*L4(t0)/BB
gR=H*k
big=L4(t5)-gR*(S(t5)+BB*(gR-h))
assert not big
C0=-L3(t0)/(h*d)
C5=-L3(t5)/(h*gR) # V at the two actual residuals at t5
C1=(C5-C0)/(t5-t0)
assert H*BB*d*gR and d!=h and gR!=h
r=lambda t,g:(g/h*P3(t),-(1-g/h)*L3(t)+g*(g-h)*(C0+C1*(t-t0)))
r1=r(t1,H)
tn=2*b-t5
r2=r(tn,gR)

assert r1[0]
lam=r1[1]/r1[0]
assert lam*r2[0]-r2[1]==E(-29055889337995)/805749053699+(E(140638940355589)/11280486751786)*m
assert lam*r2[0]-r2[1]
print('exceptional quadratic has an inconsistent V fit')
