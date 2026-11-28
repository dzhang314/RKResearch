"""Replay the exact row eliminations behind reducedHeadDeterminant."""
import sympy as S
b,c,z,k=S.symbols("b c z k")
same=lambda a,b:S.cancel(a-b)==0
D=3*b*k-2*c*k+c
A=1+2*k*(b-1)
C=2*b*c*k*k+2*b*c*k-2*b*k*k+b*k-2*c*k+c
L1=-2; Lb=-2*A/b**2; Lc=-2*C/(c*c*D)
L=b*k/((b-1)*D)
P=2*z/3+k*(4*b/3-2)*(z-1)
R=z*z/2+k*(b*b-2)*(z-1)-b*k*(b*k-c*k-c+2)*(z-1)*(z-b)/D
H=L*(z-1)*(z-b)
Aa=lambda j: c**j*Lc+(c-b)/(b-1)*L1-(c-1)/(b-1)*b**j*Lb
Bb=lambda j: L1*k*(z-1)+(b**j*Lb-L1)*H-[1,P,R][j-1]
s=b*k-2*c*k+c
a2=4*(2*k-1)*(3*b*c*k+s*z)
a3=12*b*b*c*k*k+(2*k-1)*s*z*z
b2=4*k*(2*k-1)
b3=k*(3*b*k+(2*k-1)*z)
V=(b-c)*(c-1)
J=(z-1)*(z-b)*(z-c)
assert same(Aa(2)-2*z*Aa(1)/3,V*a2/(3*b*c*D))
assert same(Aa(3)-z*z*Aa(1)/2,V*a3/(b*c*D))
assert same(Bb(2)-2*z*Bb(1)/3,J*b2/(3*D))
assert same(Bb(3)-z*z*Bb(1)/2,J*b3/D)
assert S.expand(a2*b3-a3*b2-12*b**2*k**3*(2*k-1)*(z-c))==0
print("exact four reduced entries and the denominator-cleared 2x2 determinant pass")
