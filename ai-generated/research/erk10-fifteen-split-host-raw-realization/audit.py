"""Exact low transport identity and free second-copy direction."""
import sympy as S
Y,b,c,k=S.symbols("Y b c k")
C=4*b*k/(2*k-1)
D=3*b*k-2*c*k+c
Pl=2*Y/3+k*(4*b/3-2)*(Y-1)
Ql=k*(Y-1)+b*k*(Y-1)*(Y-b)/D
Rl=Y*Y/2+k*(b*b-2)*(Y-1)-b*k*(b*k-c*k-c+2)*(Y-1)*(Y-b)/D
N=2*(4*b*k*k*Y-4*b*k*k+2*b*k*Y+2*b*k-2*k*Y+Y)/(2*k-1)
test=4*Rl-6*c*Pl+2*c*c+4*(2-c)*(Ql-c*k*(Y-1))+(Y-c)*N
assert S.cancel(test.subs(c,C))==0
assert S.cancel((3*b*k-2*c*k+c).subs(c,C)+b*k)==0
print("4 T(L)=Z verified from the low-degree head polynomials alone")
L1=-2
Lb=-2*(1+2*k*(b-1))/b**2
Lc=-2*(2*b*c*k*k+2*b*c*k-2*b*k*k+b*k-2*c*k+c)/(c*c*D)
v=(c-b,1-c,b-1)
assert S.expand(sum(v))==0
assert S.expand(sum(t*z for t,z in zip(v,(1,b,c))))==0
values=[S.factor(sum(t*l*z**j for t,l,z in zip(v,(L1,Lb,Lc),(1,b,c))).subs(c,C))
        for j in (1,2,3)]
assert S.cancel(values[1]-2*C*values[0]/3)==0
assert S.cancel(values[2]-C*C*values[0]/2)==0
assert S.cancel(values[0]-3*(b-1)*(2*k+1)*(4*b*k-2*k+1)/(2*b*k))==0
print("paid free c-copy tap direction varies the score without changing u")
