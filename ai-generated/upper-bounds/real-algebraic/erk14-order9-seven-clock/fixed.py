from fractions import Fraction as F
from itertools import combinations
from math import prod
def polmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            r[i+j]+=u*v
    return r
def polval(a,x):
    y=0
    for u in a[::-1]:y=y*x+u
    return y
def integrate(a):
    zero=sum(a)*0
    return sum((u+zero)/(k+1)for k,u in enumerate(a))
def cubic(x):
    D=polval([20,-210,910,-1995,2303,-1323,294],x)
    a=-(x-1)*polval([-20,160,-498,735,-504,126],x)/(6*D)
    b=polval([120,-1164,4634,-9387,10080,-5418,1134],x)/(6*D)
    c=-polval([36,-366,1533,-3255,3647,-2037,441],x)/D
    return [a,b,c,1]
def lag(numbers, i):
    a=numbers[i]
    return prod_poly([-b,1] for j,b in enumerate(numbers)if i!=j),prod(a-b for j,b in enumerate(numbers)if i!=j)
def prod_poly(rows):
    p=[1]
    for r in rows:p=polmul(p,r)
    return p
def masses(numbers):
    return [integrate(f)/d for f,d in (lag(numbers,i)for i in range(len(numbers)))]
def weighted_masses(x,v,w,z):
    D=prod_poly(([0,1],[-x,1],[-x/2,1]))
    out=[]
    for i in range(1,4):
        f,d=lag([1,v,w,z],i)
        out.append(integrate(polmul(f,D))/d)
    return out
def condition(x,v,w,z):
    K=weighted_masses(x,v,w,z)
    F=lambda t:t*(t-x)
    Y,U=1-v,1-w
    return K[0]*(F(z)-F(v))*Y**3-K[1]*(F(w)-F(z))*U**2*(3*Y-2*U)
def eval_geometry(g):
    x,v,w,z=g
    m=x/2
    cs=[0,1,x,m,v,w,z]
    W=masses(cs)
    # Treat all constants in generic exact/range arithmetic at least once.
    R=[1,x,v,w,z,m,x,0]
    d=[W[1],W[2]/2,W[4],W[5],W[6],W[3],W[2]/2,W[0]]
    Y=[1-s for s in R]
    rr,V,U=Y[1:4]
    u0=-rr**2/2
    K=weighted_masses(x,v,w,z)
    F0=[h*(h-x)for h in [v,w,z]]
    charges=[V**2/(2*rr)*u0]
    charges.append(charges[0]*K[0]/K[1]*(F0[2]-F0[0])/(F0[1]-F0[2]))
    charges.append(charges[0]*K[0]/K[2]*(F0[0]-F0[1])/(F0[1]-F0[2]))
    gamma=-2+4*V/(3*rr)
    S=8
    L=[[0]*S for _ in range(S)]
    L[1][0]=rr
    L[2][1]=V**2/(2*rr)
    L[2][0]=V-L[2][1]
    L[3][1]=charges[1]/u0
    L[3][2]=(U**2/2-L[3][1]*rr)/V
    L[3][0]=U-L[3][1]-L[3][2]
    for j in range(4,S):
        t=Y[j]
        v0=charges[2] if j==4 else t*0
        g0=gamma*v0
        u= -u0 if j==6 else t*0
        l0=v0/u0
        r1=t*t/2+u-l0*rr
        r2=t**3/3+g0-l0*rr**2
        s1=(r2-U*r1)/(V*(V-U))
        s2=(r2-V*r1)/(U*(U-V))
        L[j][:4]=[t-l0-s1-s2,l0,s1,s2]
    return R,d,W,L
def build(g,A0,pi):
    R,d,W,L=eval_geometry(g)
    x=g[0]
    rf,w=[u+g[0]*0 for u in R[::-1]],d[::-1]
    N=len(R)
    B=[[d[N-1-j]*L[N-1-j][N-1-i]/d[N-1-i] if i>j
        else 0 for j in range(N)]for i in range(N)]
    # First three forward virtual rows are literal origin, old xi, old half.
    loc=[0,7,8,9,10,11,12,13]
    full=[[x*u for u in row]+[0]*(14-len(row)) for row in A0]
    for i in range(3,N):
        h=[sum((rf[i]**(k+1)/(k+1)-sum(B[i][j]*rf[j]**k for j in range(i)))*pi[k][l]/x**k
                for k in range(5))for l in range(9)]+[0]*5
        for j in range(i):h[loc[j]]+=B[i][j]
        full.append(h)
    b=[0]*14
    for i,v in enumerate(w):b[loc[i]]=v
    return full,b,W
