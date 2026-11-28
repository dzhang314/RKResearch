#!/usr/bin/env python3
"""Replay exact normalized rooted-grade scalar eliminants, with no float data."""
import sympy as S

R = S.Rational
r, t, w, h, X = S.symbols("r t w h X")
f = S.factor
D = r*r-4*r+1
P = r*r-3*r+1
W = 5*r*r-14*r+5
sigma = R(1,6)
L = 3*(r-1)*(r-2)
k = (r-R(1,2))/L
hd = r**3/(36*(r-1))
first_d_tap = r**3/(6*(r-1))
ar = r/2-first_d_tap/r
a2 = R(1,2)+1/(6*(r-1))+k
phi1 = (r*r+r-R(4,5))/k
phir = (first_d_tap+ar*r**4-r**5/5)/hd
psi1 = a2+hd/(r*(r-1)*k)
psir = ar


def phi(x):
    return f(phi1+(phir-phi1)*(x-1)/(r-1))


def psi(x):
    return f(psi1+(psir-psi1)*(x-1)/(r-1))


def J(poly,x):
    return sum(c*x**(k[0]+1)/(k[0]+1)
               for k,c in S.Poly(poly,X).terms())


def taps(nodes,x,hx,quartic):
    """Actual aggregate taps on nonzero nodes from true scalar profiles."""
    ans = []
    for i, z in enumerate(nodes):
        others = [u for j,u in enumerate(nodes) if i != j]
        hull = X*S.prod(X-u for u in others)
        den = z*S.prod(z-u for u in others)
        err = (phi(x)-L*sum(others)) if quartic else L
        ans.append((f(J(hull,x)/den),f(err/den)))
    return ans


def polyeq(a,b):
    assert S.cancel(a-b) == 0


def modzero(a,q):
    n,d=S.cancel(a).as_numer_denom()
    assert S.rem(n,q,r)==0 and S.gcd(d,q,r)==1


def linquad(a,b,q2,q1,q0):
    # For a*h+b = q2*h^2+q1*h+q0 = 0, regardless of whether a vanishes.
    return q2*b*b-q1*a*b+q0*a*a


def third():
    arr=taps([S.Integer(1),r,t],t,h,False)
    (td0,td1),(tv0,tv1),(tt0,tt1)=arr
    a=f(phi(t)-(1+r+t)*L)
    b=f(J(X*(X-1)*(X-r)*(X-t),t))
    q2,q1,q0=tt1,k+tt0-psi(t)+hd*tv1-k*sigma*td1,hd*tv0-k*sigma*td0
    polyeq(a, -3*(r-1)*(4*r*r*t+r*r-13*r*t+r+4*t)/(5*(2*r-1)))
    polyeq(b, t**3*(5*r*t-10*r-3*t*t+5*t)/60)
    polyeq(q2,-3*(r-2)*(r-1)/(t*(r-t)*(t-1)))
    polyeq(q1,(4*r**3*t*t-15*r**3*t+3*r**3+6*r*r*t*t+15*r*r*t+3*r*r
               -9*r*t**3+6*r*t*t-15*r*t+4*t*t)/
               (12*(r-2)*(r-t)*(2*r-1)*(t-1)))
    polyeq(q0,-t**3*(r*r*t*t-3*r*r*t+6*r*r-r*t*t-3*r*t+t*t)/
               (432*(r-2)*(r-1)*(r-t)*(t-1)))
    polyeq(linquad(a,b,q2,q1,q0),
           -3*t**3*(r-1)*(r-t)*(t-1)*(D*t+r*(r+1))**2/
             (100*(r-2)*(2*r-1)**2))
    tn=-r*(r+1)/D
    hs=-r**3*(r+1)**2*(2*r-1)*W/(36*(r-1)*D**4)
    polyeq(a.subs(t,tn),9*r*(r-1)*(r+1)*P/(5*(2*r-1)*D))
    polyeq((a*h+b).subs({t:tn,h:hs}),0)
    polyeq((tt0+tt1*hs).subs(t,tn),0)
    modzero(tn-(r+1),P)
    modzero(a.subs(t,r+1),P)
    modzero(b.subs(t,r+1),P)
    hx=(5-15*r)/36
    modzero((q1+2*q2*hx).subs(t,r+1),P)
    modzero((q0-q2*hx*hx).subs(t,r+1),P)
    modzero((tt0+tt1*hx).subs(t,r+1),P)
    modzero(hs-hx,P)
    print("exact third: rational resultant, explicit third diagonal, including double-root exception")
    return tn,hs,arr


def fourth(tn,hu,arr):
    # h_u is the explicit (zero-diagonal) branch, including if P=0.
    Tu_r=f((arr[1][0]+arr[1][1]*hu).subs(t,tn))
    zd=f(psi(1)+hd/(r*k))
    zv=f(r*psi(r))
    zu=f(psi(tn)+(r-1)*hd*Tu_r/hu)
    qz=f(zd*(w-r)*(w-tn)/((1-r)*(1-tn))+
         zv*(w-1)*(w-tn)/((r-1)*(r-tn))+
         zu*(w-1)*(w-r)/((tn-1)*(tn-r)))
    tap=taps([S.Integer(1),r,tn,w],w,h,True)
    e=[]
    for j in range(2):
        p=(1-w)*k*(j-sigma*tap[0][j])+(r-w)*hd*tap[1][j]+\
           (tn-w)*hu*tap[2][j]-(qz-w*psi(w))*j
        e.append(f(p))
    q=[]
    for j in range(3):
        p=((k-psi(w)) if j==1 else 0)
        if j<2: p+=-k*sigma*tap[0][j]+hd*tap[1][j]+hu*tap[2][j]
        if j>0: p+=tap[3][j-1]
        q.append(f(p))
    polyeq(linquad(e[1],e[0],q[2],q[1],q[0]),
           -r*w**3*(r+1)*(r-w)*(w-1)*(r*r-r+1)*(D*w+r*(r+1))**3/
               (1200*(r-1)*(r-2)**2*(2*r-1)*D**2*W**2))
    print("exact fourth nonzero: guarded quadratic-head impossibility")

    # At a new live y=0, the normalized nonzero aggregate taps per h are
    # the cubic coefficients of the three cardinals multiplied by L.
    nz=[S.Integer(1),r,tn]
    a=[f(L/(z*S.prod(z-u for j,u in enumerate(nz) if i!=j)))
       for i,z in enumerate(nz)]
    actual=f(k*(1-sigma*a[0])+r*hd*a[1]+tn*hu*a[2])
    polyeq(phi(0)-(1+r+tn)*L,
           9*r*(r-1)*(r+1)*(3*r*r-7*r+3)/(5*(2*r-1)*D))
    polyeq(actual-qz.subs(w,0),
           -3*r*(r-1)**2*(r+1)**2*P*(r*r-r+1)/
                (4*(r-2)*(2*r-1)*D**2*W))
    assert S.rem(3*r*r-7*r+3,P,r)==2*r
    print("exact fourth zero: true quartic gate and nonzero head gap")


if __name__=="__main__":
    fourth(*third())
