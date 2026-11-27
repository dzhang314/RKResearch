#!/usr/bin/env python3
"""Reconstruct the literal tableau from the three-helper/six-tail chart."""
from fractions import Fraction as Q
from pathlib import Path
import json
from quadratic import Quad as K

def dot(v, w):
    return sum((K(x)*y for x, y in zip(v, w)), K())

def system(eq, out, n):
    data = [list(map(K, row)) + [K(rhs)] for row, rhs in zip(eq, out)]
    pivots = []
    for j in range(n):
        i = len(pivots)
        pivot = next((s for s in range(i,len(data)) if data[s][j]), None)
        if pivot is None:
            continue
        inv = data[pivot][j].inv()
        data[i], data[pivot] = data[pivot], data[i]
        data[i] = [x*inv for x in data[i]]
        for s, v in enumerate(data):
            if s != i and v[j]:
                data[s] = [x-v[j]*y for x,y in zip(v,data[i])]
        pivots.append(j)
    assert not any(row[-1] for row in data[len(pivots):])
    x = [K() for _ in range(n)]
    for i,j in enumerate(pivots):
        x[j] = data[i][-1]
    assert [dot(row,x) for row in eq] == list(out)
    return x, len(pivots)

def convolution(f,g):
    p=[K() for _ in range(len(f)+len(g)-1)]
    for i,v in enumerate(f):
        for j,w in enumerate(g):
            p[i+j]+=v*w
    return p

def clocks():
    F2=[-2,-1,1]                    # (y−2)(y+1)
    f=convolution(F2,[34,-10])     # physical x(x−2)(x−5) corrected into the defect span
    k=[K(-1),K(2),K(Q(-1,2))]
    def m(p,t=0):
        return sum((v*Q(4**(d+t),d+t+1) for d,v in enumerate(p)),K())
    def T(p):
        return [-p[0]]+[p[j-1]/j-(p[j] if j<len(p) else 0) for j in range(1,len(p)+1)]
    def h(u):
        return [K(u),-K(u)-1,K(1)]
    def L(u):
        hu=h(u)
        P,Qc=m(convolution(T(hu),f)),m(convolution(T(k),f))
        W=[P*a-Qc*b for a,b in zip(k,hu)]
        p=convolution(W,F2)
        return [m(p,i) for i in range(3)]
    def Delta(u):
        l0,l1,l2=L(u)
        return l1*l1-l0*l2
    # Delta is quadratic in u. Three exact evaluations identify its coefficients.
    d0,dplus,dminus=Delta(0),Delta(1),Delta(-1)
    scale=d0/355613
    assert dplus == scale*(248477-906502+355613)
    assert dminus == scale*(248477+906502+355613)
    assert scale
    u=K(Q(453251,248477),Q(-520,248477))
    assert Delta(u)==0
    l0,l1,_=L(u)
    y3=l1/l0
    fun=convolution(h(u),convolution(F2,[-y3,K(1)]))
    y4=m(fun,1)/m(fun)
    return [K(2),K(-1),y3,y4,u,K(1)]

def construct():
    z = 4
    y = clocks()
    c = [z-x for x in y]
    xp = [[x**j for x in c] for j in range(7)]
    moments = [K(Q(z**j,j+1)) for j in range(7)]
    b, _ = system(xp,moments,6)
    bx = [w*x for w,x in zip(b,c)]
    bxx = [w*x for w,x in zip(bx,c)]
    e_i = [[int(j == i) for j in range(6)] for i in (4,5)]
    bcx, _ = system(xp[:5] + e_i,
                         [moments[j+2]/(j+1) for j in range(5)] +
                         [b[4]*(c[4]+c[5]*(z-c[4]-1)),bx[-1]], 6)
    slots = [(i,j) for i in range(6) for j in range(i)]
    mat, rhs = [], []
    # Bx = x²/2, because the head quadratic defect is precisely x.
    for row in range(6):
        mat.append([c[j] if i==row else 0 for i,j in slots])
        rhs.append(c[row]**2/2-c[row])
    # D(1) and the extra reverse row bCB.
    for col in range(6):
        mat.append([b[i] if j==col else 0 for i,j in slots])
        rhs.append(b[col]*(z-c[col]-1))
        mat.append([bx[i] if j==col else 0 for i,j in slots])
        rhs.append(bcx[col]-bx[col])
    # Only two new grade-four defects: x² and the head node polynomial.
    vals = lambda p: [sum((x**j*w for j,w in enumerate(p)),K()) for x in c]
    for row in (bxx,bcx):
        for p in ((0,0,1),(-6,11,-6,1)):
            pf = vals(p)
            jf = vals((0,)+tuple(Q(w,j+1) for j,w in enumerate(p)))
            mat.append([row[i]*pf[j] for i,j in slots])
            rhs.append(dot(row,[jv-pv for jv,pv in zip(jf,pf)]))
    s, rank = system(mat,rhs,15)
    assert rank==15
    B = [[K(int(i==j)) for j in range(6)] for i in range(6)]
    for (i,j),v in zip(slots,s):
        B[i][j] = v
    # All helper strict taps are one; solve the three feed moments directly.
    A = [[K(int(j<=i)) for j in range(9)] for i in range(3)]
    vander = [[h**d for h in (1,2,3)] for d in range(3)]
    for x,v in zip(c,B):
        feeds,_ = system(vander,[x**(j+1)/(j+1)-dot(v,xp[j]) for j in range(3)],3)
        A.append(feeds+v)
    return [[v/z for v in row] for row in A],[K(),K(),K()]+b

if __name__=='__main__':
    d=json.loads(Path(__file__).with_name('nine-stage-quadratic.json').read_text())
    assert clocks()==[K(*a) for a in d['reflected']]
    A,b=construct()
    assert A==[[K(*a) for a in row] for row in d['A']]
    assert b==[K(*a) for a in d['b']]
    print('Reconstructed the literal quadratic nine-stage tableau with exact linear solves.')
