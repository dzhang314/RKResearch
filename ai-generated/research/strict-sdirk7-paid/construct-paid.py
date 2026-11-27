"""Reconstruct the factorial-only tableau using only exact rational arithmetic."""
from fractions import Fraction as F
from pathlib import Path
import json

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))

def solve(M, y):
    """Deterministic left-to-right elimination; set the free variables to zero."""
    n = len(M[0])
    A = [[F(x) for x in row] + [F(t)] for row,t in zip(M,y)]
    pivots = []
    for j in range(n):
        i = len(pivots)
        r = next((k for k in range(i,len(A)) if A[k][j]), None)
        if r is None:
            continue
        A[r],A[i] = A[i],A[r]
        A[i] = [a/A[i][j] for a in A[i]]
        for k in range(len(A)):
            if k != i and A[k][j]:
                a = A[k][j]
                A[k] = [x-a*y for x,y in zip(A[k],A[i])]
        pivots.append(j)
    assert not any(row[-1] for row in A[len(pivots):])
    x = [F(0)]*n
    for i,j in enumerate(pivots):
        x[j] = A[i][-1]
    assert [dot(row,x) for row in M] == y
    return x

def reconstruct(z, u, nodes):
    c = list(map(F,nodes))
    k = len(c)
    C = [[t**i for t in c] for i in range(7)]
    b = solve(C,[F(z**i,i+1) for i in range(7)])
    b1 = [w*t for w,t in zip(b,c)]
    b2 = [w*t*t for w,t in zip(b,c)]
    r = solve(C[:5] + [[int(j==i) for j in range(k)] for i in (k-2,k-1)],
              [dot(b,C[j+2])/(j+1) for j in range(5)] +
              [b[-2]*(c[-2]+c[-1]*(z-c[-2]-1)), b[-1]*c[-1]])
    P = [(2-u)*x+u-1 for x in c]
    JP = [(2-u)*x*x/2+(u-1)*x for x in c]
    slots = [(i,j) for i in range(k) for j in range(i)]
    rows,rhs = [],[]
    for i0 in range(k):
        rows.append([P[j] if i==i0 else 0 for i,j in slots])
        rhs.append(JP[i0]-P[i0])
    for j0 in range(k):
        rows.append([b[i] if j==j0 else 0 for i,j in slots])
        rhs.append(b[j0]*(z-c[j0]-1))
        rows.append([b1[i] if j==j0 else 0 for i,j in slots])
        rhs.append(r[j0]-b1[j0])
    for w in (r,b2):
        for d in (0,2,3):
            rows.append([w[i]*C[d][j] for i,j in slots])
            rhs.append(dot(w,C[d+1])/(d+1)-dot(w,C[d]))
    T = [[F(i==j) for j in range(k)] for i in range(k)]
    for (i,j),v in zip(slots,solve(rows,rhs)):
        T[i][j] = v

    # Helper clocks are 1, 1+u, 0; their quadratic defect is P.
    a32 = F(u+1,2*u)
    A = [[F(1),F(0),F(0)], [F(u),F(1),F(0)], [-1-a32,a32,F(1)]]
    t = 1+u
    for x,row in zip(c,T):
        v = x-sum(row)
        w = x*x/2-dot(row,c)
        y = x**3/3-dot(row,C[2])
        f1 = (y-w)/(t*(t-1))
        f0 = w-t*f1
        A.append([f0,f1,v-f0-f1]+row)
    A = [row+[F(0)]*(k+3-len(row)) for row in A]
    return [[p/z for p in row] for row in A], [F(0)]*3+b

if __name__=='__main__':
    s = json.loads(Path(__file__).with_name('ten-stage-paid.json').read_text())
    A,b = reconstruct(s['z'],s['u'],s['normalized_tail_clocks'])
    assert A == [[F(x,s['stage_den']) for x in row] for row in s['A']]
    assert b == [F(x,s['weight_den']) for x in s['b']]
    # Pivot obstruction in each old fixed first-adjoint chart.
    assert F(-4,2835)*(-2)/F(248,735) == F(7,837)
    assert F(53,2688)*(-2)/F(1585,4032) == F(-159,1585)
    print('Reproduced the exact ten-stage factorial-only tableau.')
