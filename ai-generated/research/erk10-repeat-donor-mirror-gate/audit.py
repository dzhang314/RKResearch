#!/usr/bin/env python3
"""Standalone exact coefficient calculation for the older reflected schedule."""
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'erk10-late-helper'))
import replay as P
Z,O=Q(0),Q(1)
X=[Z,O];Y=[O,-O]
U=[Z,O]
def primitive_shapes(branch,t):
    # basis q with f = X(X-xi)q; the xi² scaling has been cleared globally.
    V=U if branch=='center'else P.pw(U,2)
    xi=[Q(1,2)]if branch=='center'else [Q(1,2),Q(1,2)]
    q=([Q(1,4),Q(-1,4)],[-O],[O])if branch=='center'else (
      [Q(1,4),Q(-1,4)],[-O,Q(1,2)],[O])
    a=[P.ev(r,t)for r in P.R]
    ell4=P.add(*(P.scale(a[j],P.mul(w,P.pw(xi,j)))for j,w in enumerate(q)))
    ell5=P.add(*(P.scale(a[j+1],P.mul(w,P.pw(xi,j+1)))for j,w in enumerate(q)))
    return P.add(P.mul(P.add(P.scale(Q(3),V),[-O]),ell4),
                P.scale(Q(-6),P.mul(P.add(P.scale(Q(2),V),[-O]),ell5)))
def main():
    for V in map(Q,(0,1,2)):
        I=2*V/15-Q(2,35);J=2*V/35-Q(2,63)
        W=P.mul(P.pw(Y,2),P.add(P.scale(-I/4,P.pw(P.add(Y,[Q(-2,3)]),2)),[-(I/9-J)/8]))
        f=P.mul(P.hull((Z,Q(1,2))),[Q(1,4)-V/4,-O,O])
        assert P.mu(P.mul(f,W))==(2*V-1)*(7*V-3)/1058400
        assert P.mu(P.mul(f,W),1)==(3*V-1)*(7*V-3)/6350400
    print('Both normalized cubic moment polynomials verified by degree-two identity.')
    # The generic reduced l functional only has 19-integral coefficients.
    assert all(z.denominator%19 for row in P.R for z in row)
    for branch,ref in (('center',[-13,16,45]),('side',[13,-21,-187,-65,372,64])):
        pp=primitive_shapes(branch,Q(5,2))
        f0=pp[-1]/ref[-1]
        assert pp==P.scale(f0,ref)
        assert f0.numerator%19 and f0.denominator%19
        assert all(a.denominator%19 for a in pp)
        vals=[sum(a*pow(t,i,19)for i,a in enumerate(ref))%19 for t in range(19)]+[ref[-1]%19]
        assert all(vals)
        print(branch,ref,'19-unit scale',f0,'projective residues',vals)
if __name__=='__main__':main()
