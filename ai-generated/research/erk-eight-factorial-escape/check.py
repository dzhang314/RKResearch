"""Exact scalar receipts for PURE-HEAD-OBSTRUCTION.md; standard library only."""
from fractions import Fraction as Q

# Coordinates of the three nodal moments on (1,r,s,t,u).
M = [(Q(1,k+6), -Q(1,k+5), Q(1,k+4), Q(1,k+3), Q(1,k+2))
     for k in range(3)]

def linear_combo(weights):
    return tuple(sum(w*x for w,x in zip(weights,column)) for column in zip(*M))

assert linear_combo((1260,-5040,4200)) == (15,-12,7,0,0)
assert linear_combo((-1680,6300,-5040)) == (-10,6,0,7,0)
assert linear_combo((5040,-16800,12600)) == (15,-8,0,0,70)

# If the sum of roots is seven-integral, its residue cannot satisfy
# both of the two seven-integral elementary-symmetric identities.
assert all((12*r-15)%7 or (6*r-10)%7 for r in range(7))
# In the nonintegral case, this is the reduced polynomial after
# dividing the cleared quartic by the sum of its roots.
assert all((m*m+3*m*n+n*n)%7 for m in range(7) for n in range(1,7))
assert (120 % 7, 8 % 7) == (1,1)

# A six-site rational quadrature gives a separate sharpness example
# for this scalar support result. Never treat it as an RK tableau.
nodes = list(map(Q, ['0','-7/11','477/1796','1821/2639','41/35','1']))
weights = list(map(Q, [
    '622019131/7478792370', '-385592652577/3610108142645760',
    '7534498301755137329152/19263219522329061475515',
    '18191966663727249336671/43974089940447542430720',
    '-6584930078125/743123802553344', '845736233/6991544160',
]))
assert len(set(nodes)) == len(nodes) == len(weights) == 6 and all(weights)
def moment(k):
    return sum(w*x**k for x,w in zip(nodes,weights))
assert all(moment(k)==Q(1,k+1) for k in range(8))
assert moment(8)==Q(33971699089,306560173920)!=Q(1,9)

print('three exact nodal linear combinations and the two mod-seven residues verified')
print('six-site rational quadrature sharpness: moments 0–7 paid, degree 8 fails')
