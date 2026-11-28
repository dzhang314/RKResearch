"""The exact incompatible scalars for two literal singleton star tails."""
from fractions import Fraction as Q
s=Q(156,49)
c=lambda a:a*a-Q(24,7)*a+Q(48,35)
assert c(1)==-Q(37,35)
assert c(s)==Q(7104,12005)
assert c(1)*(2-s)**2==-Q(124468,84035)
assert c(s)-c(1)*(2-s)**2==Q(174196,84035)
print('double-star necessary discrepancy:', Q(174196,84035))
