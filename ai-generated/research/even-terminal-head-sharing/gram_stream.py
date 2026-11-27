"""Pass a literal exact JSON tableau to gram_fast.cpp without numeric conversion loss."""
import json,sys
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
t=json.load(open(sys.argv[1]))
a,w=t['a_integer'],t['b_integer'];m=t['stages']
assert m==len(a)==len(w) and all(len(r)==m for r in a)
assert all(type(v) is int for r in a for v in r) and all(type(v) is int for v in w)
print(m,t['order'],t['a_denominator'],t['b_denominator'])
for r in a:print(*r)
print(*w)
