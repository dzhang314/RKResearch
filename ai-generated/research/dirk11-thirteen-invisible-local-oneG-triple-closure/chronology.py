"""Independent enumeration of the literal one-label triple chronology."""
from collections import Counter, defaultdict
# X is the triple. A,B,C are the marked pairs indexed by debut, not clock
# magnitude. S is the unmarked singleton. Endpoints and dirty j are outside.
target={"X":3, "A":2, "B":2, "C":2, "S":1}
def words(w=("X",), counts=Counter(X=1), born=0):
    if len(w)==10:
        assert counts==target
        yield w
        return
    for k in target:
        if counts[k]==target[k]:
            continue
        add=0
        if k in "ABC" and not counts[k]:
            if k!="ABC"[born]:
                continue
            add=1
        v=counts.copy()
        v[k]+=1
        yield from words(w+(k,),v,born+add)

c=Counter(); rows=defaultdict(set)
prefixes={"early":tuple("XAXBC"),
          "middle":tuple("XABXC"),"late":tuple("XABCX")}
for w in words():
    assert w[0]=="X" and w.index("A")<w.index("B")<w.index("C")
    x2=w.index("X",1)
    de=sorted(w.index(k) for k in target)
    if x2==1:
        key="before other"
    elif x2<de[2]:
        key="early"
    elif x2<de[3]:
        key="middle"
    else:
        key="late"
    c[key]+=1
    if key in prefixes and w[:5]==prefixes[key]:
        rows[key].add(w[5])
assert sum(c.values())==3780 and set(c)=={"before other","early","middle","late"}
assert rows=={k:set(target) for k in prefixes}
for k,n in sorted(c.items()):
    suffix = ["surviving-prefix next labels", "".join(sorted(rows[k]))] if k in rows else []
    print(k,n,*suffix)
print("Exact marked-triple census: 3,780 literal words, and all five next-event fibres at each paid driver prefix")
