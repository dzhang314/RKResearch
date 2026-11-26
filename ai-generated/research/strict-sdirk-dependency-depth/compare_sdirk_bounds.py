"""Compare *published* strict SDIRK upper rows to exact layered widths.
No search, proof replay, compiler, or dependencies beyond the standard library.
Usage: python3 compare_sdirk_bounds.py /path/to/the/published/RKResearch
"""
from hashlib import sha256
from pathlib import Path
import re
import sys

UPPER = ("ai-generated/upper-bounds/README.md",
         "12ff9487727c1ddaca2268a0f13d3b8c136189f2698bf4f5444bea7c806492d8")
CURRENT = ("ai-generated/CURRENT.md",
           "77375e78109a96fa3aab205444c9e2a3a5c839868cef90ab5307c6774218a783")
TABLE_ROW = re.compile(r"^\|\s*(\d+)\s*\|[^|]+\|[^|]+\|([^|]+)\|\s*$")
ENTRY = re.compile(r"^(?:[0-9]+[–-])?([0-9]+)$")

def require(condition, reason):
    if not condition:
        raise SystemExit(reason)

def table(root, pin):
    relative, digest = pin
    raw = (root / relative).read_bytes()
    require(sha256(raw).hexdigest() == digest, f"source SHA-256 mismatch: {relative}")
    result = {}
    for line in raw.decode().splitlines():
        match = TABLE_ROW.match(line)
        if not match:
            continue
        p, entry = int(match[1]), ENTRY.fullmatch(match[2].strip())
        require(entry is not None and p not in result, f"malformed numeric row: {line}")
        result[p] = int(entry[1])
    require(list(result) == list(range(1, 21)), f"wrong order rows: {relative}")
    return result

def full_layer_total(p, q, D):
    L = p - D
    return 1 + sum(min(q, L+h) for h in range(1, D+1))

def one_degree(p, q, D, allows_linear):
    L = p - D
    saving = sum(
        3 <= L+h <= q or (L+h == 2 <= q and allows_linear)
        for h in range(1, D)
    )
    return full_layer_total(p, q, D) - saving

def rows(pub):
    yield (1, "-", pub[1], "-", "-", "-", "-", "-", "-", "-")
    first_gains = []
    for p in range(2, 21):
        q = (p+1)//2
        full = full_layer_total(p, q, p-1)
        require(full == p*q-q*(q-1)//2, f"full count p={p}")
        one_any = one_degree(p, q, p-1, False)
        one_matched = one_degree(p, q, p-1, True)
        require(one_any == full-max(0, q-2), f"one-degree generic count p={p}")
        require(one_matched == full-q+1, f"one-degree matched count p={p}")
        higher = sum(min(q, (2*s+1)//3) for s in range(1, p+1))
        N = (3*q-2)//2
        u, a = divmod(N, 3)
        require(higher == (p-N)*q+3*u*u+u+a*(2*u+1), f"higher count p={p}")
        if p == 2:
            full_exception = one_exception = 1  # separate implicit-midpoint case
        else:
            full_exception = full_layer_total(p, q, p-2)
            one_exception = one_degree(p, q, p-2, False)
            require(full_exception == full-2, f"full exceptional count p={p}")
            require(one_exception == full-q, f"one-degree exceptional count p={p}")
        gain = one_matched-higher
        if gain > 0:
            first_gains.append(p)
        require(gain >= 0 and higher > pub[p], f"unexpected comparison p={p}")
        yield (p, q, pub[p], full, one_any, one_matched, higher, gain,
               full_exception, one_exception)
    require(first_gains == list(range(7, 21)), "wrong range of matched gains")

def main():
    require(len(sys.argv) == 2, __doc__.strip())
    root = Path(sys.argv[1])
    pub = table(root, UPPER)
    require(pub == table(root, CURRENT), "published tables disagree")
    header = ("p", "min_real_output_q", "published_free_upper",
              "depth_pminus1_published_full",
              "depth_pminus1_published_one_degree_without_linear_loss",
              "depth_pminus1_published_one_degree_matched",
              "depth_pminus1_higher_budget_matched", "matched_one_degree_gain",
              "depth_pminus2_published_full", "depth_pminus2_published_one_degree")
    print("\t".join(header))
    for row in rows(pub):
        print("\t".join(map(str, row)))

if __name__ == "__main__":
    main()
