"""Independent stdlib check: generate unordered trees by their root branches."""
from math import prod

TABLEAUX = {
    11: ([[4], [5, 4], [4, 6, 4], [4, 9, 9, 4],
          [7, 2, 2, 2, 4], [9, 1, 1, 3, 1, 4]], [0, 0, 0, 7, 9, 7], 9),
    17: ([[8], [12, 8], [4, 3, 8], [9, 13, 12, 8],
          [6, 12, 9, 8, 8], [12, 12, 11, 13, 5, 8]], [0, 0, 0, 5, 8, 5], 16),
    187: ([[59], [148, 59], [4, 105, 59], [26, 64, 97, 59],
           [40, 46, 145, 178, 59], [97, 12, 45, 47, 56, 59]], [0, 0, 0, 73, 42, 73], 152)
}

def trees_through(n):
    trees, order, factorial = [()], [1], [1]
    for k in range(2, n + 1):
        def visit(j, left, branches):
            if not left:
                trees.append(tuple(branches))
                order.append(k)
                factorial.append(k * prod(factorial[h] for h in branches))
            else:
                while j < len(trees) and order[j] <= left:
                    visit(j, left - order[j], branches + [j])
                    j += 1
        visit(0, k - 1, [])
    return trees, order, factorial

def verify():
    trees, sizes, fac = trees_through(6)
    assert [sizes.count(k) for k in range(1, 7)] == [1, 1, 2, 4, 9, 20]
    for modulus, (A, b, seventh) in TABLEAUX.items():
        assert len(A) == len(b) == 6
        assert [len(a) for a in A] == list(range(1, 7))
        assert all(a[-1] == A[0][0] for a in A)
        assert (A[0][0] * pow(A[0][0], -1, modulus)) % modulus == 1
        branch = []
        for tree, density in zip(trees, fac):
            phi = [prod(branch[j][i] for j in tree) % modulus for i in range(6)]
            branch.append([sum(x*y for x, y in zip(a, phi)) % modulus for a in A])
            assert density * sum(x*y for x, y in zip(b, phi)) % modulus == 1
        c = [sum(a) % modulus for a in A]
        assert 7*sum(w*x**6 for w, x in zip(b, c)) % modulus == seventh
        assert ((seventh-1) * pow(seventh-1, -1, modulus)) % modulus == 1
        print(f"Z/{modulus}: 37 rooted-tree conditions passed; seventh bush = {seventh}")
    A,w,_=TABLEAUX[187]
    for p in (11,17):
        assert ([[t % p for t in a] for a in A], [t % p for t in w]) == TABLEAUX[p][:2]

if __name__ == "__main__":
    verify()
