"""Brute-force check of the Lean definition `IsTriangulation 0 (n-1) E` (Combinatorial.lean):
E = a maximal set of pairwise non-crossing chords (a,b), 0 <= a < b <= n-1.
For n = 2..8 enumerate ALL subsets of chords, keep the maximal non-crossing ones, and check:
  * their number is Catalan(n-2);
  * they coincide with the chord sets of the recursive trees (`Triangulation.chords`);
  * `triangleSet E` has n-2 triangles and equals the tree's triangle list.
"""
from itertools import combinations
from math import comb

def crosses(e, f):
    (a, b), (c, d) = e, f
    return (a < c < b < d) or (c < a < d < b)

def trees(i, j):
    """(chords, triangles) of every tree triangulation of i..j (mirrors Triangulation)."""
    if j == i + 1:
        return [(frozenset({(i, j)}), [])]
    out = []
    for k in range(i + 1, j):
        for c1, t1 in trees(i, k):
            for c2, t2 in trees(k, j):
                out.append((frozenset({(i, j)}) | c1 | c2, [(i, k, j)] + t1 + t2))
    return out

def triangle_set(E):
    return {(a, b, c) for (a, b) in E for (b2, c) in E if b2 == b and (a, c) in E}

def maximal_noncrossing(n):
    chords = [(a, b) for a in range(n) for b in range(a + 1, n)]
    m = len(chords)
    res = []
    # enumerate non-crossing sets by backtracking, keep maximal ones
    def rec(idx, cur):
        if idx == m:
            if all(c in cur or any(crosses(c, f) for f in cur) for c in chords):
                res.append(frozenset(cur))
            return
        c = chords[idx]
        if not any(crosses(c, f) for f in cur):
            cur.append(c); rec(idx + 1, cur); cur.pop()
        rec(idx + 1, cur)
    rec(0, [])
    return res

catalan = lambda k: comb(2 * k, k) // (k + 1)
ok = True
for n in range(2, 9):
    M = maximal_noncrossing(n)
    T = trees(0, n - 1)
    Ms, Ts = set(M), {c for c, _ in T}
    good = (len(M) == catalan(n - 2) == len(T) == len(Ts)) and Ms == Ts
    for c, tris in T:
        ts = triangle_set(c)
        good &= (ts == set(tris)) and len(ts) == n - 2 == len(tris)
    print(f"n={n}: maximal non-crossing sets = {len(M)}, trees = {len(T)}, "
          f"Catalan({n-2}) = {catalan(n-2)}, sets equal: {Ms == Ts}, ok={good}")
    ok &= good
print("ALL OK" if ok else "FAIL")
