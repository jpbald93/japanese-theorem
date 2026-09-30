"""Numeric check of the Japanese theorem and of the chord-distance formula used in Lean.

For random convex cyclic n-gons (n = 4..7) we enumerate all triangulations and check that:
  * the sum of inradii is the same for all of them;
  * each equals sum_i d(P_i P_{i+1}) - (n-2) R, where d is the signed distance from the centre
    to the directed side, positive to the left (the polygon is counterclockwise);
  * the per-triangle formula r = d(ab) + d(bc) + d(ca) - R holds for CCW triangles;
  * d(q, p) = -d(p, q).
"""
import math
import random
from functools import lru_cache


def inradius(a, b, c):
    la, lb, lc = math.dist(b, c), math.dist(a, c), math.dist(a, b)
    s = (la + lb + lc) / 2
    area = abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])) / 2
    return area / s


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]


def chord(O, p, q):
    return cross((q[0] - p[0], q[1] - p[1]), (O[0] - p[0], O[1] - p[1])) / math.dist(p, q)


def triangulations(i, j):
    """All triangulations of the sub-polygon i..j, as lists of triangles."""
    if j - i < 2:
        return [[]]
    out = []
    for k in range(i + 1, j):
        for L in triangulations(i, k):
            for R in triangulations(k, j):
                out.append(L + R + [(i, k, j)])
    return out


def catalan(m):
    return math.comb(2 * m, m) // (m + 1)


def main():
    rng = random.Random(20260930)
    worst = 0.0
    total = 0
    for n in range(4, 8):
        tris = triangulations(0, n - 1)
        assert len(tris) == catalan(n - 2), (n, len(tris))
        for _ in range(200):
            O = (rng.uniform(-3, 3), rng.uniform(-3, 3))
            R = rng.uniform(0.5, 4)
            angs = sorted(rng.uniform(0, 2 * math.pi) for _ in range(n))
            P = [(O[0] + R * math.cos(t), O[1] + R * math.sin(t)) for t in angs]
            side = sum(chord(O, P[i], P[(i + 1) % n]) for i in range(n)) - (n - 2) * R
            for T in tris:
                s = 0.0
                for (a, b, c) in T:
                    r = inradius(P[a], P[b], P[c])
                    rc = chord(O, P[a], P[b]) + chord(O, P[b], P[c]) + chord(O, P[c], P[a]) - R
                    worst = max(worst, abs(r - rc) / R)
                    worst = max(worst, abs(chord(O, P[b], P[a]) + chord(O, P[a], P[b])) / R)
                    s += r
                worst = max(worst, abs(s - side) / R)
                total += 1
        print(f"n={n}: {len(tris)} triangulations x 200 polygons checked")
    print(f"total triangulations checked: {total}, max relative error: {worst:.3e}")
    assert worst < 1e-9
    print("OK")


if __name__ == "__main__":
    main()
