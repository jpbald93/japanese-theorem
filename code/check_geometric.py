# Numeric check: for random strictly convex CCW polygons, open segments (p_a,p_b), (p_c,p_d)
# intersect iff indices interleave (disjoint endpoints), and never for shared endpoints.
import random, math
from fractions import Fraction as F
def area(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def open_cross(P,Q,R,S):
    # exact rational sign test: open segments PQ, RS share a point iff each pair of endpoints is strictly
    # on opposite sides of the other line (valid here: no three vertices collinear)
    d1,d2=area(P,Q,R),area(P,Q,S); d3,d4=area(R,S,P),area(R,S,Q)
    if d1==0 and d2==0: raise Exception("collinear")
    return d1*d2<0 and d3*d4<0
random.seed(1); total=0; bad=0; polys=0
for trial in range(400):
    n=random.randint(4,10)
    angs=sorted(random.uniform(0,2*math.pi) for _ in range(n))
    r=random.uniform(0.5,3)
    pts=[(F(round(r*math.cos(t)*10**6),10**6),F(round(r*math.sin(t)*10**6),10**6)) for t in angs]
    if not all(area(pts[a],pts[b],pts[c])>0 for a in range(n) for b in range(a+1,n) for c in range(b+1,n)): continue
    polys+=1
    for a in range(n):
        for b in range(a+1,n):
            for c in range(n):
                for d in range(c+1,n):
                    if (a,b)==(c,d): continue
                    g=open_cross(pts[a],pts[b],pts[c],pts[d])
                    comb=(a<c<b<d) or (c<a<d<b)
                    total+=1
                    if g!=comb: bad+=1; print("MISMATCH",n,a,b,c,d)
print(f"convex polygons tested: {polys}, ordered chord pairs: {total}, mismatches: {bad}")
print("ALL OK" if bad==0 else "FAIL")
