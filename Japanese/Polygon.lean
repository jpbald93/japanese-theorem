import Japanese.Basic

/-!
# Japanese theorem for convex cyclic polygons

The vertices of the polygon are `p 0, p 1, …, p (n - 1)` (`p : ℕ → P`). They lie on a circle `s`
and are in convex position, listed counterclockwise:
`0 < ω (p b -ᵥ p a) (p c -ᵥ p a)` for all `a < b < c < n`.

**Combinatorial model.** `Triangulation i j` is a triangulation of the sub-polygon
`p i, p (i+1), …, p j`:
* `edge i : Triangulation i (i+1)` is the degenerate polygon consisting of a single side;
* `node T₁ T₂ : Triangulation i j`, with `T₁ : Triangulation i k`, `T₂ : Triangulation k j` and
  `i < k < j`, is the triangulation consisting of the triangle `(i, k, j)` on the side `ij`,
  together with triangulations of the two remaining pieces.

This is the standard description of triangulations of a convex polygon by diagonals. The side
`ij` lies in exactly one triangle `(i, k, j)` of any triangulation, and that triangle cuts the
polygon into the pieces `i..k` and `k..j`. The trees `Triangulation 0 (n-1)` are counted by the
Catalan number `C (n-2)`, which is checked numerically for `n ≤ 7` in `code/check_japanese.py`.

**Main result.** `inradiusSum_eq` shows that for every triangulation `T` of `0..n-1`, the sum of the
inradii of its triangles is `∑ d(side) - (n - 2) R`. So it does not depend on `T`
(`japanese_polygon`).
-/

open EuclideanGeometry Module
open scoped RealInnerProductSpace

namespace Japanese

/-- Triangulations of the convex polygon with vertices `i, i+1, …, j`. -/
inductive Triangulation : ℕ → ℕ → Type
  | edge (i : ℕ) : Triangulation i (i + 1)
  | node {i k j : ℕ} (hik : i < k) (hkj : k < j) :
      Triangulation i k → Triangulation k j → Triangulation i j

namespace Triangulation

/-- The triangles `(a, b, c)` (with `a < b < c`) of a triangulation. -/
def triangles : {i j : ℕ} → Triangulation i j → List (ℕ × ℕ × ℕ)
  | _, _, edge _ => []
  | i, j, @node _ k _ _ _ T₁ T₂ => (i, k, j) :: (T₁.triangles ++ T₂.triangles)

/-- The number of triangles is `j - i - 1`. -/
theorem length_triangles : {i j : ℕ} → (T : Triangulation i j) →
    T.triangles.length = j - i - 1
  | _, _, edge _ => by simp [triangles]
  | _, _, node hik hkj T₁ T₂ => by
    simp only [triangles, List.length_cons, List.length_append, length_triangles T₁,
      length_triangles T₂]
    omega

theorem lt_of_triangulation : {i j : ℕ} → Triangulation i j → i < j
  | _, _, edge _ => Nat.lt_succ_self _
  | _, _, node hik hkj _ _ => hik.trans hkj

/-- Fan triangulation of `i..j` from the vertex `i`. -/
def fan (i : ℕ) : (m : ℕ) → Triangulation i (i + m + 1)
  | 0 => edge i
  | m + 1 => node (k := i + m + 1) (by omega) (by omega) (fan i m) (edge _)

/-- Fan triangulation of `i..j` from the vertex `j`. -/
def fan' (j : ℕ) : (m : ℕ) → Triangulation j (j + m + 1)
  | 0 => edge j
  | m + 1 => node (k := j + 1) (by omega) (by omega) (edge j)
      (by have := fan' (j + 1) m; rwa [show j + 1 + m + 1 = j + (m + 1) + 1 by omega] at this)

end Triangulation

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Sum of the inradii of the triangles of `T`, for the vertex map `p`. -/
noncomputable def inradiusSum (p : ℕ → P) {i j : ℕ} (T : Triangulation i j) : ℝ :=
  (T.triangles.map fun t => triInradius (p t.1) (p t.2.1) (p t.2.2)).sum

omit [Fact (finrank ℝ V = 2)] in
@[simp] lemma inradiusSum_edge (p : ℕ → P) (i : ℕ) :
    inradiusSum p (Triangulation.edge i) = 0 := by
  simp [inradiusSum, Triangulation.triangles]

omit [Fact (finrank ℝ V = 2)] in
lemma inradiusSum_node (p : ℕ → P) {i k j : ℕ} (hik : i < k) (hkj : k < j)
    (T₁ : Triangulation i k) (T₂ : Triangulation k j) :
    inradiusSum p (Triangulation.node hik hkj T₁ T₂) =
      triInradius (p i) (p k) (p j) + inradiusSum p T₁ + inradiusSum p T₂ := by
  simp [inradiusSum, Triangulation.triangles, add_assoc]

/-- Sum of the signed distances from `O` to the sides `p l → p (l+1)`, for `i ≤ l < j`. -/
noncomputable def chainDist (O : P) (p : ℕ → P) (i j : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico i j, chordDist o O (p l) (p (l + 1))

/-- **Japanese theorem, explicit form.** For every triangulation `T` of the sub-polygon `i..j` of
a convex cyclic polygon, the sum of the inradii is the sum of the signed distances from the
centre to the sides `i → i+1 → ⋯ → j → i`, minus `(j - i - 1) R`. -/
theorem inradiusSum_eq (s : Sphere P) (p : ℕ → P) (n : ℕ) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a)) :
    {i j : ℕ} → (T : Triangulation i j) → j < n →
      inradiusSum p T = chainDist o s.center p i j + chordDist o s.center (p j) (p i) -
        ((j - i - 1 : ℕ) : ℝ) * s.radius
  | _, _, Triangulation.edge i, _ => by
    simp [chainDist, chordDist_swap o s.center (p (i + 1)) (p i)]
  | i, j, Triangulation.node (k := k) hik hkj T₁ T₂, hj => by
    rw [inradiusSum_node, inradiusSum_eq s p n hs hconv T₁ (by omega),
      inradiusSum_eq s p n hs hconv T₂ hj,
      triInradius_eq o s (hs i (by omega)) (hs k (by omega)) (hs j hj)
        (hconv i k j hik hkj hj),
      chordDist_swap o s.center (p i) (p k), chordDist_swap o s.center (p k) (p j), chainDist,
      chainDist, chainDist, ← Finset.sum_Ico_consecutive _ hik.le hkj.le]
    have e : ((j - i - 1 : ℕ) : ℝ) = ((k - i - 1 : ℕ) : ℝ) + ((j - k - 1 : ℕ) : ℝ) + 1 := by
      rw [show j - i - 1 = (k - i - 1) + (j - k - 1) + 1 by omega]
      push_cast; ring
    rw [e]
    ring

/-- **Japanese theorem for convex cyclic polygons.** The polygon `p 0, …, p (n-1)` is inscribed
in the circle `s` and is convex, listed counterclockwise. Every triangulation of it has inradius sum
`∑ d(side) - (n - 2) R`. -/
theorem inradiusSum_polygon (s : Sphere P) (p : ℕ → P) (n : ℕ) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    (T : Triangulation 0 (n - 1)) :
    inradiusSum p T = chainDist o s.center p 0 (n - 1) + chordDist o s.center (p (n - 1)) (p 0) -
      ((n - 2 : ℕ) : ℝ) * s.radius := by
  have h := T.lt_of_triangulation
  rw [inradiusSum_eq o s p n hs hconv T (by omega)]
  congr 3

/-- **Japanese theorem for convex cyclic polygons.** Any two triangulations of a convex polygon
inscribed in a circle have the same sum of inradii. -/
theorem japanese_polygon (s : Sphere P) (p : ℕ → P) (n : ℕ) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    (T T' : Triangulation 0 (n - 1)) :
    inradiusSum p T = inradiusSum p T' := by
  rw [inradiusSum_polygon o s p n hs hconv T, inradiusSum_polygon o s p n hs hconv T']

/-- The same statement for triangulations of any sub-polygon `i..j`. -/
theorem japanese_subpolygon (s : Sphere P) (p : ℕ → P) (n : ℕ) (hs : ∀ l < n, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < n → 0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a))
    {i j : ℕ} (hj : j < n) (T T' : Triangulation i j) :
    inradiusSum p T = inradiusSum p T' := by
  rw [inradiusSum_eq o s p n hs hconv T hj, inradiusSum_eq o s p n hs hconv T' hj]

/-- Fans from the first and the last vertex give the same inradius sum. -/
theorem japanese_fans (s : Sphere P) (p : ℕ → P) (m : ℕ) (hs : ∀ l < m + 2, p l ∈ s)
    (hconv : ∀ a b c, a < b → b < c → c < m + 2 →
      0 < o.areaForm (p b -ᵥ p a) (p c -ᵥ p a)) :
    inradiusSum p (Triangulation.fan 0 m) = inradiusSum p (Triangulation.fan' 0 m) :=
  japanese_subpolygon o s p (m + 2) hs hconv (by omega) _ _

end Japanese
