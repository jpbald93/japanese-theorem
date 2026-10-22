#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED declaration, and each report is present exactly once;
#  * each REQUIRED declaration (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# REQUIRED lists every declaration cited in the accompanying paper, plus the declarations queried
# during development; names are fully qualified. Definitions may use a subset of the three axioms.
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED ones.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
LIB="Japanese"
REQUIRED="Carnot.carnot Carnot.carnot_poly Carnot.carnot_sum Carnot.cos_add_cos_add_cos Carnot.frame_data Carnot.height_sq_mul_sq Carnot.signedSideDist Carnot.signedSideDist_affineCombination Carnot.signedSideDist_circumcenter_eq Carnot.signedSideDist_eq_signedInfDist Carnot.signedSideDist_incenter Carnot.signedSideDist_point_self Japanese.Crosses Japanese.IsGeomTriangulation Japanese.IsTriangulation Japanese.IsTriangulation.card_triangleSet Japanese.IsTriangulation.exists_apex Japanese.IsTriangulation.exists_tree Japanese.IsTriangulation.exists_tree_triangles Japanese.Triangulation.chords Japanese.Triangulation.chords_injective Japanese.Triangulation.isTriangulation Japanese.Triangulation.length_triangles Japanese.Triangulation.toFinset_triangles Japanese.Triangulation.triangles Japanese.chordDist Japanese.chordDist_swap Japanese.diagonal_signedSideDist_cancel Japanese.exists_sbtw_sbtw_of_areaForm Japanese.geomCrosses_iff Japanese.inradiusSum_eq Japanese.inradiusSum_eq_triangleInradiusSum Japanese.inradiusSum_polygon Japanese.isGeomTriangulation_iff Japanese.isTriangulation_iff_exists_tree Japanese.japanese_fans Japanese.japanese_polygon Japanese.japanese_polygon_combinatorial Japanese.japanese_polygon_geometric Japanese.japanese_quadrilateral Japanese.japanese_subpolygon Japanese.not_sbtw_sbtw_of_ne_zero Japanese.not_wbtw_wbtw_of_pos Japanese.quadrilateral_inradius_sum Japanese.sbtw_inter_iff_interleave Japanese.signedSideDist_eq_chordDist Japanese.treeEquiv Japanese.triInradius Japanese.triInradius_eq Japanese.triangleInradiusSum_eq Japanese.triangleSet Japanese.l14b_triInradius_eq Japanese.l14_triInradius_eq Japanese.l14_japanese_quadrilateral Japanese.l14b_isGeomTriangulation_iff Japanese.l14b_triangleInradiusSum_eq Japanese.l14_japanese_polygon Japanese.l14b_norm Japanese.l14b_mem_unit Japanese.l14b_indep Japanese.l14b_quad_pos Japanese.l14w_japanese_quadrilateral Japanese.l14b_quad Japanese.l14b_quad_conv Japanese.l14b_quad_tri Japanese.l14b_isTri_iff Japanese.l14w_japanese_polygon Japanese.Classical.triInradius_eq_repo Japanese.Classical.triInradius_eq_zero_left Japanese.Classical.triInradius_eq_zero_right Japanese.Classical.areaForm_ne_zero_of_affineIndependent Japanese.Classical.quad_signs Japanese.Classical.cov_TriSimplex4_b_part Japanese.Classical.not_classical_TriSimplex4_b_obligation Japanese.Classical.not_classical_TriSimplex4_b_rectangle Japanese.Classical.cov_TriSimplex4_b_obligation_part Japanese.Classical.not_wbtw_of_isConvexPolygon Japanese.Classical.cov_TriSimplex4_a_obligation Japanese.Classical.cov_TriSimplex4_a_part Japanese.Classical.triInradius_subtype Japanese.Classical.cov_TriSimplex4_b"
SOURCES="$(find $LIB -name '*.lean' | sort | tr '\n' ' ') $LIB.lean"
[ -e .lake/packages/mathlib ] || lake exe cache get || { echo "FAIL: could not fetch Mathlib cache"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
