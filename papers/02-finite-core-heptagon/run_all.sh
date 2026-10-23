#!/bin/sh
# Regenerate the outputs of paper 2 (finite-core heptagon).
#   sh run_all.sh          full run (several hours on one machine; writes outputs/*.out)
#   sh run_all.sh --fast   reduced run (minutes; writes outputs/fast/*.out, never overwrites the full records)
# Referee outputs (outputs/ref_*.out, heff_check.out, ref_fitfreq.out) are recorded, not rerun.
# Python: numpy, scipy, sympy, mpmath, matplotlib.  Lean: elan toolchain, see ../../lean.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
PY=${PY:-python3}
cd "$HERE/code"
if [ "$1" = "--fast" ]; then
  OUT="$HERE/outputs/fast"; mkdir -p "$OUT"
  $PY tsums.py                      > "$OUT/tsums.out"
  $PY -c "import blocks; b = blocks.block('plane', 7, 3); print('N=7 m=3:', b['ss'], b['tt'], b['varpi'], 'Omega1 =', b['Omega1'])" > "$OUT/blocks.out"
  $PY curved.py                     > "$OUT/curved.out"
  $PY cd_asymptotics.py --fast      > "$OUT/cd_asymptotics.out"
  $PY cd_heptagon_scan.py --fast    > "$OUT/cd_heptagon_scan.out"
  $PY tanh_check.py --fast          > "$OUT/tanh_check.out"
  $PY frozen_check.py               > "$OUT/frozen_check.out"
  $PY figures.py --fast             > "$OUT/figures.out"   # writes outputs/fast/figures/, not paper/figures/
else
  OUT="$HERE/outputs"
  $PY tsums.py                      > "$OUT/tsums.out"
  $PY blocks.py                     > "$OUT/blocks.out"
  $PY plane_general.py              > "$OUT/plane_general.out"
  $PY curved.py                     > "$OUT/curved.out"
  $PY curved_general.py             > "$OUT/curved_general.out"
  $PY tanh_check.py                 > "$OUT/tanh_check.out"
  $PY cd_asymptotics.py             > "$OUT/cd_asymptotics.out"
  $PY cd_heptagon_scan.py           > "$OUT/cd_heptagon_scan.out"
  $PY cd_onset_modes.py             > "$OUT/cd_onset_modes.out"
  $PY cd_onset_m1.py                > "$OUT/cd_onset_m1.out"
  $PY frozen_check.py               > "$OUT/frozen_check.out"
  $PY ngon_reviewer.py 0.2 64 7     > "$OUT/ngon_reviewer_a020.out"
  $PY ngon_reviewer.py 0.2 96 7     >> "$OUT/ngon_reviewer_a020.out"
  $PY figures.py                    > "$OUT/figures.out"
  # rebuild the paper after the figures
  (cd "$HERE/paper" && pdflatex -interaction=nonstopmode main.tex >/dev/null && bibtex main >/dev/null && pdflatex -interaction=nonstopmode main.tex >/dev/null && pdflatex -interaction=nonstopmode main.tex > "$OUT/latex.out" 2>&1) || echo "LaTeX build failed"
fi
# Lean: build the library and record the axiom audit
if command -v lake >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
  cd "$HERE/../../lean"
  lake build Heptagon > "$OUT/lean_build.out" 2>&1
  lake env lean Heptagon/Audit.lean > "$OUT/lean_axioms.out" 2>&1
fi
echo "done: outputs in $OUT"
