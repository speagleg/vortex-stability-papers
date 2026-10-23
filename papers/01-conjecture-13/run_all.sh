#!/bin/sh
# Regenerate outputs/ for paper 01-conjecture-13.  Usage: sh run_all.sh [--fast]
# --fast skips jobs over ~5 minutes (spectral_check, c4_levelset, c4_table_modular_check, c4_slice, n8_integration).
# Interpreter: $PY (default python3) with numpy, scipy, sympy, mpmath, python-flint, matplotlib.
set -e
PY=${PY:-python3}
cd "$(dirname "$0")"
mkdir -p outputs paper/figures
run() { echo "== $1"; "$PY" -I code/$1 $2 > outputs/${1%.py}${3}.out 2>&1; }
run threshold.py
run c4_closed_forms.py
run mt_line_vs_levelset.py
run even_exact.py
run make_figures.py
if [ "$1" != "--fast" ]; then
  run spectral_check.py
  run c4_levelset.py
  run c4_table_modular_check.py
  run c4_slice.py
  run n8_integration.py sinh _sinh
fi
echo "Lean: (cd ../../lean && lake build Conj13 && lake env lean Conj13/Audit.lean > ../papers/01-conjecture-13/outputs/lean_axioms.out)"
