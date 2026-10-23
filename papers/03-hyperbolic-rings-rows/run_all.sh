#!/bin/sh
# Regenerate every output of paper 3 into outputs/<script>.out.
#   sh run_all.sh          all scripts
#   sh run_all.sh --fast   skip the scripts that take more than about 5 minutes
# Python: PY (default python3) with numpy, scipy, sympy, mpmath, python-flint, matplotlib.
set -e
cd "$(dirname "$0")"
PY=${PY:-python3}
FAST=0; [ "$1" = "--fast" ] && FAST=1
run () { echo "== $1"; s=$(date +%s); "$PY" code/$1.py > outputs/$1.out 2>&1; echo "   done in $(( $(date +%s) - s )) s"; }
# Rings: certified thresholds, Krein windows, blocks check, large N, second order
run tanh_threshold_polys
run tanh_krein
run tanh_large_n
run blocks
run boatto_map_and_verify
run ring_row_germs
run b4_varsigma
run b7_curves
run b8_flat
# Rows: exact symbol and its identities, threshold series, horocycle limit
run rows_symbol
run rows_fpi
run single_root_cert
run region_C_cert
run dual_series_check
run kappa_c_check
if [ $FAST = 0 ]; then
  run tanh_blocks_fd
  run tanh_extras
  run rows_thresholds
  run rows_screened
fi
run make_figures
