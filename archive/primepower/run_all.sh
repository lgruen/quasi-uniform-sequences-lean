#!/bin/sh
# run_all.sh -- driver for the three programs of Table tab:primepower (from the archive root: sh primepower/run_all.sh).
# Compiles audit_fq.cpp into bin/. No mathematics of its own.
set -e
mkdir -p bin; [ -x bin/audit_fq ] || g++ -O2 -std=c++17 -o bin/audit_fq primepower/audit_fq.cpp
echo "== (1) original program: best beta_q over all weights, smallest monic irreducible f (p r s)"
for prs in "2 3 2" "3 2 2" "2 4 2" "5 2 2" "3 3 2" "7 2 2" "5 2 3" "2 5 3" "7 2 3" "2 6 3" "3 4 3" "11 2 3" "5 3 3"; do
  python3 primepower/original_fq_residue.py $prs; done
echo "== (2) audit: every monic irreducible f (power-basis encoding), exhaustive over the weights (p r f s)"
for prs in "2 3 2" "3 2 2" "2 4 2" "5 2 2" "3 3 2" "7 2 2" "5 2 3" "2 5 3" "7 2 3" "2 6 3" "3 4 3" "11 2 3" "5 3 3" \
           "2 3 3" "3 2 3" "2 4 3" "3 3 3"; do
  set -- $prs; ./bin/audit_fq $1 $2 all $3 beta; done
echo "== (3) second audit: beta_q at the weights of the table rows (beta*q printed)"
python3 primepower/audit2_primepower.py rows
