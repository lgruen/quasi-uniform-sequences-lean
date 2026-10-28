#!/bin/sh
# Second audit: recompute tab:residue (lambda_jit^2 exact; exhaustive where the table says E) and the Korobov column.
J=${JIT:-bin/audit2_jit}   # compiled binary of audit2_jit.cpp
echo "== eval listed vectors"
$J eval 11 2 3; $J eval 17 2 4; $J eval 37 2 6; $J eval 101 2 30; $J eval 1009 2 122
$J eval 11 3 9 4; $J eval 17 3 6 2; $J eval 37 3 9 3; $J eval 101 3 35 13; $J eval 1009 3 105 11; $J eval 10007 3 7775 9087
$J eval 17 4 9 15 4; $J eval 37 4 14 4 2; $J eval 101 4 27 9 3; $J eval 1009 4 443 201 758
$J eval 37 5 16 8 4 2; $J eval 101 5 2 4 8 16; $J eval 1009 5 560 313 92 858
echo "== Korobov (rho, rho^2, .., -1)"
for ps in "11 2 3" "17 2 4" "37 2 6" "101 2 10" "1009 2 31" "11 3 2 4" "17 3 2 4" "37 3 3 9" "101 3 4 16" "1009 3 10 100" "10007 3 21 441" \
          "17 4 2 4 8" "37 4 2 4 8" "101 4 3 9 27" "1009 4 5 25 125" "37 5 2 4 8 16" "101 5 2 4 8 16" "1009 5 3 9 27 81"; do
  set -- $ps; echo "p=$1 s=$2: $($J eval $ps)"; done
echo "== exhaustive (E rows)"
for ps in "11 2" "17 2" "37 2" "101 2" "1009 2" "11 3" "17 3" "37 3" "101 3" "1009 3" "17 4" "37 4" "101 4" "37 5"; do
  echo "p,s=$ps: $($J exh $ps)"; done
