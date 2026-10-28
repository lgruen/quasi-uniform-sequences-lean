#!/bin/bash
# camp3.sh p profile count seed mode wmax Lmax [kmult] : random frames (gen3), every coordinate as c0, checker u3
# (the second, independent pipeline of the research repository is skipped when absent; its counts then stay 0)
p=$1; prof=$2; cnt=$3; seed=$4; mode=$5; wmax=$6; Lmax=$7; km=${8:-1}
D=${BIN:-bin}; DEG=${DEG:-none}   # D: directory of the compiled gen3/u3; DEG: optional second pipeline (not archived)
n=0; pass=0; fail=0; nr=0; hwok=0; hwbad=0; hwskip=0; wsum=0
for fr in $($D/gen3 $p $prof $cnt $seed $mode); do
  IFS=';' read -ra BS <<< "$fr"; s=${#BS[@]}
  for ((c0=0;c0<s;c0++)); do n=$((n+1))
    out=$($D/u3 $p "$fr" $c0 $wmax $Lmax $km)
    nw=$(echo "$out" | grep -c "^w=.*patterns OK"); wsum=$((wsum+nw))
    if echo "$out" | grep -q "RESULT FAIL"; then fail=$((fail+1)); echo "U3FAIL $fr c0=$c0"; echo "$out"; 
    elif [ "$nw" -eq 0 ]; then nr=$((nr+1)); echo "NOTRUN $fr c0=$c0 $(echo "$out" | head -1)";
    else pass=$((pass+1)); fi
    if [ "$km" = "1" ] && [ -x "$DEG/runU.sh" ]; then
      ho=$(cd $DEG && ./runU.sh $p "$fr" $c0 $wmax 4000 2>&1)
      if echo "$ho" | grep -q SKIP; then hwskip=$((hwskip+1)); else
        nl=$(echo "$ho" | grep -c "^w=.*OK.*patterns OK"); nv=$(echo "$ho" | grep -c "VIOLATION\|FAIL"); if [ "$nv" -eq 0 ] && [ "$nl" -ge 1 ]; then hwok=$((hwok+1)); else hwbad=$((hwbad+1)); echo "HWBAD $fr c0=$c0"; echo "$ho" | head -5; fi; fi
    fi
  done
done
echo "SUMMARY p=$p prof=$prof mode=$mode cnt=$cnt seed=$seed kmult=$km : cases=$n u3pass=$pass u3fail=$fail u3notrun=$nr levels_verified=$wsum | hw: ok=$hwok bad=$hwbad skip=$hwskip"
