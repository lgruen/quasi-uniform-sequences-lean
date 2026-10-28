#!/bin/bash
# campaign.sh P [COUNT=2] [SEED=1] -- driver: runs camp3.sh on the frame profiles (base degrees, generator mode) of the
# audit campaign behind Corollary cor:halton for the prime P, COUNT random frames per profile, every coordinate as the
# carrying coordinate c0, levels w = 0, 1 (L <= 12000). Compiles gen3.cpp and u3.cpp into bin/ on first use.
# From the archive root:  bash failure/campaign.sh 2; ... ; bash failure/campaign.sh 13   (one prime per call, < 30 s)
P=$1; CNT=${2:-2}; SEED=${3:-1}
mkdir -p bin
[ -x bin/gen3 ] || g++ -O2 -std=c++17 -o bin/gen3 failure/gen3.cpp
[ -x bin/u3 ] || g++ -O2 -std=c++17 -o bin/u3 failure/u3.cpp
case $P in
  2)  PROFS="1,1,2:0 2,3:1 2,4:1 3,4:0 4,4:0 4,3:2 1,2,3:0 1,1,2,3:0 1,1,2,3,3:0" ;;
  3)  PROFS="1,1,2:1 4,2:1 3,3:2 4,1:2 2,1,1:3 3,4:0 4,4:1 1,2,3:0 2,2,2,2:0 2,2,2:1" ;;
  5)  PROFS="1,1,1,1,1:0 1,1,1,1:0 2,2:1 4,1:2 3,2:2 2,1,1,1:3 3,3:1 4,2:0" ;;
  7)  PROFS="1,1,1,1,1:0 1,1,1:0 2,2:1 3,1:2 2,1,1,1:3 3,2:0" ;;
  11) PROFS="1,1,1,1,1:0 1,1,1:0 2,1:2 2,1,1:3 2,2:1" ;;
  13) PROFS="1,1,1,1,1:0 1,1:0 2,1:2 2,1,1,1:3 2,2:1" ;;
  *) echo "P must be one of 2 3 5 7 11 13"; exit 1 ;;
esac
tc=0; tp=0; tf=0; tn=0
for pm in $PROFS; do
  prof=${pm%:*}; mode=${pm#*:}
  line=$(BIN=bin bash failure/camp3.sh $P "$prof" $CNT $SEED $mode 1 12000 | tee /dev/stderr | grep '^SUMMARY')
  c=$(echo "$line" | sed 's/.*cases=\([0-9]*\).*/\1/'); ps=$(echo "$line" | sed 's/.*u3pass=\([0-9]*\).*/\1/')
  f=$(echo "$line" | sed 's/.*u3fail=\([0-9]*\).*/\1/'); n=$(echo "$line" | sed 's/.*u3notrun=\([0-9]*\).*/\1/')
  tc=$((tc+c)); tp=$((tp+ps)); tf=$((tf+f)); tn=$((tn+n))
done
echo "TOTAL p=$P count=$CNT seed=$SEED: cases=$tc pass=$tp fail=$tf notrun=$tn"
