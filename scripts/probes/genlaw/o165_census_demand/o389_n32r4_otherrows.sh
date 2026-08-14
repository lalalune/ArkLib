#!/bin/bash
# Sample non-order-2 rows at n=32 r=4 a0=5 to check none beats the order-2 max 3105.
# Representative e: order-4 (e=8,24), order-8 (e=4,12,20,28), order-16 (e=2..), order-32 (odd e).
n=32; r=4; a=5
best=3105; beste=16; bestf=9
for e in 8 24 4 12 1 3 17 9 7; do
  rowbest=0; rowf=""
  for f in $(seq 0 31); do
    [ $f -eq $e ] && continue
    v=$(./cd_demand one $n $r $e $f $a 2>/dev/null | grep -oE '#bad=[0-9]+' | cut -d= -f2)
    if [ "$v" -gt "$rowbest" ]; then rowbest=$v; rowf=$f; fi
    if [ "$v" -gt "$best" ]; then best=$v; beste=$e; bestf=$f; fi
  done
  echo "row e=$e MAX: #bad=$rowbest at (e=$e,f=$rowf)"
done
echo "GLOBAL (sampled) MAX: #bad=$best at (e=$beste,f=$bestf)  [order-2 row was 3105]"
