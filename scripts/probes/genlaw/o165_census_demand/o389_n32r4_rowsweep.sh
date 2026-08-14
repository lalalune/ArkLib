#!/bin/bash
# n=32 r=4 a0=5: sweep the full e=16 row, plus a sampling of other rows, to independently
# confirm 3105 is the max (and that order-2 line e=16 dominates at r=4).
n=32; r=4; a=5
best=0; beste=""; bestf=""
# full e=16 (order-2) row
for f in $(seq 0 31); do
  [ $f -eq 16 ] && continue
  v=$(./cd_demand one $n $r 16 $f $a 2>/dev/null | grep -oE '#bad=[0-9]+' | cut -d= -f2)
  echo "(16,$f)=$v"
  if [ "$v" -gt "$best" ]; then best=$v; beste=16; bestf=$f; fi
done
echo "ROW e=16 MAX: #bad=$best at (16,$bestf)"
