#!/bin/bash
cd /tmp/falsifier
for w in 0 1 2; do
  nice -n 19 ionice -c3 ./falsify 32 5 2013265921 31 scan 3 $w rec > r5_bb_w$w.txt 2> r5_bb_w$w.err &
done
wait
echo "BB_ROUND_DONE $(date +%H:%M:%S)"
for w in 0 1 2; do
  nice -n 19 ionice -c3 ./falsify 32 5 3221225473 5 scan 3 $w rec > r5_p2_w$w.txt 2> r5_p2_w$w.err &
done
wait
echo "P2_ROUND_DONE $(date +%H:%M:%S)"
grep -h SUMMARY r5_bb_w*.txt r5_p2_w*.txt
