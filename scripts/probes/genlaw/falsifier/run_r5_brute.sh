#!/bin/bash
# class-mode full-brute triple-check of the sampled flagged r=5 classes
cd /tmp/falsifier
for p in 2013265921 3221225473; do
  g0=31; [ "$p" = 3221225473 ] && g0=5
  : > brute_r5_$p.txt
  while read O m c0 mp; do
    nice -n 19 ionice -c3 ./falsify 32 5 $p $g0 class "$O" "$m" >> brute_r5_$p.txt
  done < r5_sample_$p.txt
done
echo BRUTE_SAMPLES_DONE
