#!/usr/bin/env python3
"""Falsification sweep: run the full pipeline at small split primes
p = 1 (mod 32).  If the exactness law were 'anatomy-forced in char p',
no prime would violate; the char-0 theorem instead predicts violations
exactly at primes dividing one of the obstruction norms."""
import json
from lane_a import run_prime

PRIMES = [97, 193, 257, 353, 449, 577, 641, 673, 769, 929,
          1153, 1217, 1249, 1409, 1601, 1697, 1889, 2017, 2081, 2113]

results = {}
for p in PRIMES:
    try:
        r = run_prime(p, dense_cap=1500, dd_sample=None, verbose=True)
    except AssertionError as e:
        print(f"p={p} ASSERT FAIL: {e}")
        results[p] = dict(error=str(e))
        continue
    results[p] = r
    json.dump(results, open('/tmp/laneA/sweep_results.json', 'w'),
              default=str)
print("done")
