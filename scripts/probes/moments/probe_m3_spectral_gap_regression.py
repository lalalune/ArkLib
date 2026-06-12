#!/usr/bin/env python3
"""Regression checks for the M3 pencil-spectrum gap.

This is the lightweight N3 support brick for issue #357.  The expensive exact
M3 decomposition engine has already written JSON artifacts under `experiment/`.
Here we re-check the theorem-shaped facts those artifacts suggest:

* H5 mean pinning: `sum_phi t2(phi) = C(n,2)*(q-1)`.
* A5 normalizer band: the big-spike pencils are exactly
  `{(1,0,-c) : c in H} ∪ {(0,1,0)}`.
* Spectral gap at n=16: subgroup spectra have no non-normalizer/noise pencils
  with `t2 in {4,5,6}`; the observed bands are `<=3` and `{7,8}`.

The script does not recompute the M3 tensors.  It is a fast guardrail for the
stored exact spectra and a concrete target for the future Weil/character-sum
proof of N3.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


HERE = Path(__file__).resolve().parent

CELLS = [
    (41, 10, HERE / "experiment" / "k3_q41_n10_sub.json", False),
    (113, 16, HERE / "experiment" / "k3_q113_n16_sub.json", True),
    (257, 16, HERE / "experiment" / "k3_q257_n16_sub.json", True),
]


def load_cell(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(f"missing stored spectrum JSON: {path}")
    data = json.loads(path.read_text())
    if "census" not in data:
        raise ValueError(f"stored spectrum lacks census block: {path}")
    return data


def predicted_normalizer(domain: list[int], q: int) -> set[tuple[int, int, int]]:
    pred = {(1, 0, (-c) % q) for c in domain}
    pred.add((0, 1, 0))
    return pred


def check_cell(q: int, n: int, path: Path, expect_gap: bool) -> str:
    data = load_cell(path)
    assert data["q"] == q and data["n"] == n and data["k"] == 3, (path, data["q"], data["n"])

    hist = {int(k): int(v) for k, v in data["census"]["t2_hist"].items()}
    high = data["census"]["high_t2"]
    pred = predicted_normalizer(data["domain"], q)
    big_threshold = max(3, n // 2 - 1)
    big = {tuple(item["phi"]) for item in high if item["t2"] >= big_threshold}

    h5_sum = sum(t2 * count for t2, count in hist.items())
    h5_target = math.comb(n, 2) * (q - 1)
    assert h5_sum == h5_target, (path, h5_sum, h5_target)
    assert big == pred, (path, sorted(big - pred), sorted(pred - big))

    if expect_gap:
        gap = {4, 5, 6}
        assert not (gap & set(hist)), (path, hist)
        assert set(hist) <= {0, 1, 2, 3, 7, 8}, (path, hist)
        assert hist.get(7, 0) == n // 2, (path, hist)
        assert hist.get(8, 0) == n // 2 + 1, (path, hist)

    return (
        f"q={q:>3} n={n:>2}: H5={h5_sum}, "
        f"big={len(big)}/{len(pred)}, hist={hist}"
    )


def main() -> int:
    print("M3 pencil-spectrum regression")
    for q, n, path, expect_gap in CELLS:
        print("  " + check_cell(q, n, path, expect_gap))
    print("verdict: normalizer band and stored n=16 spectral gap match N3 target")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
