# CLM-043 prime-quadratic cyclotomic-row transfer

This directory contains two exact, standard-library diagnostics for the
affine-intersection and cyclotomic-row transfer recorded as `CLM-043`. Fix an
odd prime `p`, the order-`n` subgroup `G <= F_p^x`, and the quadratic character
`chi` extended by `chi(0)=0`. For nonzero `t`, put

```text
Q = (F_p^x)^2,
C(t) = |tG intersect (1-Q)|,
r(t) = n-1_G(t),
S(t) = sum_(a in G) chi(1-at),
F(t) = sum_(A subset G, |A|=3) prod_(a in A) chi(1-at),
U = sum_(t in F_p^x) F(t)^2.
```

The human derivation proves exactly

```text
S(t)=2C(t)-r(t),
6F(t)=S(t)^3-(3r(t)-2)S(t).
```

Let `m=(p-1)/n`, `H=G intersect Q`, `e=[G:H]`, and `M=em`. For a
primitive root `zeta`, set `C_i=zeta^i H` and

```text
N_(i,j)=|{x in C_i:1-x in C_j}|.
```

Then `e=1` when `m` is even and `e=2` when `m` is odd. The row values are

```text
S_i=sum_(u=0)^(e-1) sum_(j=0)^(M-1) (-1)^j N_(i+um,j),
r_i=n-1 for i in {um:0<=u<e}, and r_i=n otherwise,
U=|H| sum_(i=0)^(M-1) ((S_i^3-(3r_i-2)S_i)/6)^2.
```

The inverse-root zero is retained throughout: when `t in G`, exactly one
factor `chi(1-at)` is zero. The punctured domain contains `t=1,...,p-1` and
never contains `t=0`.

## Result and scope

The exact diagnostic outputs are:

| `(p,n)` | `m` | `e` | `|H|` | direct `U` = row `U` | `D_6` | `D_6-36U` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `(97,3)` | 32 | 1 | 3 | 93 | 0 | -3,348 |
| `(257,4)` | 64 | 1 | 4 | 964 | 0 | -34,704 |
| `(641,5)` | 128 | 1 | 5 | 6,380 | 0 | -229,680 |
| `(1297,6)` | 216 | 1 | 6 | 25,464 | 64,800 | -851,904 |
| `(1459,6)` | 243 | 2 | 3 | 27,768 | 0 | -999,648 |
| `(2521,7)` | 360 | 1 | 7 | 118,377 | 211,680 | -4,049,892 |

Status: **PROVEN only as the exact affine-intersection/cyclotomic-row
transfer and reformulation above.** The proof is the human derivation; the
six finite cells are diagnostics that check both parity branches and every
normalization. They are not an exhaustive proof of the general statement.

This result supplies **no** uniform bound on `U`, `DC`, or `D_6`; no result for
`CLM-016`; and no Proximity Gap Grand Challenge or prize result. It makes no
novelty, priority, prize-eligibility, authorship, award, or payment claim and
is not a formal prize submission.

`reference.py` directly enumerates every punctured affine row before building
the cyclotomic rows. `independent.py` constructs the cyclotomic classes and
`N_(i,j)` rows first, reconstructs `G`, and independently evaluates elementary
symmetric functions. Both use Python 3.11 or newer and only the standard
library. `case.toml` has a closed schema and fixes the six cells and their
order. `expected.json` is canonical JSON with exact integer-valued
mathematical fields.

## Reproduce

Run these commands from this directory.

Byte-for-byte comparison of both independent implementations with the frozen
expected certificate:

```shell
python -c "import hashlib,pathlib,subprocess,sys; r=subprocess.check_output([sys.executable,'reference.py','case.toml']); i=subprocess.check_output([sys.executable,'independent.py','case.toml']); e=pathlib.Path('expected.json').read_bytes(); assert r == i == e; print(hashlib.sha256(e).hexdigest())"
```

The expected output SHA-256 is
`6f70178d995425a25109d64bb523879688363ea7c87780a28adda59f099ff7c5`.

Verify that `result-manifest.json` binds the case, expected result, and both
implementations:

```shell
python -c "import hashlib,json,pathlib; m=json.loads(pathlib.Path('result-manifest.json').read_text(encoding='utf-8')); files={'case.toml':m['case_sha256'],'expected.json':m['expected_sha256'],'reference.py':m['implementations']['reference'],'independent.py':m['implementations']['independent']}; assert all(hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() == digest for name,digest in files.items()); assert m['result_sha256'] == m['expected_sha256']; print('manifest hashes verified')"
```

Compile both programs without running them:

```shell
python -m py_compile reference.py independent.py
```

The full human derivation, scope, and prior-work map are in
[`docs/kb/deltastar-466-clm043-cyclotomic-row-transfer-2026-08-25.md`](../../../docs/kb/deltastar-466-clm043-cyclotomic-row-transfer-2026-08-25.md).
