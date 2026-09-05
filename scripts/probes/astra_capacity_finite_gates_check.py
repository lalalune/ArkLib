#!/usr/bin/env python3
"""Exact finite-parameter audit of ECCC TR26-164 revision1, not prize closure.

The real-variable inequality follows from the checked polynomial identity
and the positivity proof in the accompanying note. No external theorem is
proved by this checker. Optional source hashing performs no network access.
"""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

SOURCE = 'https://eccc.weizmann.ac.il/report/2026/164/revision/1/download'
SOURCE_SHA256 = '560e7134e49abc065718bf97a50c20b1cce7eba9d7b465b98a64be90dd88d903'
P = 365375409332725729550921208179070755120141565953


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-pdf', type=Path)
    args = parser.parse_args()
    if args.source_pdf is not None:
        actual = sha256(args.source_pdf.read_bytes()).hexdigest()
        if actual != SOURCE_SHA256:
            raise ValueError('PDF differs from the audited revision')
    n = 2**30
    assert P == n * (2**128 + 192) + 1
    assert 2**158 < P < 2**159 < 2**180
    # 27 - 256*t^3*(1-t) = (4*t-3)^2*(16*t^2+8*t+3).
    assert mul(mul([-3, 4], [-3, 4]), [3, 8, 16]) == [27, 0, 0, -256, 256]
    base_bound = Fraction(27, 256 * 768)
    assert base_bound == Fraction(9, 65536) < Fraction(1, 2**12)
    assert base_bound**5 < Fraction(1, 2**60)
    # For 0<t<1, (5+t)/(1-t)>5 and 3/t>3; the written proof
    # deduces eta<2^-60 and d>2^180. Padding then requires N>2^240.
    assert 12 * 5 * 3 == 180 and 180 + 60 == 240
    target, remainder = divmod(P, 2**128)
    assert target == n and remainder == 192 * n + 1
    assert 0 < remainder < 2**128 and P > target
    print(json.dumps(dict(
        status='PASS_FINITE_CAPACITY_PARAMETER_GATES',
        source=SOURCE, source_sha256=SOURCE_SHA256,
        source_pdf_hash_checked=args.source_pdf is not None,
        production_prime=P, production_length=n,
        production_prime_bit_length=P.bit_length(),
        uniform_base_upper_bound=str(base_bound),
        eta_strict_upper_bound='2^-60', d_strict_lower_bound='2^180',
        padded_length_strict_lower_bound='2^240',
        padded_required_agreement_strict_lower_bound='2^180',
        target_list_integer_bound=target,
        explicit_theorem41_parameters_fit_production_field=False,
        corollary51_padding_preserves_production_agreement=False,
        external_theorem_proof_checked=False, prize_closure_claim=False
    ), sort_keys=True))


if __name__ == '__main__':
    main()
