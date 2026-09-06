#!/usr/bin/env python3
"""Independent exact six-value certificate; stdlib only, no scratch imports.

P primality is supplied by the repository production certificate. This script
checks all displayed field identities, exact fiber counts, distinct values,
and a dense n=1024 lift over that same field. It does not enumerate production
coordinates or classify the full list/MCA set.
"""
from fractions import Fraction
from collections import defaultdict
import json

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30

POLYNOMIALS = [[21013949898147473983537680665153842593321561442, 21013949898147473983537680665153842593321561442, 241616374370439463213342467754976913628320808321, 241616374370439463213342467754976913628320808321, 220602424472291989229804787089823071034999246880, 220602424472291989229804787089823071034999246880, 1, 1], [125829621549097067457234094028236226857884909488, 125829621549097067457234094028236226857884909488, 346432046021389056687038881118059297892884156365, 346432046021389056687038881118059297892884156365, 197517887987333714126611752820526843075613533581, 197517887987333714126611752820526843075613533581, 18943363311336672863882327061011457227257409586, 18943363311336672863882327061011457227257409586], [18943363311336672863882327061011457227257409586, 18943363311336672863882327061011457227257409586, 2070586586810801119655353604142385366064151855, 2070586586810801119655353604142385366064151855, 218531837885481188110149433485680685668935095024, 218531837885481188110149433485680685668935095024, 125829621549097067457234094028236226857884909488, 125829621549097067457234094028236226857884909488], [1, 1, 21013949898147473983537680665153842593321561442, 21013949898147473983537680665153842593321561442, 1, 1, 21013949898147473983537680665153842593321561442, 21013949898147473983537680665153842593321561442], [0, 0, 241616374370439463213342467754976913628320808320, 241616374370439463213342467754976913628320808320, 199588474574144515246267106424669228441677685438, 199588474574144515246267106424669228441677685438], [244567222147505997944249974301582298305981161792, 160765500394703878454091241603653756634739375189, 227694445422980126200023000844713226444787904061, 15992515534270138132974820514406072549597056113, 59836924077588110775713545486169314400259871692, 337269438483890118597165313759026757117031347328, 246637808734316799063905327905724683672045313650, 244567222147505997944249974301582298305981161792]]

ALLOCATION = [(1, 0, 1, 1), (2, 0, 1, 1), (3, 219392053940651349857152530071045584056154758815, 1, 1), (4, 247518069924572532675157480848187682983641515266, 1, 1), (5, 198666720931238177635190986055041980241306690928, 1, 1), (6, 365375409332725729550921208179070755120141565949, 1, 1), (7, 162809583046697314739287419158162526858374443598, 1, 1), (8, 0, 1, 1), (9, 0, 1, 1), (10, 0, 1, 1), (11, 8040278528411839415753510174151018752588735139, 1, 1), (12, 33801539815563300941613004670267701763213804923, 3, 5), (12, 143376532876473293338755317584581232435457248186, 2, 5), (13, 226401584590010564539752510019772566282687043095, 4, 5), (13, 304651765265150092193745390057902927190232947028, 1, 5), (14, 70339997232535938394789158593338748784970462157, 2, 5), (14, 297772329701599127667695198838535351593713956111, 3, 5), (15, 210848172633271619290255203437477769726023729775, 1, 1)]


def evaluate(coefficients, x):
    answer = 0
    for coefficient in reversed(coefficients):
        answer = (answer*x+coefficient) % P
    return answer


def exact_data(s):
    n = 16*s
    assert N % n == 0
    root = pow(G, N//n, P)
    eta = pow(root, s, P)
    assert pow(root, n, P) == 1 and pow(root, n//2, P) != 1
    assert eta == pow(G, N//16, P)
    base_values = [[evaluate(f, pow(eta, j, P)) for j in range(16)]
                   for f in POLYNOMIALS]
    assert len(set(v[0] for v in base_values)) == 6
    assert all(len(f) <= 8 and f[-1] != 0 for f in POLYNOMIALS)
    groups = defaultdict(list)
    for j, value, numerator, denominator in ALLOCATION:
        assert 1 <= j <= 15 and 0 <= value < P
        weight = Fraction(numerator, denominator)
        assert 0 < weight <= 1
        groups[j].append((value, weight))
    assert set(groups) == set(range(1, 16))
    weighted = [Fraction(0)]*6
    punctured = [s-1]*6
    rounded = {}
    incidences = []
    for j, rows in sorted(groups.items()):
        assert sum(w for value, w in rows) == 1
        assert len(set(value for value, w in rows)) == len(rows)
        counts = [s*w.numerator//w.denominator for value, w in rows]
        counts[-1] += s-sum(counts)
        assert sum(counts) == s and min(counts) >= 0
        rounded[j] = [(value, count) for (value, w), count in zip(rows, counts)]
        for (value, weight), count in zip(rows, counts):
            hit = [i for i in range(6) if base_values[i][j] == value]
            assert hit
            incidences.append([j, weight.numerator, weight.denominator, hit])
            for i in hit:
                weighted[i] += weight
                punctured[i] += count
    assert weighted == [Fraction(49,5)]*4+[Fraction(51,5), Fraction(49,5)]
    hole_values = [s*v[0] % P for v in base_values]
    assert len(set(hole_values)) == 6
    degrees = [s*len(f)-1 for f in POLYNOMIALS]
    assert max(degrees) == n//2-1
    return root, rounded, punctured, hole_values, degrees, incidences


def dense_control(s=64):
    # Build each entire coefficient array and the received word independently
    # of the compressed agreement formula, then use direct Horner evaluation.
    n = 16*s
    root, rounded, expected, hole_values, degrees, _ = exact_data(s)
    lifted = []
    for f in POLYNOMIALS:
        coeff = [0]*(s*len(f))
        for j, c in enumerate(f):
            for r in range(s):
                coeff[s*j+r] = c
        lifted.append(coeff)
    coordinates = set()
    actual = [0]*6
    actual_hole = []
    for j in range(16):
        fiber = [pow(root, j+16*t, P) for t in range(s)]
        assigned = ([None]*s if j == 0 else
                    [value for value, count in rounded[j] for _ in range(count)])
        assert len(assigned) == s
        for t, x in enumerate(fiber):
            assert x not in coordinates
            coordinates.add(x)
            js = evaluate([1]*s, x)
            assert js*(x-1) % P == (pow(x, s, P)-1) % P
            decoded = [evaluate(f, x) for f in lifted]
            if j == 0 and t == 0:
                assert x == 1 and js == s
                actual_hole = decoded
                continue
            if j == 0:
                assert js == 0 and all(z == 0 for z in decoded)
                received = 0
            else:
                assert js != 0
                received = js*assigned[t] % P
            for i, z in enumerate(decoded):
                actual[i] += (z == received)
    assert len(coordinates) == n
    assert actual == expected == [691,689,691,690,716,690]
    assert actual_hole == hole_values
    # At n=1024, predecessor agreement t=684 and t-1=683>=k=512.
    threshold = n-(n-1)//3+1
    assert threshold == 684 and min(actual) >= threshold-1 >= n//2
    return {'n':n, 'k':n//2, 'full_threshold':threshold,
            'exact_punctured_agreements':actual,
            'degrees':degrees, 'distinct_hole_values':len(set(actual_hole)),
            'dense_coordinate_checks':n,
            'dense_candidate_evaluations':6*n}


def main():
    assert pow(G, N, P) == 1 and pow(G, N//2, P) != 1
    s = N//16
    _, rounded, counts, values, degrees, incidences = exact_data(s)
    threshold = 715827884
    assert threshold-1 >= N//2
    assert counts == [724775731,724775729,724775731,724775730,751619276,724775730]
    assert min(counts)-(threshold-1) == 8947846
    assert min(counts) >= threshold-1
    assert degrees == [536870911]*4+[402653183,536870911]
    assert P//(2**128) == N and len(values) == 6 < N
    output = {'status':'PASS',
              'production':{'n':N,'s':s,'k':N//2,
                  'full_threshold':threshold,
                  'exact_punctured_agreements':counts,
                  'minimum_threshold_slack':min(counts)-(threshold-1),
                  'polynomial_degrees':degrees,
                  'distinct_hole_values':values,
                  'split_fiber_counts':{str(j):[c for v,c in rounded[j]]
                                        for j in (12,13,14)},
                  'actual_MCA_bad_scalars_at_least':6,
                  'allowed_budget':N},
              'weighted_nonhole_agreements':['49/5']*4+['51/5','49/5'],
              'exact_base_incidence_rows':incidences,
              'dense_control':dense_control(),
              'scope':'Six explicit values, no full production list count; no billion scan; no Lean proof.'}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()
