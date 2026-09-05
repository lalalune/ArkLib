#!/usr/bin/env python3
"""Conditional surface-proper cut budgets, including contained tail components.

No production surface-proper interpolant is established by this checker.
See docs/kb/astra_hasse_component_split-2026-09-05.md.
"""
import argparse
import json

from astra_c2_budget_obstruction import add, mixed, polarized_mixed, scale
from astra_hasse_rank_profile_check import A, N, W, slices

SURFACE = (2317,37,10)
FIRST = (4634*(W+1),1+74*(W+1),18*(W+1))
SHARP_DIRECTION = (4634,73,19)
UNIT = (0,1,0)
TOTAL = sum(SURFACE)
STAGE_ERROR = 80791
FIELD_BUDGET = 274980728111395087
FIXED_OTHER = 8715852309650505


def split_bound(cut_degree, cutoff):
    assert cutoff >= 1
    quotient = (W+cutoff)//cutoff  # ceil((w+1)/cutoff)
    high_flag = add(scale(1+quotient,SHARP_DIRECTION),UNIT)
    # For every mu>=cutoff, mu*high_flag dominates sharp(w+1+mu).
    # The difference is affine in mu, nonnegative at the endpoint and increasing.
    endpoint = tuple(cutoff*v-((W+1+cutoff)*d+u)
                     for v,d,u in zip(high_flag,SHARP_DIRECTION,UNIT))
    slope = tuple(v-d for v,d in zip(high_flag,SHARP_DIRECTION))
    assert min(endpoint) >= 0 and min(slope) >= 0
    high = mixed(SURFACE,FIRST,high_flag)
    assert high == polarized_mixed(SURFACE,FIRST,high_flag)
    low_tail_degree = sum(SHARP_DIRECTION)*(W+cutoff)+1
    low_cap = max(STAGE_ERROR+1,low_tail_degree)
    outside = TOTAL*sum(FIRST)*cut_degree
    inside = TOTAL*cut_degree*low_cap
    return {"cut_degree":cut_degree,"multiplicity_cutoff":cutoff,
            "high_flag":high_flag,"high_multiplicity_allowance":high,
            "low_tail_degree":low_tail_degree,
            "noncontained_allowance":outside,"contained_allowance":inside,
            "conditional_cell_allowance":high+outside+inside,
            "conditional_fixed_complement_total":high+outside+inside+FIXED_OTHER}


def finite_common_component():
    # On the plane R=0: T=Y^6(Y-1)(Y-2), B=(Y-1)Z.
    # B contains the entire Y=1 component. A further degree-three cut is
    # needed there; B cuts each of the other two components at Z=0.
    p = 17
    outside, inside = [], []
    for y in range(p):
        for z in range(p):
            if (pow(y,6,p)*(y-1)*(y-2)) % p or ((y-1)*z) % p:
                continue
            if y == 1:
                if z*(z-1)*(z-2) % p == 0:
                    inside.append((y,z))
            else:
                outside.append((y,z))
    assert outside == [(0,0),(2,0)]
    assert inside == [(1,0),(1,1),(1,2)]
    assert len(outside) <= 1*8*2 and len(inside) <= 1*2*3
    return {"p":p,"surface_degree":1,"first_cut_degree":8,"extra_cut_degree":2,
            "contained_component_Y":1,"noncontained_points":outside,
            "contained_points_after_further_cut":inside,
            "actual_MCA_instance":False}


def derivative_trim_checks():
    cases = ((80,24,6,-4153747737,None),(99,30,8,-10499511676,None),
             (99,30,1,-222607971,None),(99,30,2,-704205203,None),
             (166,51,1,119175676,42105),(166,51,6,-11841107670,None),
             (240,72,1,1851066966,11828))
    result = []
    for m,s1,s2,expected_slope,expected_T in cases:
        D = m*A-s2*(A-W+2)
        H = (D-1)//(W-2)
        cs,rs = slices(D,W,m,s1,s2,H)
        excess = [c-N*r for c,r in zip(cs,rs)]
        slope = sum(excess)
        moment = sum(h*b for h,b in enumerate(excess))
        first, running, value = None,0,0
        for T,b in enumerate(excess):
            running += b
            value += running
            if value > 0:
                first = T
                break
        if first is None and slope > 0:
            first = max(H,moment//slope)
        assert (slope,first) == (expected_slope,expected_T)
        result.append({"m":m,"s1":s1,"s2":s2,"trimmed_D":D,
                       "all_T_tail_slope":slope,"first_T":first})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--derivative-trim",action="store_true")
    args = parser.parse_args()
    degrees = (6519,6996,15220,19935)
    rows = [split_bound(b,2048) for b in degrees]
    assert [r["conditional_cell_allowance"] for r in rows] == [
        19430390263862412,20838308998565916,45112362822887964,59029211531749644]
    assert all(r["conditional_fixed_complement_total"] < FIELD_BUDGET for r in rows)
    per_degree = TOTAL*(sum(FIRST)+rows[0]["low_tail_degree"])
    high = rows[0]["high_multiplicity_allowance"]
    max_degree = (FIELD_BUDGET-FIXED_OTHER-high)//per_degree
    assert (high,per_degree,max_degree) == (188834222914524,2951611603152,90146)
    assert split_bound(max_degree,2048)["conditional_fixed_complement_total"] <= FIELD_BUDGET
    assert split_bound(max_degree+1,2048)["conditional_fixed_complement_total"] > FIELD_BUDGET
    scan = [min((split_bound(b,2**j) for j in range(18)),
                key=lambda row:row["conditional_cell_allowance"]) for b in degrees]
    assert [r["multiplicity_cutoff"] for r in scan] == [2048,2048,2048,1024]
    output = {"status":"PASS_CONDITIONAL_COMPONENT_SPLIT_ARITHMETIC",
              "surface_flag":SURFACE,"first_tail_flag":FIRST,
              "first_tail_degree":sum(FIRST),"sharp_direction":SHARP_DIRECTION,
              "fixed_complement":FIXED_OTHER,"field_budget":FIELD_BUDGET,
              "fixed_cutoff_rows":rows,"best_power_of_two_cutoffs":scan,
              "maximum_cut_degree_at_fixed_cutoff":max_degree,
              "finite_common_component_control":finite_common_component(),
              "surface_properness_proved":False,"phase_recurrence_replayed":False,
              "lean_run_performed":False,"prize_bound_improved":False}
    if args.derivative_trim:
        output["derivative_trim_profiles"] = derivative_trim_checks()
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
