// Exact-integer research evaluator, NOT a Lean soundness certificate.
// Pinned source: proximity-prize/proximity-prize @
// b34c0131cfa36b51111521541d7d3e35c8791082, SubmissionLower/PackedLocatorTail*.lean.
// See docs/kb/proximity-astra-companion-2026-09-04.md for obligations.
//
// clang++ -O3 -std=c++17 scripts/probes/astra_companion_phases.cpp -o /tmp/astra-phases
// /tmp/astra-phases baseline
// /tmp/astra-phases candidate
// /tmp/astra-phases candidate-z
// /tmp/astra-phases candidate-closure
// /tmp/astra-phases search-t
// Optional final arguments give 1..256 (multiplicity, limit, slope) triples.
// In candidate-closure mode, optional --root T Y S wideY wideS initialL
// precedes those triples. This changes numerical root caps only; the caller
// must establish the root interpolants and all associated algebraic gates.
// That mode also accepts --errors E, --padding P, and --joint Bm BL TY TS TL.
// --joint adds the correlated ChainGroupMaj complement from official commit
// 032154395c51fd6f77715a7f42d9a987ab9fb48a. It prints the remaining fixed tails
// separately. Options precede sources and may appear in any order, once each.
// --actual-contact uses the source's actual weighted degree in the thin band.
// --clipped-band additionally charges each boundary channel its exact width.
// A separate exact-strip projection/rank lemma is Lean checked. Connecting
// these research rules to the repeated quotient selector remains unproved.
// The default four-source receipts remain unchanged. Additional sources use
// the same strict-slope recursion; they do not certify a Lean soundness theorem.
// Signed 128-bit arithmetic is intentional: a negative nullity must not be
// hidden by Nat subtraction. Bounds here are for the displayed small inputs.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Integer = __int128_t;
constexpr int n = 262144, w = 131071;
constexpr int max_phases = 256;
constexpr Integer published_cap = Integer(254595720129422441LL);
constexpr Integer candidate_allocation = Integer(260136176662196960LL);

std::string decimal(Integer x) {
  if (x < 0) return "-" + decimal(-x);
  if (!x) return "0";
  std::string result;
  while (x) {
    result.push_back('0' + x % 10);
    x /= 10;
  }
  std::reverse(result.begin(), result.end());
  return result;
}

Integer positive(Integer x) { return std::max<Integer>(0, x); }
Integer ceiling(Integer x, Integer y) {
  assert(y > 0);
  return x >= 0 ? (x + y - 1) / y : x / y;
}

// RCN260.UnequalParameters.regularCountCap. Coordinates are Y, R, Z.
Integer regular_count(int errors, std::array<Integer,3> left,
                      std::array<Integer,3> right) {
  auto agreement=[](std::array<Integer,3> x) {
    return std::array<Integer,3>{1+2*w*x[0], w*positive(2*x[1]-1), 2*w*x[2]+1};
  };
  auto a=agreement(left), b=agreement(right);
  std::array<Integer,3> mix{left[1]*right[2]+left[2]*right[1],
    left[0]*right[2]+left[2]*right[0], left[0]*right[1]+left[1]*right[0]};
  Integer dot=0, gap=n-w-errors;
  for (int i=0;i<3;++i) dot+=std::max(a[i],b[i])*mix[i];
  return ((n-w)*dot+(errors+1)*gap*mix[2])/gap;
}

// RCN318.TightParameters.countCap at slope 1, the R-free chain tail.
Integer tight_count(int errors, Integer weighted, int limit) {
  Integer y=(weighted-1)/w, z=limit, gap=n-w-errors;
  Integer dot=(1+2*w*y)*z+w*(2*y*z)+(2*w*z+1)*y;
  return ((n-w)*dot+(errors+1)*gap*y+2*z*z*gap)/gap;
}

// Closed-form floor of the numerator sum, not the sum of floors. This is
// exactly ChainGroupMaj.chainMaj, including Nat subtraction at r=0 and r=1.
Integer chain_majorant(int errors, int zc, int r, int y) {
  Integer z=zc, yr=y, rr=r, gap=n-w-errors;
  Integer a=(n-w)*((1+2*w*yr)*(z*rr)+w*positive(2*rr-1)*(2*z*yr)
      +(2*w*z+1)*(yr*rr))+(errors+1)*gap*(yr*rr);
  Integer b=(n-w)*((1+2*w*yr)*z+(2*w*z+1)*yr)+(errors+1)*gap*yr;
  return (positive(rr-1)*a+b*rr*positive(rr-1)/2)/gap;
}

// LocatorFactorAggregate.FlagDegree, flagMixed, and paddedTail.
struct Flag { Integer z, v, r; };
Flag add(Flag a, Flag b) { return {a.z + b.z, a.v + b.v, a.r + b.r}; }
Integer mixed(Flag p, Flag q, Flag r) {
  return (q.r*r.r + q.v*r.r + q.r*r.v)*(p.z+p.v+p.r)
       + (q.z*r.r + q.r*r.z)*(p.v+p.r)
       + (q.v*r.v + q.z*r.v + q.v*r.z)*p.r;
}
Flag tail(int r, int v, int z, int degree) {
  Integer s = std::max(r, 2), y = std::max<Integer>(r+v, s+1);
  Integer t = std::max<Integer>(r+v+z, y);
  return {2*(t-y)*degree, 1+2*(y-s)*degree, 2*(s-1)*degree};
}

// ordinaryCostOf selects the published C2 envelope when r>=3 and v>=2.
// Its algebraic/characteristic hypotheses must separately be proved for a
// retuned candidate; this function merely evaluates that envelope.
Integer ordinary_cost(int r, int v, int z) {
  Flag f{z, v, r};
  Integer s = std::max(r, 2), y = std::max<Integer>(r+v, s+1);
  Integer t = std::max<Integer>(r+v+z, y);
  if (r >= 3 && v >= 2) {
    Flag rational{131074*(t-y), 131074*(y-s-1)+2, 131074*(s-2)+3};
    Flag fiber{t-y, y-s, s+1};
    Flag cut = add(rational, {0, 131072, 262144});
    return mixed(f, tail(r,v,z,131072), rational)
         + 131076*mixed(f, fiber, cut);
  }
  return mixed(f, tail(r,v,z,131072), tail(r,v,z,131073));
}

// LocatorFastKernelArithmetic.{rectangularCount,fastLocalRankBound,
// fastCoefficientCount}. The coefficient double sum is evaluated using
// exact sums of 1,i,i^2; no floating point or asymptotic approximation occurs.
Integer rectangle(Integer a, Integer b, Integer offset, Integer limit) {
  return positive(a*b*positive(limit+1-offset)
         - b*a*positive(a-1)/2 - a*b*positive(b-1)/2);
}
Integer rank_bound(int m, int limit, int slope) {
  assert(m+slope <= limit);
  Integer result = 0;
  for (int r=0; r<m; ++r) {
    int degree=std::min(r,limit), contact=std::min(r+1,m-r);
    result += positive(rectangle(degree+1,slope+1,0,limit)
        - rectangle(std::max(0,degree+1-contact),
                    std::max(0,slope+1-contact),contact,limit));
  }
  return result;
}
Integer coefficients(std::int64_t weighted, int limit, int slope) {
  Integer result = 0;
  for (int j=0; j<=slope; ++j) {
    Integer a=Integer(weighted)-Integer(w-1)*j, b=limit+1-j;
    if (a<=0 || b<=0) break;
    Integer i=std::min<Integer>(b-1,(a-1)/w);
    Integer sum1=i*(i+1)/2, sum2=i*(i+1)*(2*i+1)/6;
    result += (i+1)*b*a-(b*w+a)*sum1+w*sum2;
  }
  return result;
}

// Number of total-degree channels in the raw quotient box.
Integer channels(int t, int y, int s) {
  assert(t>=0 && y>=0 && s>=0);
  int u=std::min(t,y), j=std::min(u,s);
  Integer b=u+1, c=t+1, sum1=Integer(j)*(j+1)/2;
  Integer sum2=Integer(j)*(j+1)*(2*j+1)/6;
  return ((j+1)*(2*b*c-b*b+b)-(2*c+1)*sum1+sum2)/2;
}

// Sum_{j=0}^last max(0, base+j), using integer arithmetic only.
Integer positive_ramp(std::int64_t base, int last) {
  std::int64_t first=std::max<std::int64_t>(0,1-base);
  if (first>last) return 0;
  return Integer(last-first+1)*(2*Integer(base)+first+last)/2;
}

// Exact dimension of the strip Dhigh-delta <= x+w*y+(w-1)*r < Dhigh,
// with y+r+z<=T, y+r<=Y, r<=S. Write k=y+r; the x-width of channel (k,r)
// is min(delta,max(0,Dhigh-w*k+r)). All earlier k-rows have full width.
// At the supported source sizes delta+S<2*w, so there are at most two
// partial rows. This formula also works without that speed assumption.
Integer clipped_band(std::int64_t high, int delta, int t, int y, int s) {
  if (high<=0 || delta<=0) return 0;
  int top=int(std::min<std::int64_t>({t,y,(high+s-1)/w}));
  int full=high>=delta ? int(std::min<std::int64_t>({t,y,(high-delta)/w})) : -1;
  Integer result=full>=0 ? Integer(delta)*channels(t,full,s) : 0;
  for (int k=full+1;k<=top;++k) {
    std::int64_t base=high-std::int64_t(w)*k;
    int last=std::min(k,s);
    result+=Integer(t-k+1)*(positive_ramp(base,last)-positive_ramp(base-delta,last));
  }
  return result;
}

using Potential = std::array<Integer,3>; // total, middle, slope coefficients
struct Source {
  int multiplicity, limit, y, slope;
  std::int64_t weighted;
  int delta;
  Integer gap;
  Potential potential;
  int band_rule=0; // 0: published thin, 1: actual contact thin, 2: clipped strip
};

// Componentwise ceiling majorant of the regular mixed numerator. The initial
// A source uses maxima153,33 to dominate the wider selected factor box.
Potential potential(int errors, int limit, int y, int s,
                    int max_y=-1, int max_s=-1) {
  int gap=n-w-errors;
  Integer ay=1+2*Integer(w)*std::max(y,max_y);
  Integer ar=Integer(w)*(2*std::max(s,max_s)-1);
  Integer az=2*Integer(w)*limit+1;
  return {ceiling((n-w)*(ay*s+ar*y),gap),
          ceiling((n-w)*(ar*limit+az*s),gap)+Integer(errors+1)*s,
          ceiling((n-w)*(ay*limit+az*y),gap)+Integer(errors+1)*y};
}
Integer evaluate(Potential a, int r, int v, int z) {
  return a[0]*(r+v+z)+a[1]*(r+v)+a[2]*r;
}

// Published Routeable disjunction: either the full quotient-channel budget
// or the contact-thinned budget is strictly below interpolation nullity.
bool routeable(const Source& source, int r, int v, int z) {
  int t=r+v+z, y=r+v;
  if (!r || t>source.limit || y>source.y || r>source.slope) return false;
  int fuel=std::min({source.limit/t,source.y/y,source.slope/r});
  std::int64_t cap=(source.band_rule ? source.weighted :
      std::int64_t(w)*(source.y+1)-source.slope)-(w*y-r);
  cap=std::max<std::int64_t>(0,cap);
  int contact=w*y-r;
  Integer band=0, thin=0;
  for (int j=1; j<=fuel; ++j) {
    int qt=source.limit-j*t, qy=source.y-j*y, qs=source.slope-j*r;
    band += Integer(source.delta)*channels(qt,qy,qs);
    int thin_y=int(std::min<std::int64_t>(qy,std::max<std::int64_t>(0,(cap+qs-1)/w)));
    Integer thin_step=Integer(source.delta)*channels(qt,thin_y,qs);
    if (source.band_rule==2) {
      Integer clipped=clipped_band(cap,source.delta,qt,qy,qs);
      assert(clipped<=thin_step);
      thin_step=clipped;
    }
    thin += thin_step;
    cap=std::max<std::int64_t>(0,cap-source.delta-contact);
    if (band>=source.gap && thin>=source.gap) return false;
  }
  return band<source.gap || thin<source.gap;
}
int route_threshold(const Source& source, int r, int v, int total_cap) {
  int high=total_cap-r-v;
  if (!routeable(source,r,v,high)) return high+1;
  int low=0;
  while (low<high) {
    int middle=(low+high)/2;
    if (routeable(source,r,v,middle)) high=middle;
    else low=middle+1;
  }
  // Monotonicity is a separate theorem in the source; check the boundary too.
  assert(routeable(source,r,v,low));
  assert(low==0 || !routeable(source,r,v,low-1));
  return low;
}

// ordinary_cost(r,v,z) is affine for z>=3. A carrier factor receives all z;
// the remaining factors are represented by the exact zero-slice knapsack.
// The source's convex-carrier lemma justifies the base envelope, not an
// assertion that the phase-refined cap itself is convex.
struct Line { Integer intercept, slope; int start; };
std::vector<Line> upper_hull(std::vector<Line> lines) {
  std::sort(lines.begin(),lines.end(),[](Line a,Line b) {
    return a.slope==b.slope ? a.intercept<b.intercept : a.slope<b.slope;
  });
  std::vector<Line> result;
  for (Line line:lines) {
    if (!result.empty() && line.slope==result.back().slope) {
      if (line.intercept<=result.back().intercept) continue;
      result.pop_back();
    }
    int start=0;
    while (!result.empty()) {
      Integer cross=ceiling(result.back().intercept-line.intercept,
                            line.slope-result.back().slope);
      start=cross<0 ? 0 : cross>100000000 ? 100000000 : int(cross);
      if (start<=result.back().start) result.pop_back(); else break;
    }
    line.start=result.empty() ? 0 : start;
    result.push_back(line);
  }
  return result;
}

// Bounded interpolation/quotient search only. This does not test the changed
// residual ledger, selected-box realization, or other T-source theorem gates.
void search_t_candidates() {
  std::vector<std::array<Integer,5>> rows;
  for (int m=80;m<=420;++m) for (int s=m*27/100;s<=m*35/100;++s) {
    int weighted=m*(n-80781), y=(weighted-1)/w;
    auto nullity=[&](int limit) {
      return coefficients(weighted,limit,s)-n*rank_bound(m,limit,s);
    };
    Integer start=nullity(100000), slope=nullity(100001)-start;
    Integer quotient=coefficients(weighted,2,s);
    if (slope<=0) continue;
    Integer limit=100000+ceiling(quotient+1-start,slope);
    // Both coefficient and rank formulas are affine in L above these caps.
    if (limit<std::max(m+s,y+s) || limit>100000) continue;
    Integer margin=nullity(int(limit))-quotient;
    assert(margin>0);
    assert(nullity(int(limit)-1)<=quotient);
    rows.push_back({limit,m,s,y,margin});
  }
  std::sort(rows.begin(),rows.end());
  assert(!rows.empty());
  assert((rows.front()==std::array<Integer,5>{6657,194,60,268,80130328}));
  std::cout<<"BOUNDED_T_KERNEL_SEARCH; columns L m S Y quotient_margin\n";
  for (int i=0;i<std::min<int>(10,rows.size());++i) {
    for (Integer value:rows[i]) std::cout<<decimal(value)<<" ";
    std::cout<<"\n";
  }
  std::cout<<"KERNEL_AND_QUOTIENT_DIMENSIONS_ONLY; FULL_SOUNDNESS_UNPROVED\n";
}

int main(int argc, char** argv) try {
  std::string mode=argc>1 ? argv[1] : "baseline";
  if (mode=="search-t" && argc==2) { search_t_candidates(); return 0; }
  bool baseline=mode=="baseline", closure=mode=="candidate-closure";
  bool keep_z=mode=="candidate-z" || closure;
  if (!baseline && mode!="candidate" && !keep_z)
    throw std::invalid_argument("mode must be baseline, candidate, candidate-z, or candidate-closure");
  int errors=baseline?80771:80781, y_cap=baseline?132:135;
  int total_cap=baseline?6412:6676;
  int slope_cap=29, wide_y=153, wide_slope=33, initial_limit=130000;
  int source_start=2, padding=0, b_m=0, b_limit=0, t_y=0, t_s=0, t_limit=0, band_rule=0;
  bool custom_root=false, custom_errors=false, custom_padding=false, joint_ledger=false;
  while (source_start<argc && std::string(argv[source_start]).rfind("--",0)==0) {
    std::string option=argv[source_start++];
    if (!closure) throw std::invalid_argument("options require candidate-closure");
    auto next=[&]() {
      if (source_start>=argc) throw std::invalid_argument("missing value for "+option);
      std::string value=argv[source_start++];
      std::size_t used=0;
      int result=std::stoi(value,&used);
      if (used!=value.size()) throw std::invalid_argument("noninteger option value");
      return result;
    };
    if (option=="--root" && !custom_root) {
      custom_root=true;
      total_cap=next(); y_cap=next(); slope_cap=next();
      wide_y=next(); wide_slope=next(); initial_limit=next();
    } else if (option=="--errors" && !custom_errors) {
      custom_errors=true; errors=next();
      if (errors<80771 || errors>81000)
        throw std::invalid_argument("error cell outside bounded research range");
    } else if (option=="--padding" && !custom_padding) {
      custom_padding=true; padding=next();
      if (padding<0 || padding>1000000) throw std::invalid_argument("invalid potential padding");
    } else if (option=="--joint" && !joint_ledger) {
      joint_ledger=true;
      b_m=next(); b_limit=next(); t_y=next(); t_s=next(); t_limit=next();
    } else if (option=="--actual-contact" && band_rule==0) {
      band_rule=1;
    } else if (option=="--clipped-band" && band_rule==0) {
      band_rule=2;
    } else throw std::invalid_argument("unknown or repeated option "+option);
  }
  if (slope_cap<1 || slope_cap>64 || y_cap<slope_cap || y_cap>256
      || total_cap<y_cap || total_cap>20000 || wide_y<y_cap || wide_y>1000
      || wide_slope<slope_cap || wide_slope>wide_y
      || initial_limit<total_cap || initial_limit>2000000)
    throw std::invalid_argument("root caps outside the bounded research range");
  if (joint_ledger && (b_m<1 || b_m>100000 || b_limit<total_cap || b_limit>2000000
      || t_y<1 || t_y>10000 || t_s<1 || t_s>t_y || t_limit!=total_cap+3
      || (std::int64_t(b_m)*(n-errors)-1)/w>wide_y))
    throw std::invalid_argument("invalid correlated residual parameters");
  int agreements=n-errors;
  bool custom_sources=argc>source_start;
  if (custom_sources && ((argc-source_start)%3 || argc>source_start+3*max_phases))
    throw std::invalid_argument("expected optionally 1..256 source triples");
  std::cout<<"root T "<<total_cap<<" Y "<<y_cap<<" S "<<slope_cap
    <<" wideY "<<wide_y<<" wideS "<<wide_slope<<" initialL "<<initial_limit<<"\n";
  std::vector<std::array<int,3>> shapes{
    {4800,328400,1480},{1200,82100,370},{1000,42000,310},{390,19500,120}};
  if (custom_sources) {
    shapes.resize((argc-source_start)/3);
    for (int i=0;i<int(shapes.size());++i) for (int j=0;j<3;++j)
      shapes[i][j]=std::stoi(argv[source_start+3*i+j]);
  }
  int phase_count=int(shapes.size());
  std::vector<Source> sources;
  for (auto shape:shapes) {
    auto [m,limit,slope]=shape;
    if (m<=0 || m>100000 || slope<=0 || slope>m
        || limit<m+slope || limit>20000000)
      throw std::invalid_argument("source requires 0<S<=m<=100000 and m+S<=L<=20000000");
    std::int64_t weighted=std::int64_t(m)*agreements;
    int y=int((weighted-1)/w);
    Source source{m,limit,y,slope,weighted,agreements-w+1,
      coefficients(weighted,limit,slope)-n*rank_bound(m,limit,slope),
      potential(errors,limit,y,slope)};
    source.band_rule=band_rule;
    if (source.gap<=0) { std::cout<<"INFEASIBLE source "<<m<<"\n"; return 2; }
    // PhaseKernelRealization.shape, phase-source domination, helper-pair
    // characteristic bounds, and raw-z route monotonicity prerequisites.
    constexpr Integer characteristic=2130706433;
    bool gates=slope<=m && m<characteristic && limit>=total_cap
        && y>=y_cap && slope>=slope_cap
        && Integer(weighted)+slope<=Integer(w)*(y+1)
        && Integer(slope_cap)*limit+Integer(total_cap)*slope<characteristic
        && Integer(y_cap)*limit+Integer(total_cap)*y<characteristic
        && Integer(y_cap)*slope+Integer(slope_cap)*y<characteristic;
    if (!gates) { std::cout<<"SOURCE_GATE_FAILED "<<m<<"\n"; return 3; }
    for (Integer& coefficient:source.potential) coefficient+=baseline?10000:padding;
    sources.push_back(source);
    std::cout<<"source "<<m<<" "<<limit<<" "<<slope<<" y "<<y
      <<" nullity "<<decimal(source.gap)<<" potential";
    for (Integer coefficient:source.potential) std::cout<<" "<<decimal(coefficient);
    std::cout<<"\n";
  }
  // Compile-time hooks for separate research envelope experiments. A visitor
  // that lowers cap must supply its own counting argument and validation.
#ifdef ASTRA_PHASE_SETUP
  ASTRA_PHASE_SETUP(sources);
#endif
  std::vector<std::vector<Integer>> zero(slope_cap+1,
      std::vector<Integer>(y_cap+1,-1));
  zero[0][0]=0; // With positive-slope factors, no nonempty r=0 partition exists.
  std::vector<std::vector<std::array<Integer,5>>> raw(slope_cap+1,
      std::vector<std::array<Integer,5>>(y_cap+1));
  for (int r=1;r<=slope_cap;++r) for (int v=0;r+v<=y_cap;++v)
    for (int z=0;z<5;++z) raw[r][v][z]=ordinary_cost(r,v,z);
  for (int r=1;r<=slope_cap;++r) for (int v=0;r+v<=y_cap;++v)
    for (int i=1;i<=r;++i) for (int j=0;j<=v;++j)
      if (zero[r-i][v-j]>=0)
        zero[r][v]=std::max(zero[r][v],raw[i][j][0]+zero[r-i][v-j]);

  // Coarse prefixes forget z. The optional experiment retains z with rolling
  // slope layers; it still requires a new proof/certificate of prefix soundness.
  // Store only active sources; a four-source replay should not pay the memory
  // cost of a large optional search. The phase index is contiguous.
  int z_extent=keep_z?total_cap+1:1;
  auto offset=[&](int v,int z,int phase) {
    return (std::size_t(v)*z_extent+z)*phase_count+phase;
  };
  std::vector<std::uint64_t> previous(std::size_t(y_cap+1)*z_extent*phase_count),
      current(previous.size());
  Potential initial=baseline ? Potential{5961153504LL,5974067721865LL,22929595672934LL}
                             : potential(errors,initial_limit,y_cap,slope_cap,wide_y,wide_slope);
  if (!baseline) for (Integer& coefficient:initial) coefficient+=padding;
  std::cout<<"initial_potential";
  for (Integer coefficient:initial) std::cout<<" "<<decimal(coefficient);
  std::cout<<"\n";
  Integer fixed_tails=joint_ledger ?
      (wide_slope+1)*tight_count(errors,Integer(b_m)*agreements,total_cap) : 0;
  // This is independent of z and stays outside the phase/prefix recurrence.
  auto correlated=[&](int r,int v) -> Integer {
    if (!joint_ledger) return 0;
    int residual_r=wide_slope-r;
    return chain_majorant(errors,total_cap,r,r+v)
      +chain_majorant(errors,total_cap,residual_r,wide_y-v)
      +regular_count(errors,{wide_y,std::max(1,residual_r),b_limit},{t_y,t_s,t_limit})
      +chain_majorant(errors,b_limit,residual_r,wide_y)
      +2*tight_count(errors,Integer(b_m)*agreements,b_limit);
  };
  // Empty universal child: all positive-R factors use the initial helper.
  // This case is small for the pinned receipts but belongs to the envelope.
  int empty_r=std::min({total_cap,wide_y,wide_slope});
  int empty_v=std::min(total_cap-empty_r,wide_y-empty_r);
  Integer maximum=evaluate(initial,empty_r,empty_v,total_cap-empty_r-empty_v)+correlated(0,0);
  int best_r=0,best_v=0,best_z=0;
  std::array<Integer,max_phases> best_costs{};
  std::array<std::uint64_t,max_phases> source_winners{};
  for (int r=1;r<=slope_cap;++r) {
#ifdef ASTRA_PHASE_SLOPE_BEGIN
    ASTRA_PHASE_SLOPE_BEGIN(r);
#endif
    for (int v=0;r+v<=y_cap;++v) {
      Integer correlated_cost=correlated(r,v);
      std::vector<Line> lines;
      std::array<Integer,3> small{};
      for (int i=1;i<=r;++i) for (int j=0;j<=v;++j) if (zero[r-i][v-j]>=0) {
        Integer rest=zero[r-i][v-j], slope=raw[i][j][4]-raw[i][j][3];
        lines.push_back({raw[i][j][3]-3*slope+rest,slope,0});
        for (int z=0;z<3;++z) small[z]=std::max(small[z],raw[i][j][z]+rest);
      }
      auto hull=upper_hull(lines);
      std::array<int,max_phases> thresholds{};
      for (int phase=0;phase<phase_count;++phase)
        thresholds[phase]=route_threshold(sources[phase],r,v,total_cap);
      std::array<Integer,max_phases> local{};
      int index=0;
      for (int z=0;z<=total_cap-r-v;++z) {
        while (index+1<int(hull.size()) && hull[index+1].start<=z) ++index;
        Integer cap=z<3 ? small[z] : hull[index].intercept+hull[index].slope*z;
        std::array<Integer,max_phases> costs{};
        int winner=-1;
        for (int phase=0;phase<phase_count;++phase) {
          Integer charge=evaluate(sources[phase].potential,r,v,z);
          Integer point=0;
          if (z<thresholds[phase]) {
            point=positive(cap-charge);
            local[phase]=std::max(local[phase],point);
          } else {
            Integer routed=charge+previous[offset(v,keep_z?z:0,phase)];
            if (routed<cap) { cap=routed; winner=phase; }
          }
          if (keep_z) {
            // In closure mode this is recomputed below using the final child
            // cap. No same-slope cap is read: all sources use previous layer.
            Integer prefix=std::max({point,Integer(previous[offset(v,z,phase)]),
                v?Integer(current[offset(v-1,z,phase)]):Integer(0),
                z?Integer(current[offset(v,z-1,phase)]):Integer(0)});
            assert(prefix<(Integer(1)<<64));
            current[offset(v,z,phase)]=std::uint64_t(prefix);
          }
          costs[phase]=cap;
        }
#ifdef ASTRA_PHASE_CAP_VISIT
        ASTRA_PHASE_CAP_VISIT(r,v,z,cap);
#endif
        if (winner>=0) ++source_winners[winner];
        if (closure) for (int phase=0;phase<phase_count;++phase) {
          Integer charge=evaluate(sources[phase].potential,r,v,z);
          Integer point=z<thresholds[phase] ? positive(cap-charge) : 0;
          Integer prefix=std::max({point,Integer(previous[offset(v,z,phase)]),
              v?Integer(current[offset(v-1,z,phase)]):Integer(0),
              z?Integer(current[offset(v,z-1,phase)]):Integer(0)});
          assert(prefix<(Integer(1)<<64));
          current[offset(v,z,phase)]=std::uint64_t(prefix);
        }
        int rt=total_cap-r-v-z, ry=wide_y-r-v, rr=wide_slope-r;
        int nr=std::min({rt,ry,rr}), nv=std::min(rt-nr,ry-nr);
        Integer joint=cap+evaluate(initial,nr,nv,rt-nr-nv)+correlated_cost;
        if (joint>maximum) {
          maximum=joint; best_r=r; best_v=v; best_z=z; best_costs=costs;
        }
      }
      if (!keep_z) for (int phase=0;phase<phase_count;++phase) {
        Integer prefix=std::max({local[phase],Integer(previous[offset(v,0,phase)]),
                                v?Integer(current[offset(v-1,0,phase)]):Integer(0)});
        assert(prefix<(Integer(1)<<64));
        current[offset(v,0,phase)]=std::uint64_t(prefix);
      }
    }
    previous.swap(current);
    std::fill(current.begin(),current.end(),0);
  }
  if (closure) {
    std::cout<<"source_winner_cells";
    for (int phase=0;phase<phase_count;++phase) std::cout<<" "<<source_winners[phase];
    std::cout<<"\n";
  }
  std::cout<<"FINAL "<<mode<<" errors "<<errors<<" Y "<<y_cap<<" T "<<total_cap
           <<" max "<<decimal(maximum)<<" at "<<best_r<<" "<<best_v<<" "<<best_z
           <<" costs";
  for (int phase=0;phase<phase_count;++phase) std::cout<<" "<<decimal(best_costs[phase]);
  std::cout<<"\n";
  if (baseline && !custom_sources) {
    assert(maximum==published_cap);
    std::cout<<"PUBLISHED_BASELINE_REPRODUCED\n";
  }
  if (!baseline && !custom_sources && !custom_root && !custom_errors && !custom_padding && !joint_ledger && !band_rule) {
    Integer expected=keep_z ? Integer(274535875126515098LL)
                            : Integer(274912523147183536LL);
    assert(maximum==expected);
    assert(maximum>candidate_allocation);
    std::cout<<"CANDIDATE_BUDGET_FAILURE_REPRODUCED\n";
  }
  if (joint_ledger) {
    std::cout<<"CORRELATED max "<<decimal(maximum)<<" fixed_tails "<<decimal(fixed_tails)
      <<" total_before_list "<<decimal(maximum+fixed_tails)
      <<" correlated_at_max "<<decimal(correlated(best_r,best_v))<<"\n";
  }
  if (!baseline && !custom_root && !custom_errors && !custom_padding && !joint_ledger && !band_rule) {
    std::cout<<(custom_sources ? "original_separate_chain_allocation " : "fixed_allocation ")
      <<decimal(candidate_allocation)
      <<(custom_sources ? " excess_before_chain_revision " : " excess ")
      <<decimal(maximum-candidate_allocation)<<"\n";
  }
  if (band_rule) std::cout<<"RESEARCH_BAND_RULE "<<band_rule<<"\n";
  std::cout<<"RESEARCH_EVALUATOR_ONLY; RETUNED_PROOF_GATES_AND_LEAN_UNCHECKED\n";
  return 0;
} catch (const std::exception& error) {
  std::cerr<<"INVALID_INPUT "<<error.what()<<"\n";
  return 64;
}
