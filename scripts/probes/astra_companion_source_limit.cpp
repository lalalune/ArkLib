// Bounded source-shape search at error cell 80791, NOT a protocol certificate.
// For each sampled (m,S), optimize L before minimizing the source's point charge.
// This improves on an integer grid of L/m ratios. No optimality over unsampled
// shapes, full phase envelopes, or mathematical counting arguments is claimed.
//
// clang++ -O3 -std=c++17 scripts/probes/astra_companion_source_limit.cpp -o /tmp/astra-source-limit
// /tmp/astra-source-limit 10 37 2320
// Optional fourth argument caps m (150..100000, default 100000).
// See docs/kb/proximity-astra-contact-strip-2026-09-04.md.

#define main phase_evaluator_main
#include "astra_companion_phases.cpp"
#undef main

namespace {
constexpr int errors = 80791, root_total = 6919, root_y = 136, root_r = 30;
constexpr std::int64_t prime = 2130706433;

int integer_argument(const char* value) {
  std::string text(value);
  std::size_t used = 0;
  int result = std::stoi(text, &used);
  if (used != text.size()) throw std::invalid_argument("expected an integer argument");
  return result;
}
}

int main(int argc, char** argv) try {
  if (argc != 4 && argc != 5)
    throw std::invalid_argument("usage: source-limit r v z [max_multiplicity]");
  int r = integer_argument(argv[1]), v = integer_argument(argv[2]);
  int z = integer_argument(argv[3]);
  int max_m = argc == 5 ? integer_argument(argv[4]) : 100000;
  if (r < 1 || r > root_r || v < 0 || v > root_y-r || z < 0 || z > root_total-r-v
      || max_m < 150 || max_m > 100000)
    throw std::invalid_argument("point or multiplicity outside the bounded research range");
  int t = r+v+z, y = r+v, tested = 0;
  std::vector<std::array<Integer,6>> passed;
  for (int m = 150; m <= max_m; m += m < 600 ? 5 : m < 1500 ? 20 : m < 12000 ? 100 : 1000) {
    std::int64_t d = std::int64_t(m)*(n-errors);
    int sy = int((d-1)/w);
    for (int s = std::max(root_r, m*305/1000-2); s <= m*311/1000+2;
         s += std::max(1, m/6000)) {
      if (d+s > std::int64_t(w)*(sy+1)) continue;
      int low = std::max({root_total, m+s, sy+1});
      int high = int(std::min({std::int64_t(20000000),
          (prime-1-std::int64_t(root_total)*sy)/root_y,
          (prime-1-std::int64_t(root_total)*s)/root_r}));
      if (high < low || std::int64_t(root_y)*s+std::int64_t(root_r)*sy >= prime) continue;

      // Both kernel counts are affine in L above m+S and the Y support cap.
      // Recompute the direct nullity for every returned witness below.
      auto nullity = [&](int L) { return coefficients(d,L,s)-n*rank_bound(m,L,s); };
      Integer at = nullity(low), slope = nullity(low+1)-at;
      if (slope <= 0) continue;
      auto band = [&](int L) {
        Integer cost = 0;
        int fuel = std::min({L/t,sy/y,s/r});
        std::int64_t cap = d-(w*y-r);
        for (int j = 1; j <= fuel; ++j) {
          cost += clipped_band(cap,n-errors-w+1,L-j*t,sy-j*y,s-j*r);
          cap = std::max<std::int64_t>(0,cap-(n-errors-w+1)-(w*y-r));
        }
        return cost;
      };
      auto slack = [&](int L) { return at+Integer(L-low)*slope-band(L); };

      // For each fixed strip channel, the number of Z coefficients is
      // max(0,L-constant). Thus band(L) is convex and the affine kernel
      // nullity minus band(L) is concave. These observations justify the
      // two binary searches numerically; the fast-formula identity and this
      // search have not been connected to a Lean optimization theorem.
      int lo = low, hi = high;
      while (lo < hi) {
        int mid = lo+(hi-lo)/2;
        if (band(mid+1)-band(mid) < slope) lo = mid+1;
        else hi = mid;
      }
      Integer best = slack(lo);
      assert((lo == low || slack(lo-1) <= best) && (lo == high || slack(lo+1) <= best));
      ++tested;
      if (best <= 0) continue;

      // On the increasing side of slack, find the first passing integer L.
      // At this fixed source shape, every potential coefficient is increasing
      // in L. This minimizes its point charge, not the whole phase envelope.
      int first = low, last = lo;
      while (first < last) {
        int mid = first+(last-first)/2;
        if (slack(mid) > 0) last = mid;
        else first = mid+1;
      }
      Integer value = slack(first), gap = nullity(first);
      assert(value > 0 && (first == low || slack(first-1) <= 0));
      assert(gap == at+Integer(first-low)*slope);
      Source source{m,first,sy,s,d,n-errors-w+1,gap,potential(errors,first,sy,s)};
      source.band_rule = 2;
      assert(routeable(source,r,v,z));
      passed.push_back({evaluate(source.potential,r,v,z),m,first,s,value,gap});
    }
  }
  std::sort(passed.begin(),passed.end());
  std::cout << "{\n  \"status\": \"BOUNDED_NUMERICAL_SOURCE_SEARCH_NO_PROTOCOL_PROOF\",\n"
      << "  \"point\": [" << r << ',' << v << ',' << z << "],\n"
      << "  \"max_multiplicity\": " << max_m << ",\n"
      << "  \"tested_shapes\": " << tested << ",\n"
      << "  \"passing_shapes\": " << passed.size() << ",\n  \"best_sources\": [\n";
  for (int i = 0; i < std::min<int>(20,passed.size()); ++i) {
    auto row = passed[i];
    if (i) std::cout << ",\n";
    std::cout << "    {\"source\": [" << decimal(row[1]) << ',' << decimal(row[2])
        << ',' << decimal(row[3]) << "], \"point_charge\": " << decimal(row[0])
        << ", \"strip_margin\": " << decimal(row[4])
        << ", \"kernel_nullity\": " << decimal(row[5]) << '}';
  }
  std::cout << "\n  ]\n}\n";
  return 0;
} catch (const std::exception& error) {
  std::cerr << "source search error: " << error.what() << '\n';
  return 1;
}
