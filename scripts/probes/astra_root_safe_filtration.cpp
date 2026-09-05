// Exhaust all first-order dimension certificates in the stated bounded class.
// No actual-kernel nonexistence or prize bound follows. See the accompanying KB note.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>

using Int = __int128_t;
struct Event {
  int64_t degree, coefficientSlope, coefficientMomentSlope, rank, rankMoment;
};
struct Counts {
  Int endpoints = 0;
  Int fullDegreeCaps = 0;
  bool positive = false;
};

static int64_t localChannel(int64_t h, int64_t r, int64_t m, int64_t s) {
  return std::min(std::max(int64_t(0), std::min(h, r) - std::max(int64_t(0), h-s) + 1), m-r);
}

static bool directPositive(int64_t n, int64_t w, int64_t a, int64_t m, int64_t s) {
  // Independent enumeration of every D, h, j, r in the small controls.
  for (int64_t d = 1; d <= m*a; ++d) {
    int64_t H = (d+s-1)/w;
    Int slope = 0, value = 0;
    for (int64_t h = 0; h <= H; ++h) {
      Int c = 0, rank = 0;
      for (int64_t j = 0; j <= std::min(s,h); ++j)
        c += std::max(int64_t(0), d-w*h+j);
      for (int64_t r = 0; r < m; ++r)
        if (r+(w-1)*h < d) rank += localChannel(h,r,m,s);
      slope += c-n*rank;
      value += slope;
      if (value > 0) return true;
    }
    if (slope > 0) return true; // The remaining total-degree tail is affine.
  }
  return false;
}

static Counts certificate(int64_t n, int64_t w, int64_t a, int64_t m, int64_t s) {
  // This inequality is used to transport T<H(D) to D=m*a; see the proof.
  assert(w > s && m <= w-s+1);
  const int64_t maxD = m*a, maxH = (maxD+s-1)/w;
  std::vector<Event> events;
  std::vector<Int> coefficients(maxH+1), ranks(maxH+1);
  for (int64_t h = 0; h <= maxH; ++h) {
    for (int64_t j = 0; j <= std::min(s,h); ++j) {
      const int64_t d = w*h-j;
      if (d <= maxD) events.push_back({d,1,h,0,0});
      coefficients[h] += std::max(int64_t(0),maxD-d);
    }
    // H(D) changes here. Include it even when the bound overestimates the support.
    const int64_t change = w*h-s+1;
    if (change > 0 && change <= maxD) events.push_back({change,0,0,0,0});
  }
  for (int64_t h = 0; h <= std::min(maxH,m+s-1); ++h) {
    for (int64_t r = 0; r < m; ++r) {
      const int64_t value = localChannel(h,r,m,s), d = r+(w-1)*h+1;
      if (value && d <= maxD) {
        events.push_back({d,0,0,value,h*value});
        ranks[h] += value;
      }
    }
  }
  events.push_back({maxD,0,0,0,0});
  std::sort(events.begin(),events.end(),[](const Event &x,const Event &y) {
    return x.degree < y.degree;
  });
  Counts result;
  Int c = 0, cm = 0, rank = 0, rm = 0, coefficientSlope = 0, momentSlope = 0;
  int64_t previous = 0;
  auto inspect = [&](int64_t d, Int cNow, Int cmNow) {
    if (d <= 0) return;
    ++result.endpoints;
    const Int B = cNow-n*rank, M = cmNow-n*rm;
    const int64_t H = (d+s-1)/w;
    if (B > 0 || (H+1)*B-M > 0) result.positive = true;
  };
  for (size_t i = 0; i < events.size();) {
    const int64_t d = events[i].degree;
    if (d > previous)
      inspect(d-1,c+coefficientSlope*(d-1-previous),cm+momentSlope*(d-1-previous));
    c += coefficientSlope*(d-previous);
    cm += momentSlope*(d-previous);
    previous = d;
    while (i < events.size() && events[i].degree == d) {
      coefficientSlope += events[i].coefficientSlope;
      momentSlope += events[i].coefficientMomentSlope;
      rank += events[i].rank;
      rm += events[i].rankMoment;
      ++i;
    }
    inspect(d,c,cm);
  }
  // These checks cover T<H(D) for every smaller D by monotonicity after saturation.
  Int prefix = 0, value = 0;
  for (int64_t T = 0; T <= maxH; ++T) {
    prefix += coefficients[T]-n*ranks[T];
    value += prefix;
    ++result.fullDegreeCaps;
    if (value > 0) result.positive = true;
  }
  return result;
}

int main() {
  int controls = 0, positiveControls = 0;
  for (int64_t w : {5,8,12}) for (int64_t n : {w+2,w+5,w+9}) {
    for (int64_t a : {w+1,n-1}) for (int64_t s = 0; s <= 3; ++s) {
      for (int64_t m = 1; m <= std::min(int64_t(5),w-s+1); ++m) {
        const bool reference = directPositive(n,w,a,m,s);
        assert(certificate(n,w,a,m,s).positive == reference);
        ++controls;
        positiveControls += reference;
      }
    }
  }
  assert(controls == 342 && positiveControls == 103);
  const int64_t n = 262144, w = 131071, a = 181353;
  Int endpointCount = 0, capCount = 0;
  for (int64_t s = 0; s <= 9; ++s) {
    Int endpoints = 0, caps = 0;
    for (int64_t m = 1; m <= 500; ++m) {
      const auto row = certificate(n,w,a,m,s);
      if (row.positive) {
        std::cerr << "Positive certificate found at R cap " << s << ", m=" << m << "\n";
        return 1;
      }
      endpoints += row.endpoints;
      caps += row.fullDegreeCaps;
    }
    endpointCount += endpoints;
    capCount += caps;
    std::cout << "{\"R_cap\":" << s << ",\"endpoint_checks\":" << int64_t(endpoints)
              << ",\"full_D_total_caps\":" << int64_t(caps) << ",\"positive\":false}\n";
  }
  assert(endpointCount == 438215244 && capCount == 1735490);
  std::cout << "{\"status\":\"PASS_BOUNDED_FIRST_ORDER_MARGIN_EXCLUSION\",\"small_controls\":"
            << controls << ",\"positive_small_controls\":" << positiveControls
            << ",\"max_m\":500,\"max_R_cap\":9,\"endpoint_checks\":" << int64_t(endpointCount)
            << ",\"full_D_total_caps\":" << int64_t(capCount)
            << ",\"all_D_up_to_mA\":true,\"all_total_caps\":true,\"actual_kernels_excluded\":false}\n";
}
