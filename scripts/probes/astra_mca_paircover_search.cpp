// Exhaustive mu_16 pair-cover syzygies over F_65537 at degree at most six.
// Fixed scope: |AB|=|AC|=5, |BC|=6, 1 in BC, and AB<AC to remove pair swap.
// No inference about another field, a larger domain, or a protocol score.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

namespace {
constexpr int prime = 65537, n = 16, full = (1 << n) - 1;
using Poly = std::array<int, n + 1>;
using Word = std::array<int, 7>;

int mod(std::int64_t value) {
  value %= prime;
  return static_cast<int>(value < 0 ? value + prime : value);
}
int times(int a, int b) { return mod(std::int64_t(a) * b); }
int power(int base, int exponent) {
  int result = 1;
  while (exponent) {
    if (exponent & 1) result = times(result, base);
    base = times(base, base);
    exponent >>= 1;
  }
  return result;
}
int evaluate(const Word &f, int x) {
  int result = 0;
  for (int i = 6; i >= 0; --i) result = mod(std::int64_t(result) * x + f[i]);
  return result;
}

int original_matrix_rank(const Poly &A, const Poly &B, const Poly &C,
                         const std::array<int, prime> &inverse) {
  // Independent reference: Gaussian elimination on all seven original
  // coefficient equations and all five unknowns, without the reduction.
  std::array<std::array<int, 5>, 7> matrix{};
  for (int i = 0; i < 7; ++i)
    matrix[i] = {i ? A[i - 1] : 0, A[i], i ? B[i - 1] : 0, B[i], C[i]};
  int rank = 0;
  for (int column = 0; column < 5; ++column) {
    int pivot = rank;
    while (pivot < 7 && matrix[pivot][column] == 0) ++pivot;
    if (pivot == 7) continue;
    std::swap(matrix[rank], matrix[pivot]);
    const int reciprocal = inverse[matrix[rank][column]];
    for (int j = column; j < 5; ++j) matrix[rank][j] = times(matrix[rank][j], reciprocal);
    for (int i = rank + 1; i < 7; ++i) {
      const int multiple = matrix[i][column];
      for (int j = column; j < 5; ++j)
        matrix[i][j] = mod(matrix[i][j] - std::int64_t(multiple) * matrix[rank][j]);
    }
    ++rank;
    if (column == 3) assert(rank == 4);
  }
  return rank;
}

struct Witness {
  int ab, ac, bc, a, b, c, d;
  Word f_b, f_c;
  std::array<int, 3> equality_counts{};
};

template <typename Container> void print_array(const Container &values) {
  std::cout << '[';
  bool first = true;
  for (const auto &value : values) {
    if (!first) std::cout << ',';
    std::cout << value;
    first = false;
  }
  std::cout << ']';
}
} // namespace

int main(int argc, char **argv) {
  if (argc > 2 || (argc == 2 && std::string(argv[1]) != "--cross-check")) {
    std::cerr << "Usage: astra_mca_paircover_search [--cross-check]\n";
    return 2;
  }
  const bool cross_check = argc == 2;
  for (int divisor = 2; divisor * divisor <= prime; ++divisor) assert(prime % divisor != 0);
  const int generator = power(3, (prime - 1) / n);
  assert(power(generator, n) == 1 && power(generator, n / 2) != 1);
  assert(power(generator, 8) == prime - 1); // Phi_16(generator)=0 for the char-zero corollary.
  assert(prime > n * n * n * n);
  std::array<int, n> nodes{};
  nodes[0] = 1;
  for (int i = 1; i < n; ++i) nodes[i] = times(nodes[i - 1], generator);
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < i; ++j) assert(nodes[i] != nodes[j]);

  std::array<int, prime> inverse{};
  inverse[1] = 1;
  for (int i = 2; i < prime; ++i)
    inverse[i] = mod(-std::int64_t(prime / i) * inverse[prime % i]);
  for (int i = 1; i < prime; ++i) assert(times(i, inverse[i]) == 1);

  std::vector<Poly> root_poly(1 << n);
  root_poly[0][0] = 1;
  for (int mask = 1; mask <= full; ++mask) {
    const int bit = __builtin_ctz(static_cast<unsigned>(mask));
    const int previous = mask & (mask - 1);
    const int degree = __builtin_popcount(static_cast<unsigned>(mask));
    for (int i = 0; i <= degree; ++i) {
      const int shifted = i ? root_poly[previous][i - 1] : 0;
      root_poly[mask][i] = mod(shifted - std::int64_t(nodes[bit]) * root_poly[previous][i]);
    }
  }
  assert(root_poly[full][0] == prime - 1 && root_poly[full][n] == 1);
  for (int i = 1; i < n; ++i) assert(root_poly[full][i] == 0);
  std::uint64_t root_polynomial_checks = 0;
  if (cross_check) {
    for (int mask = 0; mask <= full; ++mask) {
      const int degree = __builtin_popcount(static_cast<unsigned>(mask));
      if (degree != 5 && degree != 6) continue;
      assert(root_poly[mask][degree] == 1);
      for (int i = 0; i < n; ++i) {
        int value = 0;
        for (int j = degree; j >= 0; --j)
          value = mod(std::int64_t(value) * nodes[i] + root_poly[mask][j]);
        assert((value == 0) == bool(mask & (1 << i)));
      }
      ++root_polynomial_checks;
    }
    assert(root_polynomial_checks == 12376);
  }

  std::uint64_t partitions = 0, syzygies = 0, exact_paircovers = 0, triple_root_failures = 0;
  std::uint64_t reference_checks = 0;
  std::vector<Witness> witnesses;
  for (int ab = 0; ab <= full; ++ab) {
    if ((ab & 1) || __builtin_popcount(static_cast<unsigned>(ab)) != 5) continue;
    const int available = full ^ ab ^ 1;
    for (int ac = available; ac; ac = (ac - 1) & available) {
      if (ac <= ab || __builtin_popcount(static_cast<unsigned>(ac)) != 5) continue;
      const int bc = full ^ ab ^ ac;
      assert((bc & 1) && __builtin_popcount(static_cast<unsigned>(bc)) == 6);
      ++partitions;
      const Poly &A = root_poly[ab], &B = root_poly[ac], &C = root_poly[bc];
      std::array<int, 5> delta{}, v{}, q{};
      for (int i = 0; i < 5; ++i) delta[i] = mod(A[i] - B[i]);
      const int beta = mod(B[4] - C[5]);
      for (int i = 0; i < 5; ++i) {
        v[i] = mod((i ? delta[i - 1] : 0) - std::int64_t(delta[4]) * B[i]);
        q[i] = mod((i ? B[i - 1] : 0) - C[i] - std::int64_t(beta) * B[i]);
      }
      int first = 0;
      while (first < 5 && delta[first] == 0) ++first;
      assert(first < 5); // Distinct disjoint root sets give A != B.
      int second = 0, determinant = 0;
      for (; second < 5; ++second) {
        determinant = mod(std::int64_t(v[first]) * delta[second] -
                          std::int64_t(v[second]) * delta[first]);
        if (determinant) break;
      }
      assert(second < 5); // Otherwise a degree<=1 coprime-A/B relation exists.
      const int a = times(mod(std::int64_t(q[first]) * delta[second] -
                              std::int64_t(q[second]) * delta[first]), inverse[determinant]);
      const int b = times(mod(std::int64_t(v[first]) * q[second] -
                              std::int64_t(v[second]) * q[first]), inverse[determinant]);
      bool solves = true;
      for (int i = 0; i < 5; ++i)
        if (mod(std::int64_t(a) * v[i] + std::int64_t(b) * delta[i]) != q[i]) solves = false;
      if (cross_check) {
        const int rank = original_matrix_rank(A, B, C, inverse);
        assert(rank == (solves ? 4 : 5));
        ++reference_checks;
      }
      if (!solves) continue;
      ++syzygies;
      const int c = mod(-1 - a), d = mod(beta - std::int64_t(a) * delta[4] - b);
      Witness witness{ab, ac, bc, a, b, c, d, {}, {}, {}};
      for (int i = 0; i <= 6; ++i) {
        const int p = mod(std::int64_t(a) * (i ? A[i - 1] : 0) + std::int64_t(b) * A[i]);
        const int q_coefficient = mod(std::int64_t(c) * (i ? B[i - 1] : 0) + std::int64_t(d) * B[i]);
        assert(mod(p + q_coefficient + C[i]) == 0); // Original seven coefficients, lambda=1.
        witness.f_b[i] = mod(-p);
        witness.f_c[i] = q_coefficient;
      }
      bool exactly_two = true;
      for (int i = 0; i < n; ++i) {
        const int fa = 0, fb = evaluate(witness.f_b, nodes[i]), fc = evaluate(witness.f_c, nodes[i]);
        const bool eq_ab = fa == fb, eq_ac = fa == fc, eq_bc = fb == fc;
        witness.equality_counts[0] += eq_ab;
        witness.equality_counts[1] += eq_ac;
        witness.equality_counts[2] += eq_bc;
        if (int(eq_ab) + int(eq_ac) + int(eq_bc) != 1) exactly_two = false;
        assert(!(ab & (1 << i)) || eq_ab);
        assert(!(ac & (1 << i)) || eq_ac);
        assert(!(bc & (1 << i)) || eq_bc);
      }
      if (exactly_two) {
        assert((witness.equality_counts == std::array<int, 3>{5,5,6}));
        ++exact_paircovers;
        if (witnesses.size() < 32) witnesses.push_back(witness);
      } else {
        ++triple_root_failures;
      }
    }
  }
  assert(partitions == 378378 && exact_paircovers + triple_root_failures == syzygies);
  assert(!cross_check || reference_checks == partitions);
  std::cout << "{\n  \"status\":\"EXHAUSTIVE_MU16_ONE_PRIME_PAIR_SYZYGY_SEARCH\",\n"
            << "  \"prime\":" << prime << ",\n  \"domain_generator\":" << generator << ",\n  \"nodes\":";
  print_array(nodes);
  std::cout << ",\n  \"partitions_checked\":" << partitions
            << ",\n  \"syzygies\":" << syzygies
            << ",\n  \"exactly_two_paircovers\":" << exact_paircovers
            << ",\n  \"triple_root_failures\":" << triple_root_failures
            << ",\n  \"original_matrix_reference_checks\":" << reference_checks
            << ",\n  \"root_polynomial_reference_checks\":" << root_polynomial_checks
            << ",\n  \"witnesses_truncated\":" << (witnesses.size() < exact_paircovers ? "true" : "false")
            << ",\n  \"witnesses\":[";
  for (std::size_t i = 0; i < witnesses.size(); ++i) {
    if (i) std::cout << ',';
    const auto &w = witnesses[i];
    std::cout << "\n    {\"AB_mask\":" << w.ab << ",\"AC_mask\":" << w.ac << ",\"BC_mask\":" << w.bc
              << ",\"linear_coefficients_a_b_c_d_lambda\":";
    print_array(std::array<int, 5>{w.a,w.b,w.c,w.d,1});
    std::cout << ",\"codeword_A_ascending\":[0],\"codeword_B_ascending\":";
    print_array(w.f_b);
    std::cout << ",\"codeword_C_ascending\":";
    print_array(w.f_c);
    std::cout << ",\"equality_counts_AB_AC_BC\":";
    print_array(w.equality_counts);
    std::cout << '}';
  }
  std::cout << "\n  ]\n}\n";
}
