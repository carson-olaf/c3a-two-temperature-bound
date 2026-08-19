#include <gmpxx.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <queue>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace fs = std::filesystem;

namespace {
constexpr int B = 80;
constexpr int DEGREE = 160;
constexpr int X_NUM = 8149;
constexpr int X_DEN = 10000;
constexpr int Y_NUM = 42571;
constexpr int Y_DEN = 50000;
constexpr int RATE_NUM = 249293;
constexpr int RATE_DEN = 10000;
constexpr int TARGET_ALPHA_NUM = 10709;
constexpr int TARGET_ALPHA_DEN = 50000;
constexpr int EXPECTED_MASK_SIZE = 75;
constexpr int EXPECTED_SUM_SIZE = 155;
constexpr int EXPECTED_DIFF_SIZE = 161;
constexpr int INF = 1'000'000'000;
constexpr int LOG_TERMS = 120;
const std::array<int, 2> GENS = {4, 5};

const mpq_class PMINUS_LO(mpz_class("5214722552042"), mpz_class("1000000000000"));
const mpq_class PMINUS_HI(mpz_class("5214722552043"), mpz_class("1000000000000"));
const mpq_class PPLUS_LO(mpz_class("3661102186601"), mpz_class("1000000000000"));
const mpq_class PPLUS_HI(mpz_class("3661102186602"), mpz_class("1000000000000"));
const mpq_class MU_LO(mpz_class("7643532314898"), mpz_class("1000000000000"));
const mpq_class MU_HI(mpz_class("7643532314899"), mpz_class("1000000000000"));

struct Interval {
  mpq_class lo;
  mpq_class hi;
};

void require(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error(message);
}

std::vector<int> apery_mask() {
  // Independent reconstruction: shortest paths on residues modulo 4.
  const int multiplicity = GENS[0];
  using Node = std::pair<long long, int>;
  const long long LINF = std::numeric_limits<long long>::max() / 4;
  std::vector<long long> dist(multiplicity, LINF);
  std::priority_queue<Node, std::vector<Node>, std::greater<Node>> pq;
  dist[0] = 0;
  pq.push({0, 0});
  while (!pq.empty()) {
    auto [value, residue] = pq.top();
    pq.pop();
    if (value != dist[residue]) continue;
    for (int g : GENS) {
      long long nv = value + g;
      int nr = static_cast<int>(nv % multiplicity);
      if (nv < dist[nr]) {
        dist[nr] = nv;
        pq.push({nv, nr});
      }
    }
  }
  std::vector<int> mask;
  for (int n = 0; n <= B; ++n) {
    if (dist[n % multiplicity] <= n) mask.push_back(n);
  }
  return mask;
}

struct Supports {
  std::vector<unsigned char> present;
  std::vector<unsigned char> sum_present;
  std::vector<int> kappa;
};

Supports intersection_reconstruction(const std::vector<int>& mask) {
  Supports out;
  out.present.assign(B + 1, 0);
  out.sum_present.assign(DEGREE + 1, 0);
  out.kappa.assign(B + 1, INF);
  for (int a : mask) out.present[a] = 1;

  // Sum support is reconstructed by shifted Boolean unions.
  for (int a : mask) {
    for (int b = 0; b <= B; ++b) {
      if (out.present[b]) out.sum_present[a + b] = 1;
    }
  }

  // For each d, scan the lower witness b in increasing order.  The first
  // intersection b,b+d in M gives the exact minimum d+2b.
  for (int d = 0; d <= B; ++d) {
    for (int b = 0; b + d <= B; ++b) {
      if (out.present[b] && out.present[b + d]) {
        out.kappa[d] = d + 2 * b;
        break;
      }
    }
  }
  return out;
}

struct Values {
  mpz_class plus_num;
  mpz_class plus_den;
  mpz_class minus_num;
  mpz_class minus_den;
  mpz_class moment_num;
};

std::pair<mpz_class, mpz_class> sparse_eval(const std::vector<int>& coeff,
                                            int num, int den) {
  mpz_class common_den;
  mpz_ui_pow_ui(common_den.get_mpz_t(), den, DEGREE);
  mpz_class monomial = common_den;
  mpz_class value = 0;
  for (int e = 0; e <= DEGREE; ++e) {
    if (coeff[e] != 0) value += coeff[e] * monomial;
    if (e != DEGREE) {
      monomial *= num;
      require(mpz_divisible_ui_p(monomial.get_mpz_t(), den) != 0,
              "non-exact monomial recurrence");
      mpz_divexact_ui(monomial.get_mpz_t(), monomial.get_mpz_t(), den);
    }
  }
  return {value, common_den};
}

Values evaluate(const Supports& s) {
  std::vector<int> plus(DEGREE + 1, 0);
  std::vector<int> minus(DEGREE + 1, 0);
  std::vector<int> moment(DEGREE + 1, 0);
  for (int e = 0; e <= DEGREE; ++e) if (s.sum_present[e]) plus[e] = 1;
  minus[0] = 1;
  for (int d = 1; d <= B; ++d) {
    require(s.kappa[d] < INF, "missing difference");
    minus[s.kappa[d]] += 2;
  }
  for (int e = 0; e <= DEGREE; ++e) moment[e] = e * minus[e];

  auto [pnum, pden] = sparse_eval(plus, Y_NUM, Y_DEN);
  auto [mnum, mden] = sparse_eval(minus, X_NUM, X_DEN);
  auto [momnum, momden] = sparse_eval(moment, X_NUM, X_DEN);
  require(momden == mden, "moment denominator mismatch");
  return {pnum, pden, mnum, mden, momnum};
}

Interval atanh_log_unit(const mpq_class& q, int terms = LOG_TERMS) {
  require(q > 0, "log input must be positive");
  const mpq_class z = (q - 1) / (q + 1);
  const mpq_class z2 = z * z;
  mpq_class partial = 0;
  mpq_class zpow = z;
  for (int j = 0; j < terms; ++j) {
    partial += zpow / (2 * j + 1);
    zpow *= z2;
  }
  const mpq_class approximation = 2 * partial;
  const mpq_class abszpow = zpow >= 0 ? zpow : -zpow;
  const mpq_class remainder =
      2 * abszpow / ((2 * terms + 1) * (1 - z2));
  return {approximation - remainder, approximation + remainder};
}

int floor_log2_q(const mpq_class& x) {
  require(x > 0, "floor_log2 input must be positive");
  const mpz_class n = x.get_num();
  const mpz_class d = x.get_den();
  int k = static_cast<int>(mpz_sizeinbase(n.get_mpz_t(), 2))
        - static_cast<int>(mpz_sizeinbase(d.get_mpz_t(), 2));
  if (k >= 0) {
    mpz_class rhs = d << k;
    if (n < rhs) --k;
  } else {
    mpz_class lhs = n << (-k);
    if (lhs < d) --k;
  }
  return k;
}

Interval log_bounds(const mpq_class& x) {
  require(x > 0, "log input must be positive");
  if (x == 1) return {0, 0};
  if (x < 1) {
    Interval inv = log_bounds(1 / x);
    return {-inv.hi, -inv.lo};
  }
  const int k = floor_log2_q(x);
  mpq_class two_to_k;
  if (k >= 0) {
    two_to_k = mpq_class(mpz_class(1) << k);
  } else {
    two_to_k = mpq_class(1, mpz_class(1) << (-k));
  }
  const mpq_class reduced = x / two_to_k;
  const Interval l2 = atanh_log_unit(mpq_class(2));
  const Interval lr = atanh_log_unit(reduced);
  if (k >= 0) return {k * l2.lo + lr.lo, k * l2.hi + lr.hi};
  return {k * l2.hi + lr.lo, k * l2.lo + lr.hi};
}

std::string decimal_approx(const mpq_class& q, int digits = 30) {
  mpf_class x(q, static_cast<mp_bitcnt_t>(digits * 4 + 64));
  std::ostringstream out;
  out << std::fixed << std::setprecision(digits) << x;
  return out.str();
}

unsigned long bit_length(const mpz_class& x) {
  require(x > 0, "bit length needs positive integer");
  return mpz_sizeinbase(x.get_mpz_t(), 2);
}

void write_certificate(const fs::path& dir, const std::vector<int>& mask,
                       const Supports& s, const mpz_class& N,
                       const mpz_class& L) {
  fs::create_directories(dir);
  {
    std::ofstream f(dir / "mask.txt");
    for (int n : mask) f << n << '\n';
  }
  {
    std::ofstream f(dir / "sum_support.txt");
    for (int e = 0; e <= DEGREE; ++e) if (s.sum_present[e]) f << e << '\n';
  }
  {
    std::ofstream f(dir / "difference_costs.tsv");
    f << "d\tkappa\n";
    for (int d = -B; d <= B; ++d) f << d << '\t' << s.kappa[std::abs(d)] << '\n';
  }
  {
    std::ofstream f(dir / "N.txt"); f << N << '\n';
  }
  {
    std::ofstream f(dir / "L.txt"); f << L << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  fs::path emit_dir;
  if (argc == 3 && std::string(argv[1]) == "--emit") {
    emit_dir = argv[2];
  } else if (argc != 1) {
    std::cerr << "usage: " << argv[0] << " [--emit DIRECTORY]\n";
    return 2;
  }

  const std::vector<int> mask = apery_mask();
  require(static_cast<int>(mask.size()) == EXPECTED_MASK_SIZE,
          "mask size mismatch");
  require(mask.front() == 0 && mask.back() == B, "mask endpoint mismatch");
  const std::vector<int> expected_gaps = {1, 2, 3, 6, 7, 11};
  std::vector<int> gaps;
  for (int n = 1; n < 12; ++n) {
    if (!std::binary_search(mask.begin(), mask.end(), n)) gaps.push_back(n);
  }
  require(gaps == expected_gaps, "semigroup gap mismatch");

  const Supports s = intersection_reconstruction(mask);
  int sum_size = 0;
  for (unsigned char yes : s.sum_present) sum_size += yes != 0;
  int diff_size = 1;
  for (int d = 1; d <= B; ++d) diff_size += 2 * (s.kappa[d] < INF);
  require(sum_size == EXPECTED_SUM_SIZE, "sum support size mismatch");
  require(diff_size == EXPECTED_DIFF_SIZE, "difference support size mismatch");
  require(s.kappa[1] == 9 && s.kappa[2] == 18 && s.kappa[3] == 13 &&
          s.kappa[6] == 14 && s.kappa[7] == 17 && s.kappa[11] == 19,
          "special kappa values mismatch");
  for (int d = 12; d <= B; ++d) require(s.kappa[d] == d, "tail kappa mismatch");

  const Values v = evaluate(s);
  const mpq_class pminus(v.minus_num, v.minus_den);
  const mpq_class pplus(v.plus_num, v.plus_den);
  const mpq_class mu(v.moment_num, v.minus_num);

  require(PMINUS_LO < pminus && pminus < PMINUS_HI,
          "Pminus rational enclosure failed");
  require(PPLUS_LO < pplus && pplus < PPLUS_HI,
          "Pplus rational enclosure failed");
  require(MU_LO < mu && mu < MU_HI, "mu rational enclosure failed");

  const Interval lpm_lo = log_bounds(PMINUS_LO);
  const Interval lpm_hi = log_bounds(PMINUS_HI);
  const Interval lpp_lo = log_bounds(PPLUS_LO);
  const Interval lpp_hi = log_bounds(PPLUS_HI);
  const Interval lx = log_bounds(mpq_class(X_DEN, X_NUM));
  const Interval ly = log_bounds(mpq_class(Y_DEN, Y_NUM));
  const Interval lr = log_bounds(mpq_class(RATE_NUM, RATE_DEN));

  const Interval rho = {
      lpm_lo.lo + MU_LO * lx.lo,
      lpm_hi.hi + MU_HI * lx.hi,
  };
  const Interval sigma = {
      lpp_lo.lo + MU_LO * ly.lo,
      lpp_hi.hi + MU_HI * ly.hi,
  };
  const mpq_class alpha(TARGET_ALPHA_NUM, TARGET_ALPHA_DEN);
  const mpq_class admissibility_margin = lr.lo - rho.hi;
  const mpq_class exponent_rate_margin = rho.lo - sigma.hi - alpha * lr.hi;
  require(admissibility_margin > 0, "rho < log R failed");
  require(exponent_rate_margin > 0, "exponent > 1.21418 failed");

  require(mpz_even_p(v.moment_num.get_mpz_t()) != 0,
          "finite budget not integral");
  const mpz_class N = v.minus_num;
  const mpz_class L = v.moment_num / 2;
  require(L >= 4 && N >= 2, "finite parameters too small");
  require(std::gcd(RATE_NUM, RATE_DEN) == 1,
          "rate fraction not reduced");
  require(mpz_class(RATE_NUM) * RATE_NUM >
              mpz_class(2 * B + 1) * RATE_DEN * RATE_DEN,
          "prime threshold does not imply p>2B");

  const Interval l2 = log_bounds(mpq_class(2));
  const unsigned long bits = bit_length(N + 1);
  const mpq_class rhs =
      (mpq_class(EXPECTED_DIFF_SIZE * bits + 2) + 2 * alpha) * l2.hi;
  const mpq_class lhs = mpq_class(N) * exponent_rate_margin;
  require(lhs > rhs, "finite-size correction failed");

  if (!emit_dir.empty()) write_certificate(emit_dir, mask, s, N, L);

  std::cout << "INDEPENDENT C++/GMP TWO-TEMPERATURE RECONSTRUCTION: PASS\n";
  std::cout << "algorithm: Apery shortest paths + support intersections + sparse monomials\n";
  std::cout << "|M|=" << mask.size() << " |M+M|=" << sum_size
            << " |M-M|=" << diff_size << "\n";
  std::cout << "rho < log(249293/10000): PASS\n";
  std::cout << "fixed-rate exponent > 1.21418: PASS\n";
  std::cout << "finite-size correction: PASS\n";
  std::cout << "admissibility margin lower > "
            << decimal_approx(admissibility_margin) << "\n";
  std::cout << "exponent-rate margin lower > "
            << decimal_approx(exponent_rate_margin) << "\n";
  std::cout << "finite N_bits=" << bit_length(N)
            << " L_bits=" << bit_length(L) << "\n";
  std::cout << "CERTIFIED NUMERICAL HYPOTHESES FOR THE WRITTEN THEOREM: C_3a > 1.21418\n";
  return 0;
}
