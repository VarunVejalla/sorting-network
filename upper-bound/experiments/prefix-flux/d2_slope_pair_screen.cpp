#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

static int max_difference(int n, int previous_slope, int final_slope, int delta) {
  const int inv = [&] {
    for (int x = 1; x < n; ++x)
      if ((x * final_slope) % n == 1) return x;
    return 0;
  }();
  std::vector<int> order(n), unary(n * (n + 1));
  for (int k = 0; k < n; ++k) order[k] = (previous_slope * k) % n;
  for (int c = 0; c < n; ++c) {
    const int at_zero = (inv * ((n - c) % n)) % n;
    const int at_delta = (inv * ((delta - c + n) % n)) % n;
    for (int h = 0; h <= n; ++h)
      unary[c * (n + 1) + h] = (at_zero < h) + (at_delta >= h);
  }

  const int neg = -1000000;
  int best = neg;
  std::vector<int> dp(n + 1), next(n + 1);
  std::vector<int> suffix(n + 1);
  for (int first = 0; first <= n; ++first) {
    std::fill(dp.begin(), dp.end(), neg);
    dp[first] = unary[order[0] * (n + 1) + first];
    for (int pos = 1; pos < n; ++pos) {
      const int c = order[pos];
      std::fill(next.begin(), next.end(), neg);
      int run = neg;
      for (int prev = n; prev >= 0; --prev) {
        run = std::max(run, dp[prev]);
        suffix[prev] = run;
      }
      for (int h = 0; h <= n; ++h) {
        const int prior = std::max(0, h - 1);
        const int value = suffix[prior];
        if (value > neg / 2)
          next[h] = value + unary[c * (n + 1) + h];
      }
      dp.swap(next);
    }
    for (int last = 0; last <= n; ++last)
      if (first <= last + 1)
        best = std::max(best, dp[last]);
  }
  return best - n;
}

int main(int argc, char** argv) {
  std::vector<std::tuple<int,int,int,int,int>> results;
  const int n = 64;
  if (argc == 3) {
    const int a = std::stoi(argv[1]);
    const int b = std::stoi(argv[2]);
    std::array<int,64> bound{};
    for (int d = 1; d < n; ++d)
      bound[d] = max_difference(n, a, b, d);
    int sum = 0, range = 0;
    for (int d = 1; d < n; ++d) {
      const int symmetric = std::max(bound[d], bound[n-d]);
      sum += symmetric * symmetric;
      range = std::max(range, symmetric);
    }
    std::cout << "previous=" << a << " final=" << b
              << " pairwise_square_sum=" << sum
              << " Aw_upper=" << static_cast<double>(sum) / 4
              << " Aw_per_column_upper=" << static_cast<double>(sum) / 256
              << " range=" << range << '\n';
    return 0;
  }
  for (int a = 1; a < n; a += 2) {
    for (int b = 1; b < n; b += 2) {
      if (std::gcd(n,a) != 1 || std::gcd(n,b) != 1) continue;
      std::array<int,64> bound{};
      for (int d = 1; d < n; ++d) {
        bound[d] = max_difference(n,a,b,d);
      }
      int range = 0, areaNumerator = 0, arg = 0;
      for (int d = 1; d < n; ++d) {
        const int symmetric = std::max(bound[d], bound[n-d]);
        if (symmetric > range) range = symmetric, arg = d;
        areaNumerator += symmetric * symmetric;
      }
      results.emplace_back(areaNumerator,range,a,b,arg);
    }
  }
  std::sort(results.begin(), results.end());
  const int minimum = std::get<0>(results.front());
  const int minimumRange = std::get<1>(*std::min_element(results.begin(), results.end(),
      [](const auto& x, const auto& y) { return std::get<1>(x) < std::get<1>(y); }));
  const auto minimizers = std::count_if(results.begin(), results.end(),
      [minimum](const auto& r) { return std::get<0>(r) == minimum; });
  std::cout << "scanned=" << results.size() << " minimum_pairwise_area_numerator="
            << minimum << " area_minimizers=" << minimizers
            << " minimum_range=" << minimumRange << '\n';
  for (int i = 0; i < std::min<int>(20, results.size()); ++i) {
    auto [areaNumerator,range,a,b,arg] = results[i];
    std::cout << "n=64 previous=" << a << " final=" << b
              << " range=" << range << " area_per_column_upper="
              << static_cast<double>(areaNumerator) / (4*n)
              << " arg=" << arg << '\n';
  }
}
