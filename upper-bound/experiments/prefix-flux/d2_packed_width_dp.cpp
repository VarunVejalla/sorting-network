#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

static constexpr int N = 64;
static constexpr int ROWS = 4096;
static constexpr int EDGE = 40;
static constexpr int FINAL_SLOPE = 49;

static uint64_t interval_mask(int start, int width) {
  if (width == N) return ~uint64_t{0};
  if (width == 0) return 0;
  const uint64_t base = (uint64_t{1} << width) - 1;
  start %= N;
  if (start == 0) return base;
  return (base << start) | (base >> (N - start));
}

int main(int argc, char** argv) {
  std::array<int, EDGE> offsets = {
      0,27,42,52,58,23,38,49,20,62,18,36,16,47,14,13,12,11,10,9,
      8,7,6,5,4,3,2,1,28,29,30,31,32,33,34,35,36,37,38,39};
  if (argc > 1 && std::string(argv[1]) == "reverse")
    std::reverse(offsets.begin(), offsets.end());
  else if (argc > 1 && std::string(argv[1]) == "rotate")
    std::rotate(offsets.begin(), offsets.begin() + 17, offsets.end());

  // Output columns touched by the sorted one-prefix of width w in each row.
  std::vector<uint64_t> masks(ROWS * (N + 1));
  for (int r = 0; r < ROWS; ++r) {
    for (int w = 0; w <= N; ++w) {
      int start;
      if (r < EDGE) {
        start = offsets[r];
      } else if (r >= ROWS - EDGE) {
        const int from_bottom = ROWS - 1 - r;
        // The reflection packs the zero suffix at offsets[from_bottom];
        // the one-prefix occupies its complementary interval.
        start = (offsets[from_bottom] + N - w) % N;
      } else {
        start = (FINAL_SLOPE * r) % N;
      }
      masks[r * (N + 1) + w] = interval_mask(start, w);
    }
  }

  int globalBest = -1;
  int bestA = -1, bestB = -1;
  for (int a = 0; a < N; ++a) {
    for (int b = 0; b < N; ++b) {
      if (a == b) continue;
      std::array<int, N + 1> dp{};
      std::array<int, N + 1> next{};
      std::array<int, N + 1> suffix{};
      for (int r = 0; r < ROWS; ++r) {
        suffix[N] = dp[N];
        for (int w = N - 1; w >= 0; --w)
          suffix[w] = std::max(dp[w], suffix[w + 1]);
        const uint64_t* rowMasks = &masks[r * (N + 1)];
        const uint64_t bitA = uint64_t{1} << a;
        const uint64_t bitB = uint64_t{1} << b;
        for (int w = 0; w <= N; ++w) {
          const uint64_t m = rowMasks[w];
          const int gain = ((m & bitA) != 0) - ((m & bitB) != 0);
          next[w] = suffix[w] + gain;
        }
        dp.swap(next);
      }
      const int best = *std::max_element(dp.begin(), dp.end());
      if (best > globalBest) {
        globalBest = best;
        bestA = a;
        bestB = b;
      }
    }
  }

  int topCorrectionBest = -1, bottomCorrectionBest = -1;
  for (int a = 0; a < N; ++a) {
    for (int b = 0; b < N; ++b) {
      if (a == b) continue;
      std::array<int, N + 1> topDp{};
      std::array<int, N + 1> next{};
      std::array<int, N + 1> aggregate{};
      const uint64_t bitA = uint64_t{1} << a;
      const uint64_t bitB = uint64_t{1} << b;
      for (int r = 0; r < EDGE; ++r) {
        aggregate[N] = topDp[N];
        for (int w = N - 1; w >= 0; --w)
          aggregate[w] = std::max(aggregate[w + 1], topDp[w]);
        const int ordinaryStart = (FINAL_SLOPE * r) % N;
        for (int w = 0; w <= N; ++w) {
          const uint64_t packed = interval_mask(offsets[r], w);
          const uint64_t ordinary = interval_mask(ordinaryStart, w);
          const int gain =
              (((packed & bitA) != 0) - ((packed & bitB) != 0)) -
              (((ordinary & bitA) != 0) - ((ordinary & bitB) != 0));
          next[w] = aggregate[w] + gain;  // widths decrease top-to-bottom
        }
        topDp.swap(next);
      }
      topCorrectionBest = std::max(topCorrectionBest,
          *std::max_element(topDp.begin(), topDp.end()));

      std::array<int, N + 1> bottomDp{};
      for (int j = 0; j < EDGE; ++j) {
        // Bottom rows are processed from bottom to top: widths are nondecreasing.
        aggregate[0] = bottomDp[0];
        for (int w = 1; w <= N; ++w)
          aggregate[w] = std::max(aggregate[w - 1], bottomDp[w]);
        const int row = ROWS - 1 - j;
        const int ordinaryStart = (FINAL_SLOPE * row) % N;
        for (int w = 0; w <= N; ++w) {
          const int packedStart = (offsets[j] + N - w) % N;
          const uint64_t packed = interval_mask(packedStart, w);
          const uint64_t ordinary = interval_mask(ordinaryStart, w);
          const int gain =
              (((packed & bitA) != 0) - ((packed & bitB) != 0)) -
              (((ordinary & bitA) != 0) - ((ordinary & bitB) != 0));
          next[w] = aggregate[w] + gain;
        }
        bottomDp.swap(next);
      }
      bottomCorrectionBest = std::max(bottomCorrectionBest,
          *std::max_element(bottomDp.begin(), bottomDp.end()));
    }
  }

  // Restrict the input histogram to those admitting a cyclic height profile
  // with h[i] <= h[i-1] + 1. Such a histogram has contiguous support, so its
  // active row widths are strictly monotone. Only profiles whose active band
  // intersects the repaired top or bottom edge need new cases; all interior
  // profiles use the ordinary cyclic-layer theorem.
  constexpr int NEG = -1000000;
  int gradientBest = 0, gradientA = -1, gradientB = -1;
  int gradientSide = 0, gradientPhase = -1, gradientLength = 0;
  int edgeBest[N][N]{};
  for (int a = 0; a < N; ++a) {
    for (int b = 0; b < N; ++b) {
      if (a == b) continue;
      const uint64_t bitA = uint64_t{1} << a;
      const uint64_t bitB = uint64_t{1} << b;
      for (int minRow = 0; minRow < EDGE; ++minRow) {
        std::array<int, N + 1> dp;
        dp.fill(NEG);
        for (int step = 0; step < N - 1; ++step) {
          const int row = minRow + step;
          std::array<int, N + 1> next;
          next.fill(NEG);
          for (int w = 1; w < N; ++w) {
            const int start = row < EDGE ? offsets[row]
                                         : (FINAL_SLOPE * row) % N;
            const uint64_t m = interval_mask(start, w);
            const int gain = ((m & bitA) != 0) - ((m & bitB) != 0);
            int prior = 0;
            if (step > 0) {
              prior = NEG;
              for (int v = w + 1; v < N; ++v)
                prior = std::max(prior, dp[v]);
            }
            if (prior > NEG / 2) next[w] = prior + gain;
          }
          dp = next;
          const int value = *std::max_element(dp.begin(), dp.end());
          edgeBest[a][b] = std::max(edgeBest[a][b], value);
          if (value > gradientBest) {
            gradientBest = value;
            gradientA = a; gradientB = b; gradientSide = 1;
            gradientPhase = minRow; gradientLength = step + 1;
          }
          if (value <= NEG / 2) break;
        }
      }
      for (int bottomZeros = 0; bottomZeros < EDGE; ++bottomZeros) {
        std::array<int, N + 1> dp;
        dp.fill(NEG);
        for (int step = 0; step < N - 1; ++step) {
          const int fromBottom = bottomZeros + step;
          const int row = ROWS - 1 - fromBottom;
          std::array<int, N + 1> next;
          next.fill(NEG);
          for (int w = 1; w < N; ++w) {
            int start = (FINAL_SLOPE * row) % N;
            if (fromBottom < EDGE)
              start = (offsets[fromBottom] + N - w) % N;
            const uint64_t m = interval_mask(start, w);
            const int gain = ((m & bitA) != 0) - ((m & bitB) != 0);
            int prior = 0;
            if (step > 0) {
              prior = NEG;
              for (int v = 1; v < w; ++v)
                prior = std::max(prior, dp[v]);
            }
            if (prior > NEG / 2) next[w] = prior + gain;
          }
          dp = next;
          const int value = *std::max_element(dp.begin(), dp.end());
          edgeBest[a][b] = std::max(edgeBest[a][b], value);
          if (value > gradientBest) {
            gradientBest = value;
            gradientA = a; gradientB = b; gradientSide = 2;
            gradientPhase = bottomZeros; gradientLength = step + 1;
          }
          if (value <= NEG / 2) break;
        }
      }
    }
  }

  const std::array<int, N> ordinaryBudgetExcess = {
      0,9,11,8,3,5,7,9,6,8,3,5,9,11,6,1,
      10,12,9,4,6,8,10,7,2,4,6,10,5,7,2,11,
      8,10,5,7,9,11,8,3,5,7,11,6,1,3,12,9,
      4,6,8,10,7,9,4,6,8,12,7,2,4,13,10,5};
  int64_t pairRadiusSquares = 0;
  for (int a = 0; a < N; ++a) {
    for (int b = a + 1; b < N; ++b) {
      const int dAB = (b - a + N) % N;
      const int dBA = (a - b + N) % N;
      const int boundAB = std::max(ordinaryBudgetExcess[dAB], edgeBest[a][b]);
      const int boundBA = std::max(ordinaryBudgetExcess[dBA], edgeBest[b][a]);
      const int radius = std::max(boundAB, boundBA);
      pairRadiusSquares += int64_t(radius) * radius;
    }
  }

  std::vector<int> gradientWidths;
  std::array<int, N> gradientHeights{};
  std::array<int64_t, N> gradientLoads{};
  double gradientArea = 0.0;
  if (gradientSide == 2) {
    const int a = gradientA, b = gradientB, k = gradientPhase;
    const int length = gradientLength;
    std::vector<std::array<uint8_t, N + 1>> parent(length);
    std::array<int, N + 1> dp;
    dp.fill(NEG);
    std::array<int, N + 1> next{};
    std::array<int, N + 1> prefix{};
    std::array<int, N + 1> arg{};
    for (int step = 0; step < length; ++step) {
      prefix[0] = dp[0];
      arg[0] = 0;
      for (int w = 1; w <= N; ++w) {
        if (dp[w] > prefix[w - 1]) {
          prefix[w] = dp[w]; arg[w] = w;
        } else {
          prefix[w] = prefix[w - 1]; arg[w] = arg[w - 1];
        }
      }
      next.fill(NEG);
      const int fromBottom = k + step;
      const int row = ROWS - 1 - fromBottom;
      for (int w = 1; w < N; ++w) {
        int prior = step == 0 ? 0 : prefix[w - 1];
        if (step > 0 && prior <= NEG / 2) continue;
        const uint64_t m = masks[row * (N + 1) + w];
        const int gain = ((m >> a) & 1) - ((m >> b) & 1);
        next[w] = prior + gain;
        parent[step][w] = static_cast<uint8_t>(step == 0 ? 0 : arg[w - 1]);
      }
      dp = next;
    }
    int width = static_cast<int>(std::max_element(dp.begin(), dp.end()) - dp.begin());
    gradientWidths.resize(length);
    for (int step = length - 1; step >= 0; --step) {
      gradientWidths[step] = width;
      if (step > 0) width = parent[step][width];
    }
    std::array<int, N + 1> counts{};
    counts[length] = gradientWidths[0];
    for (int step = 1; step < length; ++step)
      counts[length - step] = gradientWidths[step] - gradientWidths[step - 1];
    counts[0] = N - gradientWidths.back();
    int cursor = 0;
    for (int value = length; value >= 0; --value)
      for (int n = 0; n < counts[value]; ++n)
        gradientHeights[cursor++] = value;
    for (int step = 0; step < length; ++step) {
      const int row = ROWS - 1 - k - step;
      const uint64_t m = masks[row * (N + 1) + gradientWidths[step]];
      for (int c = 0; c < N; ++c)
        gradientLoads[c] += (m >> c) & 1;
    }
    int64_t mass = 0, squares = 0;
    for (int64_t z : gradientLoads) { mass += z; squares += z * z; }
    gradientArea = 0.5 * (squares - double(mass) * mass / N);
  }

  // Recover a monotone width profile attaining the extremal pair.
  std::vector<std::array<uint8_t, N + 1>> parent(ROWS);
  std::array<int, N + 1> dp{};
  std::array<int, N + 1> next{};
  std::array<int, N + 1> suffix{};
  std::array<int, N + 1> arg{};
  for (int r = 0; r < ROWS; ++r) {
    suffix[N] = dp[N];
    arg[N] = N;
    for (int w = N - 1; w >= 0; --w) {
      if (dp[w] >= suffix[w + 1]) {
        suffix[w] = dp[w];
        arg[w] = w;
      } else {
        suffix[w] = suffix[w + 1];
        arg[w] = arg[w + 1];
      }
    }
    const uint64_t* rowMasks = &masks[r * (N + 1)];
    const uint64_t bitA = uint64_t{1} << bestA;
    const uint64_t bitB = uint64_t{1} << bestB;
    for (int w = 0; w <= N; ++w) {
      const uint64_t m = rowMasks[w];
      const int gain = ((m & bitA) != 0) - ((m & bitB) != 0);
      next[w] = suffix[w] + gain;
      parent[r][w] = static_cast<uint8_t>(arg[w]);
    }
    dp.swap(next);
  }
  int finalWidth = static_cast<int>(std::max_element(dp.begin(), dp.end()) - dp.begin());
  std::vector<int> widths(ROWS);
  for (int r = ROWS - 1; r >= 0; --r) {
    widths[r] = finalWidth;
    finalWidth = parent[r][finalWidth];
  }

  std::array<int64_t, N> loads{};
  for (int r = 0; r < ROWS; ++r) {
    const uint64_t m = masks[r * (N + 1) + widths[r]];
    for (int c = 0; c < N; ++c)
      loads[c] += (m >> c) & 1;
  }
  int64_t mass = 0, squares = 0;
  for (int64_t z : loads) {
    mass += z;
    squares += z * z;
  }
  const double area = 0.5 * (squares - double(mass) * mass / N);
  std::array<int, N> inputHeights{};
  for (int c = 0; c < N; ++c)
    for (int w : widths)
      inputHeights[c] += (w > c);

  std::cout << "exact monotone-width output-range bound=" << globalBest
            << " pair=" << bestA << "," << bestB
            << " rows=" << ROWS << " edge=" << EDGE
            << " slope=" << FINAL_SLOPE << " witness_Aw=" << area
            << " witness_range=" << (*std::max_element(loads.begin(), loads.end()) -
                                       *std::min_element(loads.begin(), loads.end()))
            << " top_edge_correction_range_bound=" << topCorrectionBest
            << " bottom_edge_correction_range_bound=" << bottomCorrectionBest
            << " gradient_profile_range_bound=" << gradientBest
            << " gradient_pair=" << gradientA << "," << gradientB
            << " gradient_side=" << gradientSide
            << " gradient_phase=" << gradientPhase
            << " gradient_active_rows=" << gradientLength
            << " gradient_witness_Aw=" << gradientArea
            << " gradient_pair_radius_square_sum=" << pairRadiusSquares
            << " gradient_pairwise_area_bound=" << (double(pairRadiusSquares) / 128.0)
            << "\ninput_heights=[";
  for (int c = 0; c < N; ++c) std::cout << (c ? "," : "") << inputHeights[c];
  std::cout << "]\noutput_heights=[";
  for (int c = 0; c < N; ++c) std::cout << (c ? "," : "") << loads[c];
  std::cout << "]\ngradient_heights=[";
  for (int c = 0; c < N; ++c) std::cout << (c ? "," : "") << gradientHeights[c];
  std::cout << "]\ngradient_output_heights=[";
  for (int c = 0; c < N; ++c) std::cout << (c ? "," : "") << gradientLoads[c];
  std::cout << "]\ngradient_widths=[";
  for (size_t i = 0; i < gradientWidths.size(); ++i)
    std::cout << (i ? "," : "") << gradientWidths[i];
  std::cout << "]\n";
}
