#include <algorithm>
#include <limits>

#if defined(_WIN32)
#define UB28_EXPORT __declspec(dllexport)
#else
#define UB28_EXPORT __attribute__((visibility("default")))
#endif

// Fused max-plus update for one reverse randomized compare-split pass.
// `flat` and `out` have shape (grid + 1, grid + 1, rest), with the last
// dimension contiguous. The packed kernels list one square matrix for each
// total count from 0 through 2*grid; each matrix uses its feasible count range.
extern "C" UB28_EXPORT void ub28_reverse_maxplus(
    const double* flat, double* out, const double* kernels,
    int grid, int rest) {
  const double neg_inf = -std::numeric_limits<double>::infinity();
  const int side = grid + 1;
  std::fill(out, out + side * side * rest, neg_inf);
  int kernel_offset = 0;
  for (int total = 0; total <= 2 * grid; ++total) {
    const int lo = total > grid ? total - grid : 0;
    const int hi = total < grid ? total : grid;
    const int len = hi - lo + 1;
#pragma omp parallel for schedule(static)
    for (int out_count = lo; out_count <= hi; ++out_count) {
      double* dst = out + (out_count * side + total - out_count) * rest;
      const int kernel_row = kernel_offset + (out_count - lo) * len;
      for (int in_count = lo; in_count <= hi; ++in_count) {
        const double weight = kernels[kernel_row + in_count - lo];
        const double* src = flat + (in_count * side + total - in_count) * rest;
        for (int z = 0; z < rest; ++z) {
          const double candidate = src[z] + weight;
          if (candidate > dst[z]) dst[z] = candidate;
        }
      }
    }
    kernel_offset += len * len;
  }
}
