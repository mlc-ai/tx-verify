// SPDX-License-Identifier: Apache-2.0
// Exhaust the positive normal binary32 inputs to the compiled PTX reciprocal square root.
#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include <vector>

using U64 = unsigned long long;
constexpr unsigned first = 0x00800000;
constexpr unsigned stop = 0x7f800000;
constexpr int threads = 256;
constexpr int blocks = 4096;

struct Extreme {
  U64 delta;
  unsigned input;
  unsigned output;
};

struct Summary {
  unsigned visited, invalid;
  Extreme below, above;
};

__host__ __device__ Extreme largest(Extreme a, Extreme b) {
  if (a.delta != b.delta) return a.delta > b.delta ? a : b;
  return a.input < b.input ? a : b;
}

__host__ __device__ Summary merge(Summary a, Summary b) {
  return {a.visited + b.visited, a.invalid + b.invalid,
          largest(a.below, b.below), largest(a.above, b.above)};
}

__global__ void sweep(Summary* summaries) {
  __shared__ Summary partial[threads];
  Summary result{0, 0, {0, ~0u, 0}, {0, ~0u, 0}};
  for (unsigned x = first + blockIdx.x * blockDim.x + threadIdx.x; x < stop;
       x += gridDim.x * blockDim.x) {
    ++result.visited;
    float root;
    asm volatile("rsqrt.approx.ftz.f32 %0, %1;" : "=f"(root) : "f"(__uint_as_float(x)));
    unsigned y = __float_as_uint(root);
    if (y < first || y >= stop) {
      ++result.invalid;
      continue;
    }
    const U64 mx = (x & (first - 1)) + first;
    const U64 my = (y & (first - 1)) + first;
    const int k = 450 - static_cast<int>(x >> 23) - 2 * static_cast<int>(y >> 23);
    // y^2 * x = (mx * my^2) / 2^k. Outside this exponent range it is far from one.
    if (k < 69 || k > 72) {
      ++result.invalid;
      continue;
    }
    const U64 product = mx * (my * my);
    const U64 high = __umul64hi(mx, my * my);
    const int shift = 72 - k;
    const U64 lo = product << shift;
    const U64 hi = shift ? (high << shift) | (product >> (64 - shift)) : high;
    // 2^72 occupies high word 256. Save the exact deviation and its generating words.
    if (hi == 256) {
      result.above = largest(result.above, {lo, x, y});
    } else if (hi == 255 && lo != 0) {
      result.below = largest(result.below, {0ULL - lo, x, y});
    } else {
      ++result.invalid;
    }
  }
  partial[threadIdx.x] = result;
  __syncthreads();
  for (unsigned stride = blockDim.x / 2; stride > 0; stride /= 2) {
    if (threadIdx.x < stride) {
      partial[threadIdx.x] = merge(partial[threadIdx.x], partial[threadIdx.x + stride]);
    }
    __syncthreads();
  }
  if (threadIdx.x == 0) summaries[blockIdx.x] = partial[0];
}

void check(cudaError_t code) {
  if (code != cudaSuccess) {
    std::fprintf(stderr, "%s\n", cudaGetErrorString(code));
    std::exit(EXIT_FAILURE);
  }
}

void print_extreme(const char* name, Extreme e) {
  std::printf("\"%s\":{\"delta\":%llu,\"input\":%u,\"output\":%u}", name, e.delta, e.input, e.output);
}

int main() {
  cudaDeviceProp device{};
  check(cudaGetDeviceProperties(&device, 0));
  Summary* gpu = nullptr;
  check(cudaMalloc(&gpu, blocks * sizeof(Summary)));
  sweep<<<blocks, threads>>>(gpu);
  check(cudaGetLastError());
  std::vector<Summary> host(blocks);
  check(cudaMemcpy(host.data(), gpu, blocks * sizeof(Summary), cudaMemcpyDeviceToHost));
  check(cudaFree(gpu));
  Summary all{0, 0, {0, ~0u, 0}, {0, ~0u, 0}};
  for (auto b : host) all = merge(all, b);
  std::printf("{\"device\":\"%s\",\"visited\":%u,\"invalid\":%u,", device.name, all.visited, all.invalid);
  print_extreme("below", all.below);
  std::printf(",");
  print_extreme("above", all.above);
  std::printf("}\n");
  return all.visited == stop - first && all.invalid == 0 ? EXIT_SUCCESS : EXIT_FAILURE;
}
