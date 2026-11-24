// SPDX-License-Identifier: Apache-2.0

// Runs tc_gemm.ptx on the GPU and compares D with a CPU reference.
// Build: nvcc -o run_tc_gemm run_tc_gemm.cu -lcuda
// Run:   ./run_tc_gemm tc_gemm.ptx [seed]

#include <cuda.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <vector>

#define CHECK(x)                                                         \
  do {                                                                   \
    CUresult r = (x);                                                    \
    if (r != CUDA_SUCCESS) {                                             \
      const char* s = nullptr;                                           \
      cuGetErrorString(r, &s);                                           \
      std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?");          \
      return 1;                                                          \
    }                                                                    \
  } while (0)

constexpr int M = 128, N = 8, K = 32;

// The K-major, no-swizzle canonical layouts used by the kernel's descriptors.
size_t offA(int i, int k) { return 16 * (i % 8) + 256 * (i / 8) + (k % 16) + 128 * (k / 16); }
size_t offB(int k, int j) { return 16 * j + (k % 16) + 128 * (k / 16); }

int main(int argc, char** argv) {
  if (argc < 2) {
    std::fprintf(stderr, "usage: %s tc_gemm.ptx [seed]\n", argv[0]);
    return 2;
  }
  std::ifstream f(argv[1]);
  std::stringstream ss;
  ss << f.rdbuf();
  std::string ptx = ss.str();
  unsigned seed = argc > 2 ? std::atoi(argv[2]) : 1;

  std::mt19937 rng(seed);
  std::uniform_int_distribution<int> dist(-128, 127);
  int8_t a[M][K], b[K][N];
  for (int i = 0; i < M; ++i)
    for (int k = 0; k < K; ++k) a[i][k] = static_cast<int8_t>(dist(rng));
  for (int k = 0; k < K; ++k)
    for (int j = 0; j < N; ++j) b[k][j] = static_cast<int8_t>(dist(rng));
  std::vector<int8_t> ga(M * K), gb(K * N);
  for (int i = 0; i < M; ++i)
    for (int k = 0; k < K; ++k) ga[offA(i, k)] = a[i][k];
  for (int k = 0; k < K; ++k)
    for (int j = 0; j < N; ++j) gb[offB(k, j)] = b[k][j];

  CHECK(cuInit(0));
  CUdevice dev;
  CHECK(cuDeviceGet(&dev, 0));
  CUcontext ctx;
  CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod;
  CHECK(cuModuleLoadData(&mod, ptx.c_str()));
  CUfunction fn;
  CHECK(cuModuleGetFunction(&fn, mod, "tc_gemm"));

  CUdeviceptr dA, dB, dD;
  CHECK(cuMemAlloc(&dA, ga.size()));
  CHECK(cuMemAlloc(&dB, gb.size()));
  CHECK(cuMemAlloc(&dD, M * N * 4));
  CHECK(cuMemcpyHtoD(dA, ga.data(), ga.size()));
  CHECK(cuMemcpyHtoD(dB, gb.data(), gb.size()));
  CHECK(cuMemsetD8(dD, 0xAB, M * N * 4));

  void* args[] = {&dA, &dB, &dD};
  CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr));
  CHECK(cuCtxSynchronize());

  std::vector<int32_t> d(M * N);
  CHECK(cuMemcpyDtoH(d.data(), dD, M * N * 4));
  int bad = 0;
  for (int i = 0; i < M; ++i)
    for (int j = 0; j < N; ++j) {
      int32_t ref = 0;
      for (int k = 0; k < K; ++k) ref += int32_t(a[i][k]) * int32_t(b[k][j]);
      if (d[i * N + j] != ref) {
        if (bad < 10) std::printf("D[%d][%d] = %d, expected %d\n", i, j, d[i * N + j], ref);
        ++bad;
      }
    }
  std::printf("%s: %d mismatches of %d (seed %u)\n", bad ? "FAIL" : "PASS", bad, M * N, seed);
  return bad ? 1 : 0;
}
