// SPDX-License-Identifier: Apache-2.0

// Runs tcgen05_ws_ts_i8.ptx (tcgen05.mma.ws with [a-tmem], kind::i8, N = 64) against the CPU
// model. Lane l holds A row l for l < M and decoys otherwise; D uses Layouts D (M = 128),
// E (M = 64: lane i + 64 (j / 32)) and G (M = 32: lane i + 32 (j / 16)).
// Build: nvcc -o run_tcgen05_ws_ts_i8 run_tcgen05_ws_ts_i8.cu -lcuda
// Run:   replace IDESC with the instruction descriptor (M = 128: 135267488, M = 64: 68158624,
//        M = 32: 34604192), then ./run_tcgen05_ws_ts_i8 ws.ptx M seed
#include <cuda.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
constexpr int N = 64, K = 32;
size_t offB(int k, int j) { return 16 * (j % 8) + 512 * (j / 8) + (k % 16) + 128 * (k / 16); }
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  const int M = std::atoi(argv[2]);
  unsigned seed = argc > 3 ? std::atoi(argv[3]) : 1;
  std::mt19937 rng(seed); std::uniform_int_distribution<int> dist(-128, 127);
  static int8_t a[128][K], b[K][N];
  for (int i = 0; i < 128; ++i) for (int k = 0; k < K; ++k) a[i][k] = dist(rng);
  for (int k = 0; k < K; ++k) for (int j = 0; j < N; ++j) b[k][j] = dist(rng);
  std::vector<int8_t> ga(4096), gb(4096);
  // A by lane, row-major: lane l holds row l for l < M, a decoy row otherwise.
  for (int l = 0; l < 128; ++l) for (int k = 0; k < K; ++k) ga[32 * l + k] = a[l < M ? l : 127 - l][k];
  for (int k = 0; k < K; ++k) for (int j = 0; j < N; ++j) gb[offB(k, j)] = b[k][j];
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str())); CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, "wsts"));
  CUdeviceptr dA, dB, dD;
  CHECK(cuMemAlloc(&dA, 4096)); CHECK(cuMemAlloc(&dB, 4096)); CHECK(cuMemAlloc(&dD, 128 * 64 * 4));
  CHECK(cuMemcpyHtoD(dA, ga.data(), 4096)); CHECK(cuMemcpyHtoD(dB, gb.data(), 4096));
  CHECK(cuMemsetD8(dD, 0xAB, 128 * 64 * 4));
  void* args[] = {&dA, &dB, &dD};
  CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
  std::vector<int32_t> d(128 * 64); CHECK(cuMemcpyDtoH(d.data(), dD, 128 * 64 * 4));
  const int blocks = 128 / M, cols = N / blocks;
  // h0: A row i from lane i; h1: from the D lane i + M b of its column block b (decoys above M - 1).
  for (int h = 0; h < 2; ++h) {
    int bad = 0;
    for (int i = 0; i < M; ++i) for (int j = 0; j < N; ++j) {
      int blk = j / cols, lane = i + M * blk;
      const int8_t* ar = a[h ? (lane < M ? lane : 127 - lane) : i];
      int32_t ref = 0;
      for (int k = 0; k < K; ++k) ref += int32_t(ar[k]) * b[k][j];
      if (d[lane * 64 + j % cols] != ref) ++bad;
    }
    std::printf("hypothesis %d: %d mismatches of %d (seed %u, M = %d)\n", h, bad, M * N, seed, M);
  }
  return 0;
}
