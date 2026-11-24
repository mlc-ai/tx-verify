// SPDX-License-Identifier: Apache-2.0

// Runs tcgen05_ws_ts_tf32.ptx (tcgen05.mma.ws with [a-tmem], kind::tf32, F32 D, M = 128, N = 64,
// K = 8) and compares D with three models of the FP32-to-TF32 input conversion: truncation of the
// low 13 mantissa bits, round-to-nearest-even to 10 mantissa bits, and no conversion. Inputs have
// bits below the TF32 mantissa; every product and sum is exact in FP32, so D shows the conversion.
// The operand bytes use the kind::i8 probe's layout (32 bytes per row or column).
// Build: nvcc -o run_tcgen05_ws_ts_tf32 run_tcgen05_ws_ts_tf32.cu -lcuda
// Run:   replace IDESC with 135268624 (M = 128, N = 64, TF32 A/B, F32 D), then
//        ./run_tcgen05_ws_ts_tf32 tf32.ptx seed [lowb]
#include <cuda.h>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
constexpr int M = 128, N = 64, K = 8;
size_t offB(int k, int j) { return 16 * (j % 8) + 512 * (j / 8) + (k % 16) + 128 * (k / 16); }
uint32_t bits(float f) { uint32_t u; std::memcpy(&u, &f, 4); return u; }
float val(uint32_t u) { float f; std::memcpy(&f, &u, 4); return f; }
float trunc19(float f) { return val(bits(f) & 0xFFFFE000u); }
float rne19(float f) {
  uint32_t u = bits(f), low = u & 0x1FFFu, keep = u & 0xFFFFE000u;
  if (low > 0x1000u || (low == 0x1000u && (keep & 0x2000u))) keep += 0x2000u;
  return val(keep);
}
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  unsigned seed = argc > 2 ? std::atoi(argv[2]) : 1;
  std::mt19937 rng(seed);
  // A: sign * (1..3 + 10 random mantissa bits + 3 random bits below TF32); B: small integers.
  static float a[M][K], b[K][N];
  for (int i = 0; i < M; ++i) for (int k = 0; k < K; ++k) {
    float base = float(1 + rng() % 3) + float(rng() % 1024) / 1024.0f;
    float low = float(rng() % 8) / 8192.0f;
    a[i][k] = (rng() % 2 ? -1.0f : 1.0f) * (base + low);
  }
  // B: small integers; with argument `lowb`, plus bits below the TF32 mantissa (2^-12 .. 2^-10 for
  // |b| in [2, 4), 2^-11 .. for [1, 2)), which truncation removes.
  const bool lowB = argc > 3 && std::string(argv[3]) == "lowb";
  for (int k = 0; k < K; ++k) for (int j = 0; j < N; ++j) {
    int v = int(rng() % 9) - 4;
    float lo = (lowB && v != 0) ? float(1 + rng() % 7) / 16384.0f : 0.0f;
    b[k][j] = v < 0 ? float(v) - lo : float(v) + lo;
  }
  std::vector<uint8_t> ga(4096), gb(4096);
  for (int l = 0; l < M; ++l) std::memcpy(&ga[32 * l], a[l], 32);
  for (int k = 0; k < K; ++k) for (int j = 0; j < N; ++j) {
    uint32_t u = bits(b[k][j]);
    for (int t = 0; t < 4; ++t) gb[offB(4 * k + t, j)] = uint8_t(u >> (8 * t));
  }
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str())); CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, "wsts"));
  CUdeviceptr dA, dB, dD;
  CHECK(cuMemAlloc(&dA, 4096)); CHECK(cuMemAlloc(&dB, 4096)); CHECK(cuMemAlloc(&dD, 128 * 64 * 4));
  CHECK(cuMemcpyHtoD(dA, ga.data(), 4096)); CHECK(cuMemcpyHtoD(dB, gb.data(), 4096));
  CHECK(cuMemsetD8(dD, 0xAB, 128 * 64 * 4));
  void* args[] = {&dA, &dB, &dD};
  CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
  std::vector<float> d(128 * 64); CHECK(cuMemcpyDtoH(d.data(), dD, 128 * 64 * 4));
  const char* names[3] = {"truncate", "round-nearest-even", "no conversion"};
  for (int h = 0; h < 3; ++h) {
    int bad = 0;
    for (int i = 0; i < M; ++i) for (int j = 0; j < N; ++j) {
      double ref = 0;
      for (int k = 0; k < K; ++k) {
        float x = h == 0 ? trunc19(a[i][k]) : h == 1 ? rne19(a[i][k]) : a[i][k];
        float y = h == 0 ? trunc19(b[k][j]) : h == 1 ? rne19(b[k][j]) : b[k][j];
        ref += double(x) * double(y);
      }
      if (double(d[i * 64 + j]) != ref) ++bad;
    }
    std::printf("%s: %d mismatches of %d (seed %u)\n", names[h], bad, M * N, seed);
  }
  return 0;
}
