// SPDX-License-Identifier: Apache-2.0
// Runs tma2d.ptx and compares the whole shared buffer with the TxVerify model of a 2D tiled
// TMA load: TensorTile.sharedByte2D (row pitch max(inner box bytes, swizzle width), swizzle
// phase from the destination's 128-byte row), TensorAddress.lookup (out-of-bounds elements are
// zero) and untouched padding (sentinel 0xEE).
// Build: nvcc -o run_tma2d run_tma2d.cu -lcuda
// Run:   ./run_tma2d tma2d.ptx  (all cases), ./run_tma2d tma2d.ptx bw bh swizzle offset x y
//        ./run_tma2d tma2d_store.ptx bw bh swizzle offset x y store  (store: trap or completion only)
#include <cuda.h>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <cstdlib>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
constexpr int W = 256, H = 64;
uint8_t gval(int x, int y) { return uint8_t((x * 7 + y * 13) % 251 + 1); }
int sectors(int m) { return m == 0 ? 1 : m == 1 ? 2 : m == 2 ? 4 : 8; }
int width(int m) { return m == 0 ? 0 : 16 << m; }
// TensorSwizzle.offset with the shared base phase.
int swz(int mode, int base, int byte) {
  int row = byte / 128, chunk = (byte / 16) % 8, mask = (base / 128 + row) % sectors(mode);
  return 128 * row + 16 * ((chunk ^ mask) & 7) + byte % 16;
}
struct Case { int bw, bh, mode, off, x, y; };
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str())); const bool storeMode = std::string(argv[argc - 1]) == "store";
  CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, storeMode ? "tmast" : "tma2d"));
  std::vector<uint8_t> g(W * H);
  for (int y = 0; y < H; ++y) for (int x = 0; x < W; ++x) g[y * W + x] = gval(x, y);
  CUdeviceptr dG, dO; CHECK(cuMemAlloc(&dG, W * H)); CHECK(cuMemAlloc(&dO, 8192));
  CHECK(cuMemcpyHtoD(dG, g.data(), W * H));
  const CUtensorMapSwizzle sw[4] = {CU_TENSOR_MAP_SWIZZLE_NONE, CU_TENSOR_MAP_SWIZZLE_32B,
                                    CU_TENSOR_MAP_SWIZZLE_64B, CU_TENSOR_MAP_SWIZZLE_128B};
  std::vector<Case> cases = {
    {64, 8, 0, 0, 0, 0}, {64, 8, 0, 256, 16, 3},          // no swizzle, plain and offset
    {128, 16, 3, 0, 0, 0}, {128, 16, 3, 384, 32, 5},      // 128B swizzle, phase from base / 128
    {64, 16, 2, 0, 0, 0}, {64, 16, 2, 640, 48, 7},        // 64B swizzle
    {32, 16, 1, 128, 16, 2},                              // 32B swizzle, odd phase
    {32, 8, 3, 0, 0, 0}, {16, 8, 2, 512, 16, 1},          // inner box narrower than swizzle: padded rows
    {64, 8, 3, 0, -16, -3}, {128, 8, 3, 1024, 192, 60},   // out-of-bounds: zero fill
  };
  // One case: bw bh swizzle(0..3) offset x y [store]. Inner coordinates that are not 16-byte
  // aligned (e.g. x = 8) trap with an illegal instruction (EXT-TMA-BOX-ALIGN).
  if (argc > 7) cases = {{std::atoi(argv[2]), std::atoi(argv[3]), std::atoi(argv[4]), std::atoi(argv[5]),
                          std::atoi(argv[6]), std::atoi(argv[7])}};
  int total = 0;
  for (const Case& c : cases) {
    CUtensorMap map;
    cuuint64_t dims[2] = {W, H}; cuuint64_t strides[1] = {W};
    cuuint32_t box[2] = {cuuint32_t(c.bw), cuuint32_t(c.bh)}; cuuint32_t es[2] = {1, 1};
    CHECK(cuTensorMapEncodeTiled(&map, CU_TENSOR_MAP_DATA_TYPE_UINT8, 2, (void*)dG, dims, strides, box, es,
      CU_TENSOR_MAP_INTERLEAVE_NONE, sw[c.mode], CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE));
    unsigned bytes = c.bw * c.bh; uint64_t out = dO; int x = c.x, y = c.y, off = c.off;
    void* args[] = {&map, &x, &y, &off, &bytes, &out};
    CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
    std::vector<uint8_t> o(8192); CHECK(cuMemcpyDtoH(o.data(), dO, 8192));
    std::vector<int> model(8192, 0xEE);
    int pitch = c.bw > width(c.mode) ? c.bw : width(c.mode);
    for (int j = 0; j < c.bh; ++j) for (int i = 0; i < c.bw; ++i) {
      int gx = c.x + i, gy = c.y + j;
      int v = (gx >= 0 && gx < W && gy >= 0 && gy < H) ? gval(gx, gy) : 0;
      model[c.off + swz(c.mode, c.off, j * pitch + i)] = v;
    }
    int bad = 0;
    for (int b = 0; b < 8192; ++b) if (o[b] != model[b]) ++bad;
    std::printf("box %3dx%-2d swizzle %3d off %4d origin (%4d,%3d): %d mismatched bytes\n",
      c.bw, c.bh, width(c.mode), c.off, c.x, c.y, bad);
    total += bad;
  }
  std::printf("total mismatched bytes: %d\n", total);
  return 0;
}
