// SPDX-License-Identifier: Apache-2.0
// Runs tma_gather4.ptx and compares the whole shared buffer with the TxVerify model of a
// .tile::gather4 load (EXT-TMA-GATHER4): the tile copy of the map's box with box dimension 1
// replaced by 4, whose row j reads tensor row y_j from column x (TensorTile.sharedByte: row pitch
// max(inner box bytes, swizzle width), swizzle phase from the destination's 128-byte row; out-of-
// bounds elements are zero, padding keeps the sentinel 0xEE). The mbarrier expects 4 * bw bytes.
// Build: nvcc -o run_tma_gather4 run_tma_gather4.cu -lcuda
// Run:   ./run_tma_gather4 tma_gather4.ptx  (all cases),
//        ./run_tma_gather4 tma_gather4.ptx bw bh swizzle offset x y0 y1 y2 y3
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
int swz(int mode, int base, int byte) {
  int row = byte / 128, chunk = (byte / 16) % 8, mask = (base / 128 + row) % sectors(mode);
  return 128 * row + 16 * ((chunk ^ mask) & 7) + byte % 16;
}
struct Case { int bw, bh, mode, off, x, y[4]; };
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str()));
  CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, "tmag4"));
  std::vector<uint8_t> g(W * H);
  for (int y = 0; y < H; ++y) for (int x = 0; x < W; ++x) g[y * W + x] = gval(x, y);
  CUdeviceptr dG, dO; CHECK(cuMemAlloc(&dG, W * H)); CHECK(cuMemAlloc(&dO, 8192));
  CHECK(cuMemcpyHtoD(dG, g.data(), W * H));
  const CUtensorMapSwizzle sw[4] = {CU_TENSOR_MAP_SWIZZLE_NONE, CU_TENSOR_MAP_SWIZZLE_32B,
                                    CU_TENSOR_MAP_SWIZZLE_64B, CU_TENSOR_MAP_SWIZZLE_128B};
  std::vector<Case> cases = {
    {64, 1, 0, 0, 0, {0, 1, 2, 3}}, {64, 1, 0, 256, 16, {9, 2, 40, 2}},   // no swizzle, repeated row
    {128, 1, 3, 0, 0, {5, 0, 63, 17}}, {128, 1, 3, 384, 32, {1, 30, 7, 7}},  // 128B swizzle and phase
    {64, 1, 2, 0, 48, {3, 2, 1, 0}}, {64, 1, 2, 640, 0, {11, 12, 50, 4}},    // 64B swizzle: 2 rows per 128 B
    {32, 1, 1, 128, 16, {8, 6, 4, 2}}, {32, 1, 3, 0, 0, {1, 2, 3, 4}},       // 32B; narrower than swizzle
    {64, 1, 3, 0, -16, {-3, 5, 64, 70}}, {128, 1, 3, 1024, 192, {60, -1, 63, 0}},  // out of bounds per row
  };
  if (argc > 10) { Case c{std::atoi(argv[2]), std::atoi(argv[3]), std::atoi(argv[4]), std::atoi(argv[5]),
                          std::atoi(argv[6]), {std::atoi(argv[7]), std::atoi(argv[8]), std::atoi(argv[9]), std::atoi(argv[10])}};
                   cases = {c}; }
  int total = 0;
  for (const Case& c : cases) {
    CUtensorMap map;
    cuuint64_t dims[2] = {W, H}; cuuint64_t strides[1] = {W};
    cuuint32_t box[2] = {cuuint32_t(c.bw), cuuint32_t(c.bh)}; cuuint32_t es[2] = {1, 1};
    CHECK(cuTensorMapEncodeTiled(&map, CU_TENSOR_MAP_DATA_TYPE_UINT8, 2, (void*)dG, dims, strides, box, es,
      CU_TENSOR_MAP_INTERLEAVE_NONE, sw[c.mode], CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE));
    unsigned bytes = 4 * c.bw; uint64_t out = dO; int x = c.x, y0 = c.y[0], y1 = c.y[1], y2 = c.y[2], y3 = c.y[3], off = c.off;
    void* args[] = {&map, &x, &y0, &y1, &y2, &y3, &off, &bytes, &out};
    CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
    std::vector<uint8_t> o(8192); CHECK(cuMemcpyDtoH(o.data(), dO, 8192));
    std::vector<int> model(8192, 0xEE);
    int pitch = c.bw > width(c.mode) ? c.bw : width(c.mode);
    for (int j = 0; j < 4; ++j) for (int i = 0; i < c.bw; ++i) {
      int gx = c.x + i, gy = c.y[j];
      int v = (gx >= 0 && gx < W && gy >= 0 && gy < H) ? gval(gx, gy) : 0;
      model[c.off + swz(c.mode, c.off, j * pitch + i)] = v;
    }
    int bad = 0;
    for (int b = 0; b < 8192; ++b) if (o[b] != model[b]) ++bad;
    std::printf("box %3dx%d swizzle %3d off %4d x %4d rows (%3d,%3d,%3d,%3d): %d mismatched bytes\n",
      c.bw, c.bh, width(c.mode), c.off, c.x, c.y[0], c.y[1], c.y[2], c.y[3], bad);
    total += bad;
  }
  std::printf("total mismatched bytes: %d\n", total);
  return 0;
}
