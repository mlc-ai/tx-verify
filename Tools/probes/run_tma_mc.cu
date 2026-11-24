// SPDX-License-Identifier: Apache-2.0

// Runs tma_mc.ptx on one 4-CTA cluster and compares every CTA's shared buffer with the TxVerify
// model of a .multicast::cluster tensor load (tensorMulticast): one copy per ctaMask rank, with
// the 2D tiled layout (TensorTile.sharedByte) at the same CTA-relative offset; CTAs outside the
// mask keep the 0xEE sentinel.
// Build: nvcc -o run_tma_mc run_tma_mc.cu -lcuda
// Run:   ./run_tma_mc tma_mc.ptx
#include <cuda.h>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
constexpr int W = 256, H = 64;
uint8_t gval(int x, int y) { return uint8_t((x * 7 + y * 13) % 251 + 1); }
int sectors(int m) { return m == 0 ? 1 : m == 1 ? 2 : m == 2 ? 4 : 8; }
int width(int m) { return m == 0 ? 0 : 16 << m; }
int swz(int mode, int base, int byte) {
  int row = byte / 128, chunk = (byte / 16) % 8, mask = (base / 128 + row) % sectors(mode);
  return 128 * row + 16 * ((chunk ^ mask) & 7) + byte % 16;
}
struct Case { int bw, bh, mode, off, x, y, mask; };
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str())); CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, "tmamc"));
  std::vector<uint8_t> g(W * H);
  for (int y = 0; y < H; ++y) for (int x = 0; x < W; ++x) g[y * W + x] = gval(x, y);
  CUdeviceptr dG, dO; CHECK(cuMemAlloc(&dG, W * H)); CHECK(cuMemAlloc(&dO, 4 * 8192));
  CHECK(cuMemcpyHtoD(dG, g.data(), W * H));
  const CUtensorMapSwizzle sw[4] = {CU_TENSOR_MAP_SWIZZLE_NONE, CU_TENSOR_MAP_SWIZZLE_32B,
                                    CU_TENSOR_MAP_SWIZZLE_64B, CU_TENSOR_MAP_SWIZZLE_128B};
  const Case cases[] = {
    {64, 8, 0, 0, 0, 0, 0xF}, {128, 16, 3, 384, 32, 5, 0x5}, {64, 16, 2, 640, 48, 7, 0xA},
    {32, 8, 3, 0, -16, 60, 0xE}, {64, 8, 0, 256, 16, 3, 0x1},
  };
  int all = 0;
  for (const Case& c : cases) {
    CUtensorMap map;
    cuuint64_t dims[2] = {W, H}; cuuint64_t strides[1] = {W};
    cuuint32_t box[2] = {cuuint32_t(c.bw), cuuint32_t(c.bh)}; cuuint32_t es[2] = {1, 1};
    CHECK(cuTensorMapEncodeTiled(&map, CU_TENSOR_MAP_DATA_TYPE_UINT8, 2, (void*)dG, dims, strides, box, es,
      CU_TENSOR_MAP_INTERLEAVE_NONE, sw[c.mode], CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE));
    CHECK(cuMemsetD8(dO, 0, 4 * 8192));
    unsigned bytes = c.bw * c.bh, mask = c.mask; uint64_t out = dO; int x = c.x, y = c.y, off = c.off;
    void* args[] = {&map, &x, &y, &off, &bytes, &mask, &out};
    CHECK(cuLaunchKernel(fn, 4, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
    std::vector<uint8_t> o(4 * 8192); CHECK(cuMemcpyDtoH(o.data(), dO, 4 * 8192));
    std::vector<int> tile(8192, 0xEE);
    int pitch = c.bw > width(c.mode) ? c.bw : width(c.mode);
    for (int j = 0; j < c.bh; ++j) for (int i = 0; i < c.bw; ++i) {
      int gx = c.x + i, gy = c.y + j;
      tile[c.off + swz(c.mode, c.off, j * pitch + i)] = (gx >= 0 && gx < W && gy >= 0 && gy < H) ? gval(gx, gy) : 0;
    }
    int bad = 0;
    for (int r = 0; r < 4; ++r) for (int b = 0; b < 8192; ++b) {
      int expect = (c.mask >> r & 1) ? tile[b] : 0xEE;
      if (o[r * 8192 + b] != expect) ++bad;
    }
    std::printf("mask 0x%X box %3dx%-2d swizzle %3d off %4d origin (%4d,%3d): %d mismatched bytes over 4 CTAs\n",
      c.mask, c.bw, c.bh, width(c.mode), c.off, c.x, c.y, bad);
    all += bad;
  }
  std::printf("total mismatched bytes: %d\n", all);
  return 0;
}
