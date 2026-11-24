// SPDX-License-Identifier: Apache-2.0

// Runs tma<r>d.ptx (r = 1, 3, 4, 5) and compares the whole shared buffer with the TxVerify model
// of an r-dimensional tiled TMA load (THREAD-TENSOR-TILE-SHARED): selected rows are the outer
// axes' index combinations, axis 1 varying fastest (TensorTile.rows / indexOf); the row pitch
// is the inner box bytes padded to the swizzle width; out-of-bounds elements on any axis are zero;
// padding keeps the 0xEE sentinel.
// Build: nvcc -o run_tmand run_tmand.cu -lcuda
// Run:   ./run_tmand <dir with tma1d.ptx, tma3d.ptx, tma4d.ptx, tma5d.ptx>
#include <cuda.h>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
const int DIM[5] = {64, 6, 5, 4, 3};
int total(int r) { int n = 1; for (int a = 0; a < r; ++a) n *= DIM[a]; return n; }
uint8_t gval(const int* c) { return uint8_t((c[0] * 7 + c[1] * 13 + c[2] * 29 + c[3] * 31 + c[4] * 37) % 251 + 1); }
int sectors(int m) { return m == 0 ? 1 : m == 1 ? 2 : m == 2 ? 4 : 8; }
int width(int m) { return m == 0 ? 0 : 16 << m; }
int swz(int mode, int base, int byte) {
  int row = byte / 128, chunk = (byte / 16) % 8, mask = (base / 128 + row) % sectors(mode);
  return 128 * row + 16 * ((chunk ^ mask) & 7) + byte % 16;
}
struct Case { int rank, mode, off; int box[5]; int origin[5]; };
int main(int argc, char** argv) {
  std::string dir = argc > 1 ? argv[1] : ".";
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  std::vector<uint8_t> g(total(5));
  for (int i = 0; i < total(5); ++i) {
    int c[5], r = i; for (int a = 0; a < 5; ++a) { c[a] = r % DIM[a]; r /= DIM[a]; }
    g[i] = gval(c);
  }
  CUdeviceptr dG, dO; CHECK(cuMemAlloc(&dG, g.size())); CHECK(cuMemAlloc(&dO, 8192));
  CHECK(cuMemcpyHtoD(dG, g.data(), g.size()));
  const CUtensorMapSwizzle sw[4] = {CU_TENSOR_MAP_SWIZZLE_NONE, CU_TENSOR_MAP_SWIZZLE_32B,
                                    CU_TENSOR_MAP_SWIZZLE_64B, CU_TENSOR_MAP_SWIZZLE_128B};
  const Case cases[] = {
    {1, 0, 0, {48, 1, 1, 1, 1}, {16, 0, 0, 0, 0}}, {1, 0, 128, {32, 1, 1, 1, 1}, {48, 0, 0, 0, 0}},
    {3, 0, 0, {16, 3, 2, 1, 1}, {16, 1, 1, 0, 0}}, {3, 1, 256, {16, 3, 2, 1, 1}, {32, 4, 3, 0, 0}},
    {3, 3, 384, {32, 2, 3, 1, 1}, {0, -1, 3, 0, 0}},
    {4, 0, 0, {16, 2, 2, 2, 1}, {16, 2, 1, 1, 0}}, {4, 2, 512, {16, 3, 2, 3, 1}, {48, 5, -1, 2, 0}},
    {5, 0, 0, {16, 2, 2, 2, 2}, {0, 1, 2, 1, 1}}, {5, 3, 1024, {16, 2, 3, 2, 2}, {32, 0, 3, 3, 2}},
  };
  int all = 0;
  for (const Case& c : cases) {
    std::ifstream f(dir + "/tma" + std::to_string(c.rank) + "d.ptx"); std::stringstream ss; ss << f.rdbuf();
    std::string ptx = ss.str();
    CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str()));
    CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, ("tma" + std::to_string(c.rank) + "d").c_str()));
    CUtensorMap map; cuuint64_t dims[5], strides[4]; cuuint32_t box[5], es[5];
    cuuint64_t st = 1;
    for (int a = 0; a < c.rank; ++a) { dims[a] = DIM[a]; box[a] = c.box[a]; es[a] = 1; if (a > 0) strides[a - 1] = st; st *= DIM[a]; }
    CHECK(cuTensorMapEncodeTiled(&map, CU_TENSOR_MAP_DATA_TYPE_UINT8, c.rank, (void*)dG, dims, strides, box, es,
      CU_TENSOR_MAP_INTERLEAVE_NONE, sw[c.mode], CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE));
    unsigned bytes = 1; for (int a = 0; a < c.rank; ++a) bytes *= c.box[a];
    int co[5]; for (int a = 0; a < 5; ++a) co[a] = c.origin[a];
    int off = c.off; uint64_t out = dO;
    std::vector<void*> args = {&map};
    for (int a = 0; a < c.rank; ++a) args.push_back(&co[a]);
    args.push_back(&off); args.push_back(&bytes); args.push_back(&out);
    CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args.data(), nullptr)); CHECK(cuCtxSynchronize());
    std::vector<uint8_t> o(8192); CHECK(cuMemcpyDtoH(o.data(), dO, 8192));
    std::vector<int> model(8192, 0xEE);
    int pitch = c.box[0] > width(c.mode) ? c.box[0] : width(c.mode);
    int rows = 1; for (int a = 1; a < c.rank; ++a) rows *= c.box[a];
    for (int row = 0; row < rows; ++row) for (int i0 = 0; i0 < c.box[0]; ++i0) {
      int idx[5] = {i0, 0, 0, 0, 0}, r = row;
      for (int a = 1; a < c.rank; ++a) { idx[a] = r % c.box[a]; r /= c.box[a]; }
      int gc[5] = {0, 0, 0, 0, 0}; bool in = true;
      for (int a = 0; a < c.rank; ++a) { gc[a] = c.origin[a] + idx[a]; if (gc[a] < 0 || gc[a] >= DIM[a]) in = false; }
      model[c.off + swz(c.mode, c.off, row * pitch + i0)] = in ? gval(gc) : 0;
    }
    int bad = 0; for (int b = 0; b < 8192; ++b) if (o[b] != model[b]) ++bad;
    std::printf("rank %d box", c.rank);
    for (int a = 0; a < c.rank; ++a) std::printf(" %d", c.box[a]);
    std::printf(" swizzle %3d off %4d origin", width(c.mode), c.off);
    for (int a = 0; a < c.rank; ++a) std::printf(" %d", c.origin[a]);
    std::printf(": %d mismatched bytes\n", bad);
    all += bad;
    CHECK(cuModuleUnload(mod));
  }
  std::printf("total mismatched bytes: %d\n", all);
  return 0;
}
