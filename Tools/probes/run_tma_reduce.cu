// SPDX-License-Identifier: Apache-2.0
// Runs tma_reduce.ptx and compares the whole global tensor with the TxVerify layout of a 2D
// tiled tensor store (TensorStore.destination / TensorTile.sharedByte) and the reduction of each
// in-bounds element with its shared element; out-of-bounds elements and the rest of the tensor
// keep their initial values. 32-bit elements (u32 or s32 map).
// Build: nvcc -o run_tma_reduce run_tma_reduce.cu -lcuda
// Run:   ./run_tma_reduce tma_reduce.ptx REDOP type(u32|s32) bw bh swizzle offset x y
//        (the PTX's REDOP is replaced with the given reduction)
#include <cuda.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#define CHECK(x) do { CUresult r = (x); if (r != CUDA_SUCCESS) { const char* s = nullptr; cuGetErrorString(r, &s); std::fprintf(stderr, "%s failed: %s\n", #x, s ? s : "?"); return 1; } } while (0)
constexpr int W = 64, H = 32;
int sectors(int m) { return m == 0 ? 1 : m == 1 ? 2 : m == 2 ? 4 : 8; }
int width(int m) { return m == 0 ? 0 : 16 << m; }
int swz(int mode, int base, int byte) {
  int row = byte / 128, chunk = (byte / 16) % 8, mask = (base / 128 + row) % sectors(mode);
  return 128 * row + 16 * ((chunk ^ mask) & 7) + byte % 16;
}
uint32_t red(const std::string& op, bool sgn, uint32_t a, uint32_t b) {
  int32_t sa = int32_t(a), sb = int32_t(b);
  if (op == "add") return a + b;
  if (op == "min") return sgn ? uint32_t(sa < sb ? sa : sb) : (a < b ? a : b);
  if (op == "max") return sgn ? uint32_t(sa > sb ? sa : sb) : (a > b ? a : b);
  if (op == "inc") return a >= b ? 0 : a + 1;
  if (op == "dec") return (a == 0 || a > b) ? b : a - 1;
  if (op == "and") return a & b;
  if (op == "or") return a | b;
  return a ^ b;
}
int main(int argc, char** argv) {
  std::ifstream f(argv[1]); std::stringstream ss; ss << f.rdbuf(); std::string ptx = ss.str();
  const std::string op = argv[2]; const bool sgn = std::string(argv[3]) == "s32";
  const int bw = std::atoi(argv[4]), bh = std::atoi(argv[5]), mode = std::atoi(argv[6]);
  const int off = std::atoi(argv[7]), x0 = std::atoi(argv[8]), y0 = std::atoi(argv[9]);
  for (size_t k; (k = ptx.find("REDOP")) != std::string::npos;) ptx.replace(k, 5, op);
  CHECK(cuInit(0)); CUdevice dev; CHECK(cuDeviceGet(&dev, 0)); CUcontext ctx; CHECK(cuCtxCreate(&ctx, nullptr, 0, dev));
  CUmodule mod; CHECK(cuModuleLoadData(&mod, ptx.c_str())); CUfunction fn; CHECK(cuModuleGetFunction(&fn, mod, "tmared"));
  std::vector<uint32_t> g(W * H);
  for (int i = 0; i < W * H; ++i) g[i] = uint32_t(i * 40503u + 7u) ^ (i % 3 ? 0x80000000u : 0u);
  CUdeviceptr dG; CHECK(cuMemAlloc(&dG, W * H * 4)); CHECK(cuMemcpyHtoD(dG, g.data(), W * H * 4));
  const CUtensorMapSwizzle sw[4] = {CU_TENSOR_MAP_SWIZZLE_NONE, CU_TENSOR_MAP_SWIZZLE_32B,
                                    CU_TENSOR_MAP_SWIZZLE_64B, CU_TENSOR_MAP_SWIZZLE_128B};
  CUtensorMap map;
  cuuint64_t dims[2] = {W, H}; cuuint64_t strides[1] = {W * 4};
  cuuint32_t box[2] = {cuuint32_t(bw), cuuint32_t(bh)}; cuuint32_t es[2] = {1, 1};
  CHECK(cuTensorMapEncodeTiled(&map, sgn ? CU_TENSOR_MAP_DATA_TYPE_INT32 : CU_TENSOR_MAP_DATA_TYPE_UINT32, 2,
    (void*)dG, dims, strides, box, es, CU_TENSOR_MAP_INTERLEAVE_NONE, sw[mode],
    CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE));
  int x = x0, y = y0, o = off;
  void* args[] = {&map, &x, &y, &o};
  CHECK(cuLaunchKernel(fn, 1, 1, 1, 128, 1, 1, 0, nullptr, args, nullptr)); CHECK(cuCtxSynchronize());
  std::vector<uint32_t> out(W * H); CHECK(cuMemcpyDtoH(out.data(), dG, W * H * 4));
  std::vector<uint32_t> model = g;
  const int pitch = bw * 4 > width(mode) ? bw * 4 : width(mode);
  for (int j = 0; j < bh; ++j) for (int i = 0; i < bw; ++i) {
    int gx = x0 + i, gy = y0 + j;
    if (gx < 0 || gx >= W || gy < 0 || gy >= H) continue;
    int byte = off + swz(mode, off, j * pitch + 4 * i);
    uint32_t s = uint32_t(byte / 4) * 2654435761u + 12345u;
    model[gy * W + gx] = red(op, sgn, g[gy * W + gx], s);
  }
  int bad = 0;
  for (int k = 0; k < W * H; ++k) if (out[k] != model[k]) ++bad;
  std::printf("%s.%s box %dx%d swizzle %d off %d origin (%d,%d): %d mismatched elements of %d\n",
    op.c_str(), sgn ? "s32" : "u32", bw, bh, width(mode), off, x0, y0, bad, W * H);
  return 0;
}
