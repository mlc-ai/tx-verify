// SPDX-License-Identifier: Apache-2.0

// Read-only input through the non-coherent cache (ld.global.nc).
extern "C" __global__ void copy_ldg(const float* __restrict__ A, float* __restrict__ B, unsigned N) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < N) B[i] = __ldg(&A[i]);
}
