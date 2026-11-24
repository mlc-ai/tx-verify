// SPDX-License-Identifier: Apache-2.0

extern "C" __global__ void copy_dynamic(const float* A, float* B, unsigned N) {
  unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < N) B[i] = A[i];
}
