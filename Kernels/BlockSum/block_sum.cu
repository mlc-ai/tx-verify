// SPDX-License-Identifier: Apache-2.0

// Shared memory plus a CTA barrier: thread 0 sums its CTA's 256 inputs.
extern "C" __global__ void block_sum(const float* A, float* B) {
  __shared__ float s[256];
  unsigned t = threadIdx.x;
  s[t] = A[blockIdx.x * 256 + t];
  __syncthreads();
  if (t == 0) {
    float acc = 0.0f;
#pragma unroll 1
    for (unsigned k = 0; k < 256; ++k) acc += s[k];
    B[blockIdx.x] = acc;
  }
}
