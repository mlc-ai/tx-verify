// SPDX-License-Identifier: Apache-2.0

extern "C" __global__ void row_sum(const float* A, float* B, unsigned M, unsigned K) {
  unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= M) return;
  float acc = 0.0f;
#pragma unroll 1
  for (unsigned k = 0; k < K; ++k) acc += A[static_cast<unsigned long long>(row) * K + k];
  B[row] = acc;
}
