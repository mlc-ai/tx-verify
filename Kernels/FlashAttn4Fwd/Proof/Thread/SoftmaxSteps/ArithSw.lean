-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The software `exp2` instances

The 24 instances of the software `exp2` template (`Assumptions.swExp2`) in the softmax
segments (`SoftmaxRuns`) match the code with the registers of their slots (`matchAt`, by
evaluation). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem swMatch_2121 : Assumption.cuteExp2.matchAt kernel 2121 = some m2121 := by
  rfl

theorem swMatch_2152 : Assumption.cuteExp2.matchAt kernel 2152 = some m2152 := by
  rfl

theorem swMatch_2179 : Assumption.cuteExp2.matchAt kernel 2179 = some m2179 := by
  rfl

theorem swMatch_2200 : Assumption.cuteExp2.matchAt kernel 2200 = some m2200 := by
  rfl

theorem swMatch_2227 : Assumption.cuteExp2.matchAt kernel 2227 = some m2227 := by
  rfl

theorem swMatch_2248 : Assumption.cuteExp2.matchAt kernel 2248 = some m2248 := by
  rfl

theorem swMatch_2301 : Assumption.cuteExp2.matchAt kernel 2301 = some m2301 := by
  rfl

theorem swMatch_2322 : Assumption.cuteExp2.matchAt kernel 2322 = some m2322 := by
  rfl

theorem swMatch_2349 : Assumption.cuteExp2.matchAt kernel 2349 = some m2349 := by
  rfl

theorem swMatch_2370 : Assumption.cuteExp2.matchAt kernel 2370 = some m2370 := by
  rfl

theorem swMatch_2397 : Assumption.cuteExp2.matchAt kernel 2397 = some m2397 := by
  rfl

theorem swMatch_2418 : Assumption.cuteExp2.matchAt kernel 2418 = some m2418 := by
  rfl

theorem swMatch_3136 : Assumption.cuteExp2.matchAt kernel 3136 = some m3136 := by
  rfl

theorem swMatch_3167 : Assumption.cuteExp2.matchAt kernel 3167 = some m3167 := by
  rfl

theorem swMatch_3194 : Assumption.cuteExp2.matchAt kernel 3194 = some m3194 := by
  rfl

theorem swMatch_3215 : Assumption.cuteExp2.matchAt kernel 3215 = some m3215 := by
  rfl

theorem swMatch_3242 : Assumption.cuteExp2.matchAt kernel 3242 = some m3242 := by
  rfl

theorem swMatch_3263 : Assumption.cuteExp2.matchAt kernel 3263 = some m3263 := by
  rfl

theorem swMatch_3316 : Assumption.cuteExp2.matchAt kernel 3316 = some m3316 := by
  rfl

theorem swMatch_3337 : Assumption.cuteExp2.matchAt kernel 3337 = some m3337 := by
  rfl

theorem swMatch_3364 : Assumption.cuteExp2.matchAt kernel 3364 = some m3364 := by
  rfl

theorem swMatch_3385 : Assumption.cuteExp2.matchAt kernel 3385 = some m3385 := by
  rfl

theorem swMatch_3412 : Assumption.cuteExp2.matchAt kernel 3412 = some m3412 := by
  rfl

theorem swMatch_3433 : Assumption.cuteExp2.matchAt kernel 3433 = some m3433 := by
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
