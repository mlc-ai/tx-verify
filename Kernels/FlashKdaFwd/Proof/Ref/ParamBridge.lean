-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.ParamNames

@[expose] public section

/-! # The literal names of the parameter objects 1 to 9 are the specification's names

The thread machine names a parameter by the literal the decoded code carries (`paramName i`,
`Proof/Thread/ParamNames.lean`); the specification's precondition names it `param "i"`, the
kernel's name followed by `_param_i`. `Proof/Thread/ParamBridge.lean` has the equations the
machine itself needs (the objects 0 and 10 and the scalars). The reference layer needs the
remaining by-value objects to read a tensor map off `Pre`: the objects 1 to 7 hold the maps of
the tile loads (`beta` and the six workspace arrays), 8 the map of the initial state and 9 the
map of the final state.

Each equation is one kernel evaluation of a 1,425-character string (about a minute and several
gigabytes; the elaborator cannot do it). Import this file only where a tensor-map descriptor is
derived: the generic lemmas (`Ref/TensorLoad.lean`) take the name equation as a hypothesis. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

theorem paramName_1 : paramName 1 = param "1" := by kernel_rfl
theorem paramName_2 : paramName 2 = param "2" := by kernel_rfl
theorem paramName_3 : paramName 3 = param "3" := by kernel_rfl
theorem paramName_4 : paramName 4 = param "4" := by kernel_rfl
theorem paramName_5 : paramName 5 = param "5" := by kernel_rfl
theorem paramName_6 : paramName 6 = param "6" := by kernel_rfl
theorem paramName_7 : paramName 7 = param "7" := by kernel_rfl
theorem paramName_8 : paramName 8 = param "8" := by kernel_rfl
theorem paramName_9 : paramName 9 = param "9" := by kernel_rfl

end PTX.Kernels.FlashKdaFwd.Proof.Ref
