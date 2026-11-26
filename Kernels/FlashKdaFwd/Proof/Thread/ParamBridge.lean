-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.ParamNames

@[expose] public section

/-! # The literal parameter names are the specification's names

The thread machine names a parameter by the literal the decoded code carries (`paramName i`);
the specification's precondition names it `param "i"`, the kernel's name followed by
`_param_i`. Each equation is one kernel evaluation of that string (about a minute; the
elaborator cannot do it), so they are kept in this file, which nothing but `Start.lean` imports.
`paramName_15` is in `ParamNames.lean`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Kernels.FlashKdaFwd

theorem paramName_0 : paramName 0 = param "0" := by kernel_rfl
theorem paramName_10 : paramName 10 = param "10" := by kernel_rfl
theorem paramName_11 : paramName 11 = param "11" := by kernel_rfl
theorem paramName_12 : paramName 12 = param "12" := by kernel_rfl
theorem paramName_13 : paramName 13 = param "13" := by kernel_rfl
theorem paramName_16 : paramName 16 = param "16" := by kernel_rfl

end PTX.Kernels.FlashKdaFwd.Proof.Thread
