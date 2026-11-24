-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Data.Decoded
public meta import Kernels.TmlFa4Fwd.Data.Decoded
public import Kernels.TmlFa4Fwd.Flow.Sites
public meta import Kernels.TmlFa4Fwd.Flow.Sites

open PTX.Kernels.TmlFa4Fwd

/- Check that the decoder supplies a rule for every instruction and that
the generator's event sites are exactly the non-local instruction counters. -/
#eval show IO Unit from do
  let code := Decoded.kernel.code
  unless code.length == 9206 do throw (IO.userError s!"instruction count: {code.length}")
  let missing := code.zipIdx.filterMap (fun (i, pc) =>
    if i.op.rule.isSome then none else some pc)
  unless missing.isEmpty do throw (IO.userError s!"instructions without rules: {missing}")
  let actual := code.zipIdx.filterMap (fun (i, pc) => if i.op.isLocal then none else some pc)
  unless actual == Flow.all do
    let extra := Flow.all.filter (fun pc => !actual.contains pc)
    let absent := actual.filter (fun pc => !Flow.all.contains pc)
    throw (IO.userError s!"event site mismatch: extra {extra}; absent {absent}")
