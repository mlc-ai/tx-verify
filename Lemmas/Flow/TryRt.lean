-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean

@[expose] public section

/-! # Runtime errors as ordinary failures

`first` and `try` do not catch runtime errors (the maximum recursion depth, the heartbeat limit):
an evaluation that runs away (a comparison of a free word, `w + 4294967294` unfolded) ends the
whole tactic instead of letting the next alternative run. `try_rt tac` (also spelled
`catch_rt tac`) runs `tac` and turns such an error into an ordinary failure, restoring the state.
The library's segment, closing and normalising tactics (`seg_fp`, `seg_auto`, `sym_close`,
`seg_close`, `site_norm`) use it, so their fallbacks run. -/

namespace PTX.Flow
open Lean Elab Tactic

/-- `try_rt tac`: `tac`, with a runtime error turned into an ordinary failure. -/
elab "try_rt " t:tacticSeq : tactic => do
  let saved ← saveState
  let n0 := (← Core.getMessageLog).toList.length
  -- the new message must differ from the runtime one, which is how such an error is recognized
  tryCatchRuntimeEx (evalTactic t) fun e => do
    -- an aborted elaboration (`abortTactic`, "internal exception #5") has logged its error under
    -- error recovery; that log is restored away with the state, so its errors are reported here
    let logged := ((← Core.getMessageLog).toList.drop n0).filter (·.severity == .error)
    saved.restore (restoreInfo := true)
    if logged.isEmpty then throwError "try_rt: {e.toMessageData}"
    else
      throwError "try_rt: {e.toMessageData}: {MessageData.joinSep
        (logged.map (·.data)) Format.line}"

/-- `catch_rt tac`: the same as `try_rt tac`. -/
macro "catch_rt " t:tacticSeq : tactic => `(tactic| try_rt $t)

end PTX.Flow
