-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WqLock
public import Kernels.InklingRelDecode.Proof.Thread.WqDispatch

@[expose] public section

/-!
# The key time and the lockstep at every state (`Wq*`)

* `Thread/WqKxD.lean`, `Thread/WqKxW*.lean`: the key time of a state (`Lk.kxD`, `Lk.kxW`) and its
  static facts, machine by machine.
* `Thread/WqDispatch.lean`: the dispatch's successor times (`Lk.dispatch_time`) and the polls'
  positions are not synchronizing (`Lk.wait_notSy`).
* `Interface/WqKx.lean`: `Lk.kx` and its facts at the level of the thread machine.
* `Interface/WqLock.lean`: `Lk.lock_any` (one key at one synchronizing ordinal, at every state) and
  `Lk.kx_lock` (one key time).
-/
