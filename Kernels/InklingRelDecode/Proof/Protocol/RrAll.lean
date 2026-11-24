-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RrArrive
public import Kernels.InklingRelDecode.Proof.Interface.RrSObs

@[expose] public section

/-!
# Premises of `ProtocolRest` proved from the thread layer: umbrella

* `Interface/RrArrive.lean`: thread 0 of the default partition arrives on `p_ready (i % 2)` in
  every iteration of a complete execution (`Rr.sm_reaches_arrive`), the arrivals along its states
  (`Rr.arr_cnt`), thread 0 of a CTA (`Rr.thread0`);
* `Interface/RrSObs.lean`: `Rr.sObserved_of : Life.SObserved` (every `s_ready` commit of an exited
  CTA is observed).
-/
