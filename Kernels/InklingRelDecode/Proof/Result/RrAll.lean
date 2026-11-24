-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RrOst
public import Kernels.InklingRelDecode.Proof.Result.RrRdv
public import Kernels.InklingRelDecode.Proof.Result.RrSoft

@[expose] public section

/-!
# The rendezvous-type and loader-side premises of `InputsRest`: umbrella

* `RrSoft`: `Rd.softAll : Rd.SoftAll L G` (the package's softmax threads are the default-partition
  threads of the CTA, `Sr.SoftOf`).
* `RrOst`: `Rr.ostIter_of : Rs.OStIter`, `Rr.ostBound_of`, `Rr.oaccOstIter_of` (the coordinate of a
  rescale store is the softmax state's loop counter: `Sr.OSt` carries the store's event and the
  count of the thread's `o_done` polls, `Rd.sm_cnt` gives `smOPolled d = d.i` at `stO`).
* `RrRdv`: `Rr.sRdv_of : Rd.SRdv` (thread 0's arrival of block `i`, `Mbar.Route.soft_bar` and
  named barrier 0's rendezvous `Bar.bar128Causal`; `Interface/RrArrive.lean` has the arrival's
  existence and count).
* `Interface/RrArrive.lean`: thread 0's arrival on `p_ready (i % 2)` in every iteration
  (`Rr.sm_reaches_arrive`, `Rr.arr_cnt`); `Interface/RrSObs.lean`: `Rr.sObserved_of :
  Life.SObserved` (not imported here: `AssembleProtocol.lean` imports it).
-/
