-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RequestSites
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- What an event at position `p` with `c` barrier-1 events and `r` register requests before it
satisfies: the position of each request fixes `c` and `r` (the dispatch loop's, up to the round),
a barrier-1 event after zero or two barrier-1 events follows one or two requests, and an exit
follows three barrier-1 events. -/
def ledgerOk (p c r : Nat) : Bool :=
  (!decide (p ∈ requestPcs) ||
    (p == 27 && c == 0 && r == 0) || (p == 574 && c == 1 && r == 1) ||
    (p == 2847 && c == 3 && r == 2) || (p == 2337 && r % 3 == 0) ||
    ((p == 2333 || p == 2344 || p == 2422) && c == 1 && r == 1) ||
    ((p == 2336 || p == 2420 || p == 2555) && c == 3 && r == 2)) &&
  (!decide (p ∈ barOneSites) ||
    ((c != 0 || decide (1 ≤ r)) && (c != 2 || decide (2 ≤ r)))) &&
  (p != 2855 || decide (3 ≤ c))

/-- The requests of the default partition. -/
def dataReq (p : Nat) : Bool := p == 27 || p == 574 || p == 2847

/-- The requests of the worker warps. -/
def workerReq (p : Nat) : Bool := [2333,2336,2337,2344,2420,2422,2555].contains p

end PTX.Kernels.InklingRelDecode.Proof.Lib
