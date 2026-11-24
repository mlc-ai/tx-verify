-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions.DelayedTmem
public import Assumption.PollAgree
public import Assumption.CommitOrder
public import Assumption.TcLdDataflow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Assumptions

open PTX.Assumption

/-- The 44 guarded uniform branches on the result of the preceding mbarrier poll. -/
def pollAgreeSites : List Nat :=
  [518, 680, 705, 731, 757, 783, 961, 1147, 1176, 1207, 1362, 1431, 1612, 1867, 1878, 1889, 1894,
   2142, 2146, 2211, 2295, 2298, 2353, 2420, 2546, 2549, 2596, 2959, 2973, 3421, 3426, 3499,
   4875, 5110, 5182, 6559, 6677, 7464, 7739, 8474, 8477, 8770, 8773, 9202]

/-- The four plain branches on the result of the preceding mbarrier poll. -/
def plainPollSites : List Nat := [2336, 2451, 2587, 2627]

/-- A warp spinning on one barrier relies on agreement for its `bra.uni` guard. -/
def pollAgree : Assumption :=
  pollAgreeAt "tml-fa4-fwd-poll-agree" pollAgreeSites
    "These loader, MMA, output, softmax and correction polls branch uniformly on their \
    lanes' individual mbarrier results without a warp vote. The four plain branches \
    in the MMA loop do not need this interpretation."

/-- The first Q-empty commit is issued by the MMA warp's elected lane. The loader's
Q tail waits for the following second-stage Q-empty commit and uses the same CTA. -/
def commitOrderSites : List Nat := [2537]

/-- The first-stage Q-empty arrival completes when the second-stage arrival is observed. -/
def commitOrder : Assumption :=
  commitOrderAt "tml-fa4-fwd-commit-order" commitOrderSites
    "The first-stage Q-empty commit at pc 2537 signals shared offset 16. The loader's tail \
    polls offset 24 at pc 1893, which observes the next commit (pc 2541) of the same \
    elected MMA lane. No tail poll observes the offset-16 release."

/-- The unbiased score loads and correction rescale loads that meet Core's dataflow check. -/
def tcLdDataflowSites : List Nat :=
  [6679, 6696, 6713, 6730, 8012, 8039, 8065, 8091, 8117, 8143, 8169, 8195, 8231, 8258,
   8284, 8310, 8336, 8362, 8388, 8414]

/-- These score loads wait for bias before their results are consumed. They do not satisfy
the existing dataflow check and have no explicit wait in the softmax role. -/
def tcLdUncoveredSites : List Nat := [3428, 3446, 3463, 3481, 5112, 5129, 5146, 5163]

/-- Completion by register consumption at the statically checked sites without an explicit
wait. The final output loads use their own explicit waits. -/
def tcLdDataflow : Assumption :=
  tcLdDataflowAt kernel "tml-fa4-fwd-tcld-dataflow" tcLdDataflowSites
    "The score loads of the unbiased loop and the accumulator loads in the correction \
    rescale loops have no wait::ld. Their results are consumed before the next memory, \
    barrier or tensor operation other than another load. Completion is used to order \
    reuse of the cells and deallocation of Tensor Memory."

/-- The synchronization assumptions with site evidence in the frozen kernel. -/
def synchronization : List Assumption := [pollAgree, commitOrder, tcLdDataflow, delayedTmem]

end PTX.Kernels.TmlFa4Fwd.Assumptions
