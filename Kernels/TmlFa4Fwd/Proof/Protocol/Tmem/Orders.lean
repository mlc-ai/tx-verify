-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.ScoreDone

@[expose] public section

/-! # No unordered Tensor Memory writes or MMA reads, from the hand-offs -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- **The hand-offs the Tensor Memory orders need**, each a channel's statement. -/
structure Handoffs (L : Launch) (X : Execution) : Prop where
  s : SFullHandoff L X
  p : PReadyHandoff L X
  p2 : P2Gate L X
  o : OFullHandoff L X
  route : ORoute L X

/-- The protocols' orders between MMAs and stores, from the hand-offs. -/
theorem tcOrders (ht : ScoreFacts L X) (ho : OAccFacts L X) (hH : Handoffs L X) : TcOrders L X where
  s_done := fun hh hw hi hc hu hf => s_doneBefore ht hH.s hh hw hi hc hu hf
  p_done := fun hh hw hs hf hc hl hhi => store_done ht hH.p hH.p2 hh hw hs hf hc hl hhi
  o_store_done := fun hh h8 h12 hst hs hj hO hf hc hu =>
    o_store_done ht ho hH.p hh h8 h12 hst hs hj hO hf hc hu
  o_done_store := fun hh h8 h12 hs hj hO hx hxc hc hu =>
    o_done_store ho (oready ht hH.s hH.o hH.route) hh h8 h12 hs hj hO hx hxc hc hu

/-- **No two Tensor Memory writes of one cell are unordered**, from the hand-offs. -/
theorem writes_safe (hp : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hH : Handoffs L X) : ¬ WritesUnsafe L X :=
  no_writes_unsafe hp ht ho (tcOrders ht ho hH)

/-- **No MMA read is unordered with a writer of its cell**, from the hand-offs. -/
theorem reads_safe (hp : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hH : Handoffs L X) : ¬ ReadsUnsafe L X :=
  no_reads_unsafe ht ho (tcOrders ht ho hH) fun hw hx hthr hlt =>
    scoreDonePv hp ht hH.s hH.p hw hx hthr hlt

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
