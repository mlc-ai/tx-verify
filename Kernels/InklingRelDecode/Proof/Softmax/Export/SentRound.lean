-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
import Kernels.InklingRelDecode.Proof.Softmax.Soft.SentState
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent

/-! # The round of a shuffle of pc 1838, from the shuffles before it

The shuffles a lane made before its shuffle of pc 1838 are the startup's, the preloads', the
rounds' before, and the first of its round, so the count fixes the round, and the lane 16 away has
the same count at the same round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The shuffles before a shuffle of pc 1838** count its round. -/
public theorem shfl5_count {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩) :
    ((X.tr g).take k).countP Execution.isShfl = 1 + Iface.preloadCount Q L (g / L.block) +
      Lib.shflBase (pollRound 1257 ((X.tr g).take k) - 1) + 1 ∧
    0 < pollRound 1257 ((X.tr g).take k) := by
  obtain ⟨w, ent, d, y, n, hsc, -, -, hyd, site, -⟩ := sent_state hp hX hf get
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have ref := (reached_table hf hg nu hsc).2
  change Softmax.Ref _ d (softCounts n) at ref
  have total := shfl_ordinal hp hX len hsc nu
  have score := congrArg Cnt.s ref.ledger
  change n (.poll 1257) = d.i + d.site.afterS.toNat at score
  have count (key : Cls) : n key = ((X.tr g).take k).countP (cls key) := fcount hsc key
  have ds : d.site = .shfl5 := hyd ▸ site
  rw [count] at score total
  have as : d.site.afterS.toNat = 1 := by rw [ds]; rfl
  have ir : shflInRound d.site d.i = 1 := by rw [ds]; rfl
  simp only [shflCount, ir] at total
  change pollRound 1257 ((X.tr g).take k) = d.i + d.site.afterS.toNat at score
  refine ⟨total.trans ?_, by omega⟩
  rw [score, as, Nat.add_sub_cancel]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
