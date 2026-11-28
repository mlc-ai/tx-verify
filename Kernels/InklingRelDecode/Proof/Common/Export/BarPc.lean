-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.BarSchedule
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.BarPc
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame

private theorem cls_bar (i : Nat) : cls (.bar i) = Execution.isBarId i := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> rfl

/-- **The pc of a data lane's rendezvous by its ordinal.** At a barrier event of a data thread
(a thread of the first four warps) the pc is the entry of `Lib.dataBar` at the number of earlier
barrier events that are not visits of the optional rescale rendezvous; the optional rendezvous
itself stands where the schedule has the round's fourth fixed one. -/
theorem data_bar_pc {Q L m X g k pc id cnt md} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.bar id cnt md⟩) (lg : g%L.block < 128) :
    let es := (X.tr g).take k
    let t := es.countP (Execution.isBarId 0) + es.countP (Execution.isBarId 1) -
      es.countP (fun e => e.pc == 2326)
    pc = Lib.dataBar (Iface.preloadCount Q L (g/L.block)) (Lib.blocksOf Q L (g/L.block)) t ∨
      (pc = 2326 ∧ Lib.dataBar (Iface.preloadCount Q L (g/L.block))
        (Lib.blocksOf Q L (g/L.block)) t = 999) := by
  have hg := Frame.lt_of_get hX he
  have nu := Frame.noUbBefore_of_get hX he
  have clean : ∀ f, (⟨pc,.bar id cnt md⟩ : Event).kind ≠ .ub f := by simp
  obtain ⟨⟨s,n⟩,hs,guard⟩ := event_table hf hX hp he clean
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have tab := guard (prefix_ub_zero hs nu)
  have pcs := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs clean
  have pub := publication_prefix hp hX hg nu hs
  have c0 := fcount hs (.bar 0)
  have c2 := fcount hs (.atPc 2326)
  rw [cls_bar] at c0
  change pc = _ at pcs
  have site : BarSitePc ((thread Q L g).pc (s,n)) := by
    rw [← pcs]
    obtain ⟨-, one | full | half⟩ := Lib.recorded_bar hX hp.block he
    · exact .inl one.2.2
    · exact .inr (decide_eq_true (List.mem_append_left _ full.2.2))
    · exact .inr (decide_eq_true (List.mem_append_right _ half.2.2))
  have key := data_bar_state hp hX hg hk hs nu tab lg site
  have c2' : n (.atPc 2326) = ((X.tr g).take k).countP (fun e => e.pc == 2326) := c2
  have eq : n (.bar 0) + publication (s,n) - n (.atPc 2326) =
      ((X.tr g).take k).countP (Execution.isBarId 0) +
        ((X.tr g).take k).countP (Execution.isBarId 1) -
      ((X.tr g).take k).countP (fun e => e.pc == 2326) := by
    rw [← pub, ← c0, c2']
  unfold DataBarAt at key
  simp only [eq] at key
  rcases key with h | ⟨h1, h2⟩
  · exact .inl (pcs.trans h)
  · exact .inr ⟨pcs.trans h1, h2⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
