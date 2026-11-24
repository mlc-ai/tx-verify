-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof2.Lib.BarLaneKeys
public import Kernels.InklingRelDecode.Proof.Protocol.MbarRoute

@[expose] public section

/-!
# The 128-thread generations of named barrier 0

Named barrier 0 has three groups in turn (the development notes, "Protocol `ctaBar`"). Its arrivals
follow
the classification `NamedBar.PhSources` for the loop group `D` = warps 0 to 3 with the count 128
from the source ordinal 2 on (`bar0_sources`, from `Interface.bar0_event_class`), so the phased
generation ledger of `BarLanePhase.lean` and the key lemmas of `BarLaneKeys.lean` apply, and
the loop's generations are proved as the premises of the consumers state them:

* `bar128Witness`: exactly the statement of `Mbar.Bar128Witness`;
* `bar128Causal`: the base-causality form, **with the event before the first arrival**: two
  default-partition threads of one CTA at `bar.sync 0, 128` events of one barrier-0 ordinal, the
  second passed: every earlier event `before < a` of the first is base-causally before every
  later event of the second. The statement `Sr.Bar128Causal` takes the first arrival `(g, a)`
  itself as the earlier event; it is not provable, because `CtaBarSync` and program order leave an
  event only towards later events of its thread, and `(g, a)` can be its thread's last event (the
  second thread passes once the warp's record exists, and the first thread's trace may end at its
  arrival). `Sr.BarChain` uses it only with the event `(t, wk)` before the arrival, which is the
  form proved here.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The loop group of named barrier 0: warps 0 to 3. -/
def loopGroup : Finset Nat := Finset.range 4

theorem loopGroup_sub (hpre : Pre Q L mem0) :
    loopGroup ⊆ Finset.range (CtaBarrier.warps L.block) := by
  intro w hw
  have hb : L.block = 256 := hpre.block
  simp only [loopGroup, Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢
  omega

theorem loopGroup_card : loopGroup.card = 4 := by
  simp [loopGroup]

theorem loopGroup_ne (hpre : Pre Q L mem0) : 4 ≠ CtaBarrier.warps L.block := by
  have hb : L.block = 256 := hpre.block
  simp [CtaBarrier.warps, hb]

theorem loopGroup_target : CtaBarrier.target L.block (some 128) = .ok 4 := by
  simp [CtaBarrier.target]

/-- **The arrivals on barrier 0 follow the three groups' classification**: no count, or the
count 128 with a warp of the default partition and a source ordinal at least 2. -/
theorem bar0_sources (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    NamedBar.PhSources L X loopGroup (some 128) 2 0 := by
  intro e pc cnt ⟨mode, he⟩ hg
  obtain ⟨g, k⟩ := e
  rcases bar0_event_class hpre hX hS ht he with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · refine .inr ⟨h1, ?_, h3⟩
    simp only [loopGroup, Finset.mem_range]
    omega

/-- **`Mbar.Bar128Witness`, as the premise states it**: two default-partition threads of one CTA
at `bar.sync 0, 128` events with the same number of earlier barrier-0 events, the second passed:
the first's event is a witness of the second's return. -/
theorem bar128Witness (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    Mbar.Bar128Witness L X := by
  intro g p a y pc pc' hg hp hcta hg' hp' hga hpy hy hord
  have hw : ∀ {t : Nat}, t % L.block < 128 → (t % L.block) / 32 ∈ loopGroup := by
    intro t h
    simp only [loopGroup, Finset.mem_range]
    omega
  exact NamedBar.D_same_ordinal_witness hX (bar0_sources hpre hX hS ht) (loopGroup_sub hpre)
    loopGroup_card (loopGroup_ne hpre) loopGroup_target ⟨hg, hp, hcta⟩ hga hpy hy (hw hg')
    (hw hp') hord

/-- **`Sr.Bar128Causal` with the earlier event before the first arrival**: two default-partition
threads of one CTA at `bar.sync 0, 128` events of one barrier-0 ordinal, the second thread passed:
every event of the first thread before its arrival is base-causally before every later event of
the second. -/
theorem bar128Causal (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    ∀ {g p a y before f pc pc' : Nat}, g < L.threads → p < L.threads →
      g / L.block = p / L.block → g % L.block < 128 → p % L.block < 128 →
      X.get (g, a) = some ⟨pc, .bar 0 (some 128) .sync⟩ →
      X.get (p, y) = some ⟨pc', .bar 0 (some 128) .sync⟩ →
      ((X.tr g).take a).countP (Execution.isBarId 0) = ((X.tr p).take y).countP
        (Execution.isBarId 0) → before < a → y < f → f < (X.tr p).length →
      baseCausality L X (g, before) (p, f) := by
  intro g p a y before f pc pc' hg hp hcta hg' hp' hga hpy hord hb hyf hf
  have hw : ∀ {t : Nat}, t % L.block < 128 → (t % L.block) / 32 ∈ loopGroup := by
    intro t h
    simp only [loopGroup, Finset.mem_range]
    omega
  exact NamedBar.D_same_ordinal_baseCausality hX (bar0_sources hpre hX hS ht) (loopGroup_sub hpre)
    loopGroup_card (loopGroup_ne hpre) loopGroup_target ⟨hg, hp, hcta⟩ hga hpy (by omega)
    (hw hg') (hw hp') hord hb hyf hf

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
