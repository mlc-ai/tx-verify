-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerClc
public import Kernels.Fp16Gemm8192.Proof.Thread.AccTiles
public import Kernels.Fp16Gemm8192.Proof.Thread.ReaderExitCons
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex

@[expose] public section

/-! # A consumer's named barrier arrivals and response reads at its trace's end

Projections of the consumer's run invariants at the end of a trace. The arrivals on the group's CLC
barrier follow from the response polls (`cons_clc`) and the tile count (`cons_tiles`); the arrivals
on the output barrier follow from `OutTile` and the accumulator count (`cons_acc_count`). Every
response read but the latest, which follows a successful poll that is not the latest, names a
response that claims a CTA (`ReadInv`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A consumer's barrier arrivals at its trace's end.** -/
theorem cons_bars_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) :
    (X.tr g).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c.clcHold +
        Consumer.holds c = consCount L g (X.tr g) + Consumer.tileOpen c ∧
      Consumer.outBars L g (X.tr g) + 16 * (Consumer.holds c + c.inEpi) =
        16 * consCount L g (X.tr g) + c.outPhase ∧
      c.started + Consumer.holds c ≤ consCount L g (X.tr g) := by
  have h1 := cons_clc hpre hX hg hσ
  rw [List.take_length] at h1
  have h2 := cons_tiles hpre hX hg hσ
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have h3 := consInv hpre hg htr (X.tr g).length _ hσ
  rw [List.take_length] at h3
  have h4 : Consumer.OutTile L g c (X.tr g) := h3.2.2.2.2.2.1
  have h5 := Consumer.cons_acc_count hpre hX hg hσ
  unfold Consumer.OutTile at h4
  refine ⟨by omega, by omega, by omega⟩

/-- **A consumer's barrier arrivals along its run.** At any prefix, its arrivals on its group's CLC
barrier, with the response it holds, are its tiles plus its open task, and its arrivals on its
output
barrier, with the sixteen of its epilogue in progress, are sixteen per tile plus its slice's
position. -/
theorem cons_bar_phase_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    ∃ q, ((X.tr g).take k).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) +
        c.clcHold = q + Consumer.tileOpen c ∧
      Consumer.outBars L g ((X.tr g).take k) + 16 * c.inEpi = 16 * q + c.outPhase := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨h1, h2, -⟩ := clcPoll_inv hpre hg htr k _ hσ
  have h3 := consInv hpre hg htr k _ hσ
  have h4 : Consumer.OutTile L g c ((X.tr g).take k) := h3.2.2.2.2.2.1
  unfold Consumer.OutTile at h4
  exact ⟨arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) ((X.tr g).take k), by omega,
    by omega⟩

/-- **A consumer's response reads before an event of its trace.** A response read right after a
successful poll that is not the latest one there names a response that claims a CTA. -/
theorem cons_claims_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    ∀ j pc p acq sc pcr src bs rr, ((X.tr g).take k)[j]? =
        some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      ((X.tr g).take k)[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g →
      src.size = 16 → Flow.responseOf bs = some rr →
      okPolls (clcResp L g) (((X.tr g).take k).take j) + 1 <
        okPolls (clcResp L g) ((X.tr g).take k) →
      Loader.claims rr := by
  have h' := Consumer.readInv_of hpre hX hg hσ
  intro j pc p acq sc pcr src bs rr ha hb hl hs hr hlt
  by_contra hc
  have h3 := (h'.1.1 j pc p acq sc pcr src bs rr ha hb hl hs hr hc).1
  omega

/-- **A consumer's state after a named barrier arrival is in its task loop**: the barrier sites'
successors are the acknowledgement, the accumulator poll, a slice's stores, fence, TMA store and
commit. -/
theorem cons_after_bar_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {id : Nat}
    {cnt : Option Nat} {c0 c : Consumer.D} (he : X.get (g, k) = some e)
    (hk : e.kind = .bar id cnt) (hσ0 : Frame.stateAt (code L) X g k = some (some (.inr (.cons c0))))
    (hσ1 : Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c)))) :
    Consumer.exitOff c = none ∧ c.site ≠ .setMaxReg := by
  have hrw := role_warp hpre hX hg k (len_of_get he).le _ hσ0
  have htid : Consumer.tidOf L g < 256 := by
    simp only [roleWarp, Prologue.warpOf] at hrw
    simp only [Consumer.tidOf]
    omega
  obtain ⟨-, -, -, -, h5, -⟩ := cons_out_facts hpre hX hg he hσ0 htid
  have hnext : Frame.stateAt (code L) X g (k + 1) = (Consumer.next L g c0 e).map
      (Option.map fun c' => (Sum.inr (Prologue.Role.cons c') : ThreadD)) := by
    rw [Frame.stateAt_succ he, hσ0]
    rfl
  rw [hnext] at hσ1
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c0
  rcases h5 id cnt hk with ⟨hs, -⟩ | ⟨⟨s, hs | hs⟩, -⟩ <;> simp only at hs <;> subst hs <;>
    simp only [Consumer.next] at hσ1 <;> (try split_ifs at hσ1) <;>
    simp at hσ1 <;> subst hσ1 <;> simp [Consumer.exitOff]

end
end PTX.Kernels.Fp16Gemm8192.Proof
