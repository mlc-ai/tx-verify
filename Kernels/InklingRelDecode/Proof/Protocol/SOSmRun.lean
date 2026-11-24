-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmEvents

@[expose] public section

/-!
# The default partition's handshake counts along a run

* `sm_count`: the counting theorem along a run of the softmax region's machine
  `Sm.code Sm.asms L g d₀`: the count of a class of events `p` is the change of a measure `μ` of
  the abstract state if each step changes it by one exactly at the events `p` counts. The
  states of a run that reaches a state (`after = some (some d)`) are all states of the machine
  (`after_some`).
* `sm_sPolls`: along a run, the successful polls of `s_ready b` number
  `below2 b (smPolled d) - below2 b (smPolled d₀)`.
* `sm_pArrivals`: for thread 0 of the block, the arrivals on `p_ready b` of a run number
  `below2 b d.i - below2 b d₀.i`; any other thread has none (`sm_pArrivals_nonlead`).
* `sm_swait`: at the `waitS` site, in a run from the start of the region (`smPolled d₀ = 0`), the
  event is the poll of `s_ready (i % 2)` with parity `fullParity i`, for the thread's `n`-th block
  of that buffer (`i = blockB b n`, `n` its earlier polls of that barrier), and its parity is
  `n % 2`.
* `sm_parrive`: at the `arrive` site, in a run from the start of the region, the event is the
  arrival on `p_ready (i % 2)` and `i = blockB b n`, `n` the earlier arrivals on that barrier.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW count_trace)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d0 : Sm.D}

/-! ### The kinds of events that end a thread count nothing -/

theorem ends_not_okW {e : Event} (h : Ends e) : okW e = false := by
  obtain ⟨pc, k⟩ := e
  rcases h with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;> simp [okW]

/-! ### The counts -/

/-- **A step of the softmax region, for the arrivals of thread 0**: the loop counter rises at the
`arrive` site. -/
theorem sm_next_arrived {d d' : Sm.D} {e : Event} (hlead : g % L.block = 0)
    (h : Sm.next L g d e = some (some d')) :
    d'.i = d.i + if d.site = .arrive then 1 else 0 := by
  obtain ⟨site, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases site
  all_goals
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup, Sm.toBar20, hlead, ite_true] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals simp_all [Sm.D.upd, Sm.D.afterSum]

end
end PTX.Kernels.InklingRelDecode.Proof.SO
