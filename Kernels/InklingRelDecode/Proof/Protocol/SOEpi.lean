-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOSmExec

@[expose] public section

/-!
# The epilogue's poll of `o_final`

The epilogue (`Epi.D`, warps 0 to 3, all 128 threads) polls `o_final` of its CTA **once**, with
parity 0, before its `tcgen05.ld` of the `O` tile (`Epi.Shape.wait`), and takes no other part in
the handshake. The poll is the epilogue's first site on every path, also for a split with no block
(`num_iters < 1`, `D.sk`: the second kernel fix moved the poll in front of the `num_iters`
branch), so a thread's polls of `o_final` are zero or one:

* `epiPolled d`: the polls that have succeeded at state `d`: none at the `wait` site, one after
  it.
* `epi_okPoll_f`: a successful poll of `o_final` exactly at the `wait` site (the barrier is the
  state's: `Epi.Means`).
* `epi_fPolls`: along a run the polls number `epiPolled d - epiPolled d₀`.
* `epi_fwait`: at `wait` in a run from the start of the epilogue the event is the poll of `o_final`
  with parity 0, and no earlier poll of `o_final` was made: **the parity field of the barrier's
  thread-layer facts** (a poll with 0 earlier ones has parity 0, offset `δ = 0`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (okW count_trace countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (oFinal)

noncomputable section
set_option maxRecDepth 100000

/-- The successful `o_final` polls at epilogue state `d`. -/
def epiPolled (d : Epi.D) : Nat :=
  match d.site with | .wait => 0 | _ => 1

/-- A step of the epilogue raises `epiPolled` exactly at a successful poll at `wait`. -/
theorem epi_next_polled {d d' : Epi.D} {e : Event} (hi : Epi.Inv d)
    (h : Epi.next d e = some (some d')) :
    epiPolled d' = epiPolled d + if d.site = .wait ∧ okW e = true then 1 else 0 := by
  obtain ⟨site, pr, o, sk⟩ := d
  have hpre := hi.pre
  cases site
  all_goals
    simp only [Epi.next, Epi.stNext] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals simp_all [epiPolled, okW, Epi.D.stores]
    all_goals (repeat' split)
    all_goals simp_all
    all_goals split_ifs at *

variable {L : Launch} {g : Nat} {d0 : Epi.D}

theorem epi_pc_notWait (s : Epi.Site) (h1 : s ≠ .wait) : s.pc ∉ waitSites := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals try (exact absurd rfl h1)
  all_goals decide +kernel

variable {d : Epi.D} {e : Event} {u : TState}

/-- **A fired event of the epilogue at a site other than `wait` is not a poll.** -/
theorem epi_fired_notWait (hs : d.site ≠ .wait) (hF : Epi.Fired L g d e (some u)) :
    ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc := by
  obtain ⟨t, ha, -, hf⟩ := hF
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  have hn : NotWait ((Epi.code Epi.asms L g d).tmpl (some d) t) := by
    show NotWait (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Epi.asms L g t ins.op
      | none => Tmpl.ub .pcOutOfRange)
    split
    · rename_i ins hc
      exact eventTmpl_notWait (fun p b o par a s h => epi_pc_notWait d.site hs (wait_pc hc h))
    · trivial
  exact fires_notWait hn hf

/-- **The event of an epilogue state, as a count of `o_final` polls.** -/
theorem epi_okPoll_f {Q : Params} (hS : Sm.SharedOk L)
    (hm : Epi.Means Q L g d.pr) (hF : Epi.Fired L g d e (some u)) :
    okPoll (oFinal L (g / L.block)) e = (decide (d.site = .wait) && okW e) := by
  by_cases h1 : d.site = .wait
  · obtain ⟨ok, he⟩ := Epi.shape_wait_oFinal hS.2 hm hF h1
    rw [he, loc_oFinal]
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, h1]
  · have hnw := epi_fired_notWait h1 hF
    have hk : okPoll (oFinal L (g / L.block)) e = false := okPoll_notWait hnw
    have hw : okW e = false := by
      obtain ⟨pc, k⟩ := e
      cases k <;> first | rfl | exact absurd rfl (hnw _ _ _ _ _)
    rw [hk, hw]
    simp

variable {Q : Params} (hS : Sm.SharedOk L) {es : List Event}
    (hT : (Epi.code Epi.asms L g d0).toMachine.Trace (some d0) es)
    (hin : ∀ j < es.length, ∃ d1 : Epi.D,
      (Epi.code Epi.asms L g d0).toMachine.after (some d0) (es.take j) = some (some d1) ∧
        Epi.Inv d1 ∧ Epi.Means Q L g d1.pr) {d : Epi.D}
include hS hT hin

end
end PTX.Kernels.InklingRelDecode.Proof.SO
