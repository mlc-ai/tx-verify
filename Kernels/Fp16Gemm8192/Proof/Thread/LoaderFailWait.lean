-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks

@[expose] public section

/-! # A loader at its response wait has read no non-claiming response after a response poll

The loader's response relation (`LoaderTasks.Rel`) holds a read after each successful response poll
of a live loader to a response that claims a CTA; the loader at its response wait is live, and a
successful response poll that is the thread's last event leaves it at its read, not at the wait. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A loader at its response wait has read no non-claiming response after a successful response
poll**: each read after a successful poll of its CTA's response barrier names a response that
claims a CTA. -/
theorem loader_fail_wait_thm {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {l : Loader.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .clcWait) :
    ∀ j pc p acq sc pcr src bs rr,
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ →
      Flow.responseOf bs = some rr → Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have c : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length (.inr (.loader l))
      (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  have hLive : LoaderTasks.Live l := by
    unfold LoaderTasks.Live
    rw [hs]
    trivial
  intro j pc p acq sc pcr src bs rr hw hr _hfp hrr
  have hw' : (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := hw
  have hr' : (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ := hr
  have hj1 : j + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hr').1
  obtain ⟨pcr', src', bs', rr', hr2, -, -, hrr2, hcl⟩ := c.rel.1 j pc p acq sc hj1 hw' hLive
  rw [hr'] at hr2
  obtain ⟨-, rfl, rfl⟩ : pcr = pcr' ∧ src = src' ∧ bs = bs' := by
    simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hr2
    exact ⟨hr2.1, hr2.2.1, hr2.2.2⟩
  rw [hrr] at hrr2
  cases hrr2
  exact hcl

end
end PTX.Kernels.Fp16Gemm8192.Proof
