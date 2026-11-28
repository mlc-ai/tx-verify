-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring

@[expose] public section

/-! # The raw ring's handoff

Slot `s` of the raw ring of CTA `c`: the TMA lane (`RawTma`) issues the gathers of a use and
polls `rawFree s`; the dequant lanes (`RawDeq`) poll `rawReady s` and arrive on `rawFree s`. The
empty barrier is a unit handoff (offset 1) from the dequant lanes' arrivals to the TMA lane's
polls (`rawFree_handoff`, from `rawFree_observes`); the full barrier's completion is observed
directly (`rawReady_observes`, `Protocol/Shared/Raw.lean`). Both lanes are threads of CTA `c`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The TMA lane of CTA `c` among the launch's threads. -/
def RawTma (L : Launch) (X : Execution) (c g : Nat) : Prop := g < L.threads ∧ g = tmaThread L X c

/-- The dequant lanes of CTA `c` among the launch's threads. -/
def RawDeq (L : Launch) (c h : Nat) : Prop := h < L.threads ∧ ∃ y, h = deqLane L c y

/-- The TMA lane is a thread of its CTA. -/
theorem rawTma_cta (hp : Pre P L m) {c g : Nat} (h : RawTma L X c g) : g / L.block = c := by
  obtain ⟨-, rfl⟩ := h
  have := tmaThread_mod (X := X) hp c
  rw [hp.block]
  omega

/-- A dequant lane is a thread of its CTA. -/
theorem rawDeq_cta (hp : Pre P L m) {c h : Nat} (hh : RawDeq L c h) : h / L.block = c := by
  obtain ⟨-, y, rfl⟩ := hh
  have := y.isLt
  simp only [deqLane, hp.block]
  omega

/-- The CTA of a TMA lane has a dequant lane. -/
theorem rawTma_deq (hp : Pre P L m) {c g : Nat} (h : RawTma L X c g) :
    ∃ h', RawDeq L c h' := by
  have hc := rawTma_cta hp h
  obtain ⟨hg, -⟩ := h
  refine ⟨deqLane L c 0, ?_, 0, rfl⟩
  simp only [Launch.threads, hp.block, deqLane] at hg ⊢
  rw [hp.block] at hc
  omega

/-- A TMA lane and a dequant lane of one CTA are threads of one CTA. -/
theorem rawTma_sameCta (hp : Pre P L m) {c g h : Nat} (hg : RawTma L X c g) (hh : RawDeq L c h) :
    SameCta L g h := ⟨hg.1, hh.1, (rawTma_cta hp hg).trans (rawDeq_cta hp hh).symm⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hp hX hFw hR hI hB hN

/-- **The empty handoff of the raw ring**: the TMA lane's successful poll of `rawFree s` with
`q + 1` earlier ones synchronizes with every dequant lane's arrival of use `q`. -/
theorem rawFree_handoff (c : Nat) (s : Fin 2) :
    UnitHandoff L X (mbarLoc L c (.rawFree s)) (RawDeq L c) (RawTma L X c) 1 :=
  handoff_of_observes hX hR (fun _ _ hg hh => by
    obtain ⟨h1, h2, h3⟩ := rawTma_sameCta hp hh hg
    exact ⟨h2, h1, h3.symm⟩) fun _ he hq g hg => by
    obtain ⟨-, b, rfl⟩ := hg
    obtain ⟨-, hall⟩ := rawFree_observes hp hX hFw hR hI hB hN he hq
    exact hall b

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
