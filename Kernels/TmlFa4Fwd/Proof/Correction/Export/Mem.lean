-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemRead
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The correction warps' memory events

An event of a correction lane that accesses memory is a read of a scheduler word, a statistics
load, a final store or an LSE store (`corr_mem`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The correction warps' memory events.** -/
theorem corr_mem (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {e : Event} (he : X.get (g, k) = some e) (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨ ∃ n st : Fin 2, a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 368 + 1024 * n.val +
        4 * (128 * st.val + Correction.rowN L g)⟩)) ∨
      ∃ a bs, e.kind = .wr a bs ∧
        ((∃ st, Correction.FstAt L g st a) ∨ a.loc.space = .global) := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at hm; exact hm
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev1, hevR⟩
  · exact (start_mem hev hi.2 hm).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  obtain ⟨rv, -, -, hFE, -⟩ : CorrWarp.CFits p L g d (n .shfl) (n .vote) := (hR h0).2
  have hno : ∀ kd, e.kind = kd → ¬ MemKind kd → False := fun kd h h' => h' (h ▸ hm)
  have hst : ∀ {n st : Fin 2}, d.site.statRd = some (n, st) → Correction.rdOrUb e →
      ∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨ ∃ n st : Fin 2, a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 368 + 1024 * n.val +
        4 * (128 * st.val + Correction.rowN L g)⟩) := by
    intro n st hs h
    rcases h with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact ⟨a, bs, hk, .inr ⟨n, st, Correction.stat_rd hp hat hi' hc hf hs hk⟩⟩
    · exact (hub f h).elim
  rcases hev1.data_or_vote with hev1 | ⟨_,_,hv⟩
  case inr => rw [hv] at hm; exact hm.elim
  have hsched : d.scheduler.site = d.site := rfl
  cases hs : d.site <;> simp only [Correction.Ev, hsched, hs] at hev1
  case word | q0 | q1 =>
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      rcases hev1 with h | ⟨f, h⟩
      · exact h
      · exact (hub f h).elim
    simp only [CorrWarp.EvR, hsched, hs] at hevR
    exact .inl ⟨a, bs, hk, .inl (Epilogue.sched_rd hp hFE hevR hk)⟩
  case uk =>
    simp only [CorrWarp.EvR, hsched, hs] at hevR
    rcases hevR with ⟨bs, hk⟩ | ⟨f, h⟩
    · simp only [Epilogue.Fits, CorrWarp.toE, hsched, hs, CorrWarp.epi] at hFE
      obtain ⟨R, bal, hC, -, -⟩ := hFE
      exact .inl ⟨_, bs, hk, .inl (Epilogue.usedK_rd rfl (rfl : _ = Kind.rd _ bs)
        (Epilogue.usedK_addr hp hC))⟩
    · exact (hub f h).elim
  case rscale st => exact .inl (hst (n := 0) (st := st) (by rw [hs]; rfl) hev1)
  case fsum st => exact .inl (hst (n := 0) (st := st) (by rw [hs]; rfl) hev1)
  case fmax st => exact .inl (hst (n := 1) (st := st) (by rw [hs]; rfl) hev1)
  case fst st j hh =>
    rcases hev1 with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact .inr ⟨a, bs, hk, .inl ⟨st, Correction.fst_at hp hat hc hf hs hk⟩⟩
    · exact (hub f h).elim
  case lse hh =>
    rcases hev1 with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact .inr ⟨a, bs, hk, .inr (Correction.lse_wr hat hc hf ⟨hh, hs⟩ hk)⟩
    · exact (hub f h).elim
  case rld | fld | rst =>
    rcases hev1 with ⟨_, _, _, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case rldw =>
    rcases hev1 with h | ⟨_, _, _, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case down | up | total | pre | tiles =>
    simp only [Epilogue.Ev, Correction.Site.toE] at hev1
    obtain ⟨_, _, h⟩ := hev1
    exact (hno _ h id).elim
  case setmax => obtain ⟨_, _, _, h⟩ := hev1; exact (hno _ h id).elim
  case fw | wend | vote | rvote => obtain ⟨_, h⟩ := hev1; exact (hno _ h id).elim
  case fence => obtain ⟨_, _, h⟩ := hev1; exact (hno _ h id).elim
  case barEnd | rwait =>
    rcases hev1 with h | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  all_goals exact (hno _ hev1 id).elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
