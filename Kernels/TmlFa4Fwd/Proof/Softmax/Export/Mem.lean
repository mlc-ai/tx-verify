-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemRead
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Read
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The softmax warps' memory events

An event of a softmax lane that accesses memory is a read of a scheduler word, a bias load or a
statistics store (`soft_mem`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The softmax warps' memory events.** -/
theorem soft_mem (hw : Prologue.warpIndex L g < 8) {e : Event} (he : X.get (g, k) = some e)
    (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨ Softmax.BiasAt L g a)) ∨
      ∃ a bs, e.kind = .wr a bs ∧ Softmax.StatAt L g a := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at hm; exact hm
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev⟩
  · exact (start_mem hev hi.2 hm).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hF : SmWarp.SFits p L g d (n .shfl) (n .vote) := (hR.2 h0).2
  have hFE := hF.1
  have hevR := SmWarp.fired_r hp hX he hσ hub
  have hev1 := hev.1
  have hno : ∀ kd, e.kind = kd → ¬ MemKind kd → False := fun kd h h' => h' (h ▸ hm)
  have hsched : d.scheduler.site = d.site := rfl
  cases hs : d.site <;> simp only [Softmax.Ev, hsched, hs] at hev1
  case word | q0 | q1 =>
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      rcases hev1 with h | ⟨f, h⟩
      · exact h
      · exact (hub f h).elim
    simp only [SmWarp.EvR, hsched, hs] at hevR
    exact .inl ⟨a, bs, hk, .inl (Epilogue.sched_rd hp hFE hevR hk)⟩
  case uk =>
    simp only [SmWarp.EvR, hsched, hs] at hevR
    rcases hevR with ⟨bs, hk⟩ | ⟨f, h⟩
    · simp only [Epilogue.Fits, SmWarp.toE, hsched, hs, SmWarp.epi] at hFE
      obtain ⟨R, bal, hC, -, -⟩ := hFE
      exact .inl ⟨_, bs, hk, .inl (Epilogue.usedK_rd rfl (rfl : _ = Kind.rd _ bs)
        (Epilogue.usedK_addr hp hC))⟩
    · exact (hub f h).elim
  case bld b c =>
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      rcases hev1 with h | ⟨f, h⟩
      · exact h
      · exact (hub f h).elim
    exact .inl ⟨a, bs, hk, .inr (Softmax.bld_at hp (d := d.scheduler) hat hc hf hs hk)⟩
  case stat pl =>
    rcases hev1 with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact .inr ⟨a, bs, hk, Softmax.stat_at hp (d := d.scheduler) hat (by
      have h := hi'.1
      change (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
      simpa only [Softmax.Control.Inv, hs] using h) hc hf (.inl ⟨pl, hs⟩) hk⟩
    · exact (hub f h).elim
  case fin j =>
    rcases hev1 with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact .inr ⟨a, bs, hk, Softmax.stat_at hp (d := d.scheduler) hat (by
      have h := hi'.1
      change (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
      simpa only [Softmax.Control.Inv, hs] using h) hc hf (.inr ⟨j, hs⟩) hk⟩
    · exact (hub f h).elim
  case sld =>
    unfold Softmax.tcLdOrUb at hev1
    rcases hev1 with ⟨_, _, _, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case sldw =>
    unfold Softmax.tcLdOrUb at hev1
    split at hev1
    · rcases hev1 with h | ⟨f, h⟩
      · exact (hno _ h id).elim
      · exact (hub f h).elim
    · rcases hev1 with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · exact (hno _ h id).elim
      · exact (hub f h).elim
  case pst =>
    split at hev1
    · exact (hno _ hev1 id).elim
    · rcases hev1 with ⟨_, _, _, h⟩ | ⟨f, h⟩
      · exact (hno _ h id).elim
      · exact (hub f h).elim
  case down | up | total | pre | tiles =>
    simp only [Epilogue.Ev, Softmax.Site.toE] at hev1
    obtain ⟨_, _, h⟩ := hev1
    exact (hno _ h id).elim
  case setmax => obtain ⟨_, _, _, h⟩ := hev1; exact (hno _ h id).elim
  case wq | ws | wb | pwend | wend | vote => obtain ⟨_, h⟩ := hev1; exact (hno _ h id).elim
  case fence => obtain ⟨_, _, h⟩ := hev1; exact (hno _ h id).elim
  case barEnd | pwst =>
    rcases hev1 with h | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case pws =>
    rcases hev1 with ⟨_, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case pel =>
    rcases hev1 with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  all_goals exact (hno _ hev1 id).elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
