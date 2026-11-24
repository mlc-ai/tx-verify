-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Lemmas.Flow.LoadShared
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

/-! # The MMA warp's memory events

An event of a lane of warp 12 that accesses memory is a read of a scheduler word, an MMA, or the
write or the read of the allocation word at `sb + 312` (`mma_mem`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- The allocation word of a lane's CTA. -/
def AllocAcc (L : Launch) (g : Nat) (a : Acc) : Prop :=
  a.size = 4 ∧ a.loc = ⟨.shared, g / L.block, L.sharedBase + 312⟩

end PTX.Kernels.TmlFa4Fwd.Proof

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The read of the allocation word. -/
private theorem ld_at (hp : Pre p L m) {v : Mma.V} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Mma.code p L g (Mma.ent p L)).AtD ⟨.ldAlloc, v⟩ t)
    (hc : kernel.code[(Mma.code p L g (Mma.ent p L)).pc ⟨.ldAlloc, v⟩]? = some ins)
    (hf : Fires ((Mma.code p L g (Mma.ent p L)).pc ⟨.ldAlloc, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) : AllocAcc L g a := by
  have hs0 : t.sub = 0 := h.2.1
  replace h : At t (Mma.Site.ldAlloc).pc (Mma.facts p L g (Mma.ent p L) ⟨.ldAlloc, v⟩) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  replace hc : kernel.code[(Mma.Site.ldAlloc).pc]? = some ins := hc
  have hsh := hp.shared
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  change Fires _ (loadTmpl Assumptions.all L g t .shared false 32 [1179] 2535 312) e o at hf
  have hr : t.regs 2535 = some (b32 L.sharedBase) :=
    (Mma.reg_of (d := ⟨.ldAlloc, v⟩) h (by lit_mem)).trans rfl
  have hea := effAddr_b32_off (L := L) (g := g) (off := 312) hr (by omega)
  refine shape_ld (P := fun e => ∀ a bs, e.kind = .rd a bs → AllocAcc L g a) hf hea hs0
    (fun bs _ a' bs' hk' => by cases hk'; exact ⟨rfl, rfl⟩)
    (fun f a' bs' hk' => by cases hk') a bs hk

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The MMA warp's memory events.** -/
theorem mma_mem (hw : Prologue.warpIndex L g = 12) {e : Event} (he : X.get (g, k) = some e)
    (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨ AllocAcc L g a)) ∨
      (∃ a bs, e.kind = .wr a bs ∧ AllocAcc L g a) ∨
      ∃ a s acc ms, e.kind = .tc (.mma a s acc ms) := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at hm; exact hm
  have hno : ∀ kd, e.kind = kd → ¬ MemKind kd → False := fun kd h h' => h' (h ▸ hm)
  rcases Mma.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨s, n, hσ, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1⟩
  · exact (start_mem hev hi.2 hm).elim
  · obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
    have hk3 := Mma.pre_kind hp hat hc hf
    cases s with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; exact (hno _ h id).elim
    | alloc => exact (hno _ (hk3.2.1 rfl) id).elim
    | wr =>
      obtain ⟨col, h⟩ := hk3.2.2 rfl
      exact .inr (.inl ⟨_, _, h, rfl, rfl⟩)
    | enter => exact absurd hi.2 (by simp [Mma.Start.exit])
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hF : Mma.MFits p L g d (n .shfl) (n .vote) := (hR h0).2
  cases hs : d.site
  case ldAlloc =>
    obtain ⟨site, v⟩ := d
    simp only at hs
    subst hs
    simp only [Mma.Ev] at hev1
    rcases hev1 with ⟨a, bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨a, bs, hk, .inr (ld_at hp hat hc hf hk)⟩
    · exact (hub f h).elim
  case word =>
    have hFE := Mma.efits hF (by rw [hs]; rfl)
    have hE := Mma.ev_toE (by rw [hs]; rfl) hev1
    simp only [Mma.Ev, hs, Mma.Site.toE, Epilogue.Ev] at hev1
    rcases hev1 with ⟨bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨_, bs, hk, .inl (Epilogue.sched_rd hp hFE hE hk)⟩
    · exact (hub f h).elim
  case q0 | q1 =>
    have hFE := Mma.efits hF (by rw [hs]; rfl)
    have hE : Epilogue.Ev p L g (Mma.toE d) e := by
      simp only [Mma.Ev, hs] at hev1
      simp only [Epilogue.Ev, Mma.toE, hs, Mma.Site.epi]
      exact hev1
    simp only [Mma.Ev, hs] at hev1
    rcases hev1 with ⟨bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨_, bs, hk, .inl (Epilogue.sched_rd hp hFE hE hk)⟩
    · exact (hub f h).elim
  case uk =>
    have hFE := Mma.efits hF (by rw [hs]; rfl)
    simp only [Epilogue.Fits, Mma.toE, hs, Mma.Site.epi] at hFE
    obtain ⟨R, bal, hC, -, -⟩ := hFE
    simp only [Mma.Ev, hs] at hev1
    rcases hev1 with ⟨bs, hk⟩ | ⟨f, h⟩
    · exact .inl ⟨_, bs, hk, .inl (Epilogue.usedK_rd rfl (rfl : _ = Kind.rd _ bs)
        (Epilogue.usedK_addr hp hC))⟩
    · exact (hub f h).elim
  case qk | pv =>
    simp only [Mma.Ev, hs] at hev1
    rcases hev1 with h | ⟨f, h⟩
    · exact .inr (.inr h)
    · exact (hub f h).elim
  all_goals simp only [Mma.Ev, hs] at hev1
  case down | up | total | pre | tiles | vote =>
    simp only [Epilogue.Ev, Mma.Site.toE] at hev1
    first
      | (obtain ⟨_, _, h⟩ := hev1; exact (hno _ h id).elim)
      | (obtain ⟨_, h⟩ := hev1; exact (hno _ h id).elim)
  case bcast | sh => obtain ⟨_, _, h⟩ := hev1; exact (hno _ h id).elim
  case wt | mw =>
    rcases hev1 with ⟨_, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case eq | ep | ce =>
    rcases hev1 with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case cm =>
    rcases hev1 with ⟨_, h, -, -⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  case relinq | dealloc =>
    rcases hev1 with ⟨_, _, h⟩ | ⟨f, h⟩
    · exact (hno _ h id).elim
    · exact (hub f h).elim
  all_goals exact (hno _ hev1 id).elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
