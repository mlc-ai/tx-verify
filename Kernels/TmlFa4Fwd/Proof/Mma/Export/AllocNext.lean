-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Fact
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Lane 0 of the MMA warp is still at the allocation after its request

The allocation is two events on lane 0 of warp 12, the request and the store of the allocated
column, both at pc 1909. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The state after an allocation request of lane 0 of warp 12** is at the allocation. -/
theorem alloc_next (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) (hl : laneOf L g = 0) {k pc : Nat} {grp : CtaGroup}
    {dst : Option Loc} {nn : Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc nn))⟩) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g (k + 1) = some (some σ)) :
    (thread p L g).pc σ = 1909 := by
  have hG := good_at hp hX (Frame.lt_of_get hX he) hw k
  rcases good_cases hp hX he (by intro pc f h; cases h) hG with ⟨s, n, h0, hS, -⟩ |
    ⟨s, n, h0, -⟩ | ⟨dd, n, h0, -, hJ, -⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX he h0
    have := start_nores hev hx
    simp [Tmem.Pair.isTmemOp] at this
  · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he h0 (fun f h => by cases h)
    have hk3 := Mma.pre_kind hp hat hc hf
    rw [Frame.stateAt_succ (show (X.tr g)[k]? = _ from he), h0] at hσ
    have hn : (thread p L g).next (.inr ⟨.mma, .inl s⟩, n) _ = some (some σ) := hσ
    obtain ⟨σ', n'⟩ := σ
    obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
    simp only [glued, Code.glue, frag, Mma.M, Mma.G, Mma.S] at h1
    cases s with
    | set => obtain ⟨inst, hk⟩ := hk3.1 rfl; cases hk
    | alloc =>
      simp only [hl, ↓reduceIte, Option.map_some, Code.enter, Mma.Start.exit] at h1
      cases Option.some.inj h1
      rfl
    | wr => obtain ⟨c, hk⟩ := hk3.2.2 rfl; cases hk
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · exfalso
    have hrd := Mma.ev_res (mfired hp hX he h0).1 rfl
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he h0 (fun f h => by cases h)
    obtain ⟨r1, r2⟩ := Mma.rd_kind hp (d := dd) hat hc hf (by intro f h; cases h)
    obtain ⟨site, v⟩ := dd
    cases site <;> simp only [Mma.isRD, Bool.false_eq_true] at hrd
    · have := r1 ⟨_, rfl⟩; cases this
    · obtain ⟨a, h⟩ := r2 ⟨_, rfl⟩; cases h

/-- **An allocation request of warp 12** names the allocation word, and lane 0 is then at the store
of the allocated column, another lane at the first barrier. -/
theorem alloc_after (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {nn : Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc nn))⟩) :
    pc = 1909 ∧ dst = some ⟨.shared, g / L.block, L.sharedBase + 312⟩ ∧
      ∃ n, Frame.stateAt (thread p L) X g (k + 1) = some (some (.inr ⟨.mma,
        if laneOf L g = 0 then .inl .wr else .inr ⟨(), ⟨.bar1, {}⟩⟩⟩, n)) := by
  have hG := good_at hp hX (Frame.lt_of_get hX he) hw k
  rcases good_cases hp hX he (by intro pc f h; cases h) hG with ⟨s, n, h0, hS, -⟩ |
    ⟨s, n, h0, -⟩ | ⟨dd, n, h0, -, hJ, -⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX he h0
    have := start_nores hev hx
    simp [Tmem.Pair.isTmemOp] at this
  · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he h0 (fun f h => by cases h)
    have hk3 := Mma.pre_kind hp hat hc hf
    cases s with
    | set => obtain ⟨inst, hk⟩ := hk3.1 rfl; cases hk
    | alloc =>
      have hk := hk3.2.1 rfl
      simp only [Kind.tc.injEq, TcKind.resource.injEq] at hk
      refine ⟨Flow.fires_pc hf, hk.2.1, Code.bump (Proof.cls L g) n
        ⟨pc, .tc (.resource grp dst (.alloc nn))⟩, ?_⟩
      rw [Frame.stateAt_succ (show (X.tr g)[k]? = _ from he), h0]
      show (thread p L g).next (.inr ⟨.mma, .inl .alloc⟩, n) _ = _
      by_cases hl : laneOf L g = 0
      · simp [thread, glued, Code.counted, Code.glue, frag, Mma.M, Mma.G, Mma.S, hl, Code.enter,
          Mma.Start.exit]
      · simp [thread, glued, Code.counted, Code.glue, frag, Mma.M, Mma.G, Mma.S, hl, Code.enter,
          Mma.Start.exit]
    | wr => obtain ⟨c, hk⟩ := hk3.2.2 rfl; cases hk
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · exfalso
    have hrd := Mma.ev_res (mfired hp hX he h0).1 rfl
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he h0 (fun f h => by cases h)
    obtain ⟨r1, r2⟩ := Mma.rd_kind hp (d := dd) hat hc hf (by intro f h; cases h)
    obtain ⟨site, v⟩ := dd
    cases site <;> simp only [Mma.isRD, Bool.false_eq_true] at hrd
    · have := r1 ⟨_, rfl⟩; cases this
    · obtain ⟨a, h⟩ := r2 ⟨_, rfl⟩; cases h

/-- **Lane 0's event after its allocation request** is the store of the allocated column. -/
theorem alloc_store (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) (hl : laneOf L g = 0) {k pc : Nat} {grp : CtaGroup}
    {dst : Option Loc} {nn : Nat} {e : Event}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc nn))⟩)
    (he' : X.get (g, k + 1) = some e) :
    ∃ bytes, e = ⟨pc, .wr { loc := ⟨.shared, g / L.block, L.sharedBase + 312⟩, size := 4 }
      bytes⟩ := by
  obtain ⟨rfl, -, n, hσ⟩ := alloc_after hp hX hw he
  simp only [hl, ↓reduceIte] at hσ
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    strict_fired_site hp hX he' hσ rfl
  obtain ⟨col, hk⟩ := (Mma.pre_kind hp (s := .wr) hat hc hf).2.2 rfl
  obtain ⟨pc', kd⟩ := e
  have hpc : pc' = 1909 := Flow.fires_pc hf
  subst hpc
  simp only at hk
  subst hk
  exact ⟨_, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
