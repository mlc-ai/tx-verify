-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords

@[expose] public section

/-!
# The machines continue at the event they fire

`Safety.Protocol.faultFree` asks that no followed event be one the machine's `next` rejects with
`none` (it has to be restricted to events with a later event: `ShapeTrace.next_ret_none`). The
roles' `next` returns `none` (a thread that is dead) in two kinds of place: the event is not of
the kind the site matches on, and a value is outside the domain. At a continuing event the kind is
the one of the site's shape, so for the roles that have a shape theorem for every site only the
value-dependent `none` remains:

* `loader_next_ne_none`: the bytes of its reads are those of a 32-bit word (`NumPreRead`,
  `NumWordRead` and the block table's contents give it);
* `mma_next_ne_none`: the bytes of the read of `num_iters` rebuild, and the word kept from it reads
  as bits (`NumWordRead` gives both);
* `dstart_next_ne_none`: the bytes of the read of the Tensor Memory base word rebuild
  (`BaseWordRead` gives it);
* `epi_next_ne_none`: `setpOk` (and, for `num_iters >= 1`, `rcpOk`) at the `o_final` poll,
  the received word is the warp index at the broadcast, and `loadOk` after the 64-word load.

Not done: the worker (`ld0`, `ldRole` reads; no shape theorem for `shfl`, `ldRole`), the
prologue (`ProA.next`: kinds `rd` and `elect` at about 100 sites; `unfold ProA.next` exceeds the
default heartbeats) and the softmax region (`Sm*`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The loader's `next` never rejects the event of its shape**, if its reads return the bytes of
32-bit words (`hrb`: a read whose bytes do not rebuild, and a block-table word without bits, are
the value-dependent `none`) and its two loaded counter words read as bits at the compare after
`bar.sync 1` (`hrg`: `Loader.Rng`). -/
theorem loader_next_ne_none {d : Loader.D} {e : Event} (hsh : EvW.LdShape Q L g d e)
    (hrb : ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ x, bs = (b32 x).toBytes.map some)
    (hrg : Loader.Rng d) :
    Loader.next L g d e ≠ none := by
  unfold EvW.LdShape at hsh
  unfold Loader.next
  cases hst : d.site <;> rw [hst] at hsh <;> dsimp only
  case bar0 =>
    rw [hrg.wi (by rw [hst]; rfl), hrg.wn (by rw [hst]; rfl)]
    simp
  all_goals dsimp only at hsh
  all_goals
    first
      | (simp; done)
      | (rcases hsh with ⟨ac, bs, rfl, -⟩; dsimp only
         obtain ⟨x, rfl⟩ := hrb _ ac bs rfl
         rw [rebuild_b32]
         dsimp only
         try rw [Raw.word32Of_b32]
         simp)
      | (rcases hsh with ⟨ok, rfl⟩; dsimp only; simp)
      | (rcases hsh with ⟨inst, ld, rfl⟩; dsimp only; simp)

/-- **The MMA warp's `next` never rejects the event of its shape**, if the bytes of its read of
`num_iters` rebuild (`hrb`), at `barrier.sync 1`, the word kept from that read reads as bits
(`hwd`), and a broadcast's received word reads as 7 (`hB`): the value-dependent `none`. -/
theorem mma_next_ne_none {d : Mma.D} {e : Event} (hsh : EvW.MmShape L g d e)
    (hrb : d.site = .ldNum → ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    (hwd : d.site = .bar0 → Raw.word32Of (Mma.numWord d) ≠ none) (hB : Mma.BcastOk e) :
    Mma.next L g d e ≠ none := by
  unfold EvW.MmShape at hsh
  unfold Mma.next
  simp only [← Mma.numWord_def]
  cases hst : d.site <;> rw [hst] at hsh hrb hwd <;> dsimp only at hsh hrb hwd ⊢
  all_goals
    first
      | (simp; done)
      | (cases hq : Raw.word32Of (Mma.numWord d)
         · exact absurd hq (hwd rfl)
         · simp)
      | (rcases hsh with ⟨ac, bs, rfl, -⟩
         obtain ⟨v, hv⟩ := hrb rfl _ ac bs rfl
         dsimp only
         rw [hv]
         simp)
      | (rcases hsh with ⟨ok, rfl⟩; dsimp only; simp)
      | (rcases hsh with ⟨recv, ok, rfl⟩; dsimp only
         first | (rw [hB _ _ _ _ _ _ rfl]; simp) | (split <;> simp))

/-- **The common start's `next` never rejects the event of its shape**, if the bytes of its read of
the Tensor Memory base word rebuild. -/
theorem dstart_next_ne_none {d : DStart.D} {e : Event} (hsh : DStart.Shape L g d e)
    (hrb : d.site = .ld0 → ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ v, rebuild 3 bs = .ok v) :
    DStart.next L g d e ≠ none := by
  obtain ⟨s, tm⟩ := d
  unfold DStart.Shape at hsh
  unfold DStart.next
  cases s <;> dsimp only at hsh hrb ⊢
  all_goals
    first
      | (simp; done)
      | (rcases hsh with ⟨ac, bs, rfl, -⟩
         obtain ⟨v, hv⟩ := hrb rfl _ ac bs rfl
         dsimp only
         rw [hv]
         simp)
      | (rcases hsh with ⟨recv, ok, rfl⟩; dsimp only; cases recv <;> simp)

/-- **The epilogue's `next` never rejects the event of its shape** at a site that has one, if the
zero test of the row sum is defined (`setpOk`), the reciprocal is defined (`rcpOk`, needed only
for `num_iters >= 1`) and the 64 words rebuild (`loadOk`). -/
theorem epi_next_ne_none {d : Epi.D} {e : Event} (hsh : Epi.Shape L g d e)
    (hrcp : d.site = .wait → d.pr.setpOk = true ∧ (d.sk = false → d.pr.rcpOk = true))
    (hld : d.site = .waitLd → d.loadOk = true)
    (hbc : d.site = .shfl → ∀ pc m av b c recv ok, e = ⟨pc, .shfl m av b c recv ok⟩ →
      recv = b32 d.pr.w)
    (hw4 : d.pr.w < 4) :
    Epi.next d e ≠ none := by
  obtain ⟨site, pr, o, sk⟩ := d
  have hw4' : pr.w < 4 := hw4
  unfold Epi.Shape at hsh
  unfold Epi.next
  cases site <;> dsimp only at hsh hrcp hld ⊢
  all_goals
    first
      | (simp; done)
      | (rcases hsh with ⟨ok, rfl⟩
         dsimp only
         cases ok
         · simp
         · obtain ⟨h1, h2⟩ := hrcp rfl
           cases hsk : sk
           · simp [h1, h2 hsk]
           · simp [h1])
      | (rcases hsh with ⟨recv, ok, rfl⟩
         dsimp only
         rw [hbc rfl _ _ _ _ _ _ _ rfl]
         simp [Raw.laneOk, Raw.word32Of_b32, hw4'])
      | (rcases hsh with ⟨recv, ok, rfl⟩; dsimp only; split <;> simp)
      | (simp [hld rfl])

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
