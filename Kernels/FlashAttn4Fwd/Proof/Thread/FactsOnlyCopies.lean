-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccessRoles
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Lemmas.Protocol.Region
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Only tensor copies write the ring regions (`RingFacts.only_copies`)

A memory write is a thread's, a tensor store's, a tensor copy's, a cancellation response's or a
bulk copy's (`MemWrites`). A thread's access lies below offset `68608` (`OlderFacts_access_low`),
where the ring regions start; a tensor store writes global memory (`store_writeLoc_global`); the
kernel issues no cancellation request and no bulk copy (`kernel_no_clc`, `kernel_no_bulk`). So a
write of a ring byte is a tensor copy's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel issues no cancellation request. -/
theorem kernel_no_clc : OpPcsFast kernel.code clcOp [] = true := by
  decide +kernel

/-- An event of a kind no instruction of the kernel fires does not exist. -/
theorem no_event (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {kd : Kind} {p : Op → Bool}
    (he : X.get (g, k) = some ⟨pc, kd⟩) (hub : ∀ f, kd ≠ .ub f)
    (hk : OpPcsFast kernel.code p [] = true)
    (hop : ∀ {A L g t op q o}, Fires q (eventTmpl A L g t op) ⟨pc, kd⟩ o → p op = true) :
    False := by
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he
      (fun pc' f h => hub f (by cases h; rfl))
  exact absurd (OpPcsFast.mem hk hc (hop hf)) List.not_mem_nil

theorem FBar.regionOff_full : ∀ b : FBar, b.isFull = true → 68608 ≤ b.regionOff := by
  decide

/-- **Every memory write of a byte in a ring region is a tensor copy's.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.RingFacts_only_copies (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hlow : LowAccessLow L X) :
    ∀ {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {c : Nat} {b : FBar} {l : Loc},
      X.MemWrites w a bs → a.Covers l → b.isFull → InRegion L c b l →
        ∃ i x y z, w = .async i (.write (.load x y z)) := by
  intro w a bs c b l hw hc hb hr
  obtain ⟨hsp, -, hlo, -⟩ := hr
  have hoff := FBar.regionOff_full b hb
  rcases w with ⟨g, k⟩ | ⟨i, part⟩
  · -- a thread's write lies below the ring regions
    have hA : X.Access (g, k) a true := by
      rcases hw with hw | ⟨old, hw⟩
      · exact .inr (.inl ⟨bs, hw, rfl⟩)
      · exact .inr (.inr ⟨old, _, hw⟩)
    have h := OlderFacts_access_low hpre hX ht hlow hA hc
    omega
  cases part
  case writeLoad x y z => exact ⟨i, x, y, z, rfl⟩
  case writeStore x y z =>
    obtain ⟨o, addr, bb, -, -, hloc, -⟩ := hw
    obtain ⟨hcta, -⟩ := hc
    have hg := Execution.store_writeLoc_global hloc
    exfalso
    have : l.space = a.loc.space := hcta
    rw [this, hg] at hsp
    cases hsp
  case writeCta c' =>
    obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hw
    exact (no_event hpre hX ht he (fun _ h => by cases h) kernel_no_clc
      fun hf => fires_clcIssue_op hf rfl).elim
  case writeCopy =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hw
    exact (no_event hpre hX ht he (fun _ h => by cases h) kernel_no_bulk
      fun hf => fires_bulk_op hf rfl).elim
  case writeElem j =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hw
    exact (no_event hpre hX ht he (fun _ h => by cases h) kernel_no_bulk
      fun hf => fires_bulk_op hf rfl).elim
  all_goals exact hw.elim

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
