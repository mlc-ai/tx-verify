-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowFeed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefNextLoop

@[expose] public section

/-! # The following theorem of one execution

`follow_at`: the thread machine follows every launched thread of a consistent execution
(`Follow`), by the library's induction (`Frame.followedOn` along `Frame.lexOrder` of the warp
collectives up to an event, `Frame.inductive_lex`) with the invariant `JF` (`jf_init`) and one
good step per fragment: the startup (`startup_step`), warpgroup 1's head (`head_step`), the MMA
warp (`mma_step`), the idle code (`idle_step`), the TMA and index warps (`tma_step`,
`index_step`) and warpgroups 0 and 2 (`wg0_step`, `dequant_step`). No machine stops at a
followed event: warpgroup 0 (`wg0_live`), warpgroup 2 (`deq_live`), the index warp (`ix_live`),
the TMA warp (`tma_live`: its coordinate reads continue on any payload).

It has no premise beyond `Pre` and `Consistent`: the startup follows every value the read-back at
pc 92 returns (a zero word to the relinquishment, any other word to the `trap`, a value without
a word to the comparison's fault). The launch-level form is `Common/Export/Followed.lean`'s
`follow_of`. -/

/-! # The following, step by step: warpgroups 0 and 2

A step of warpgroup 0 (`wg0_step`) or warpgroup 2 (`dequant_step`) keeps `JF`: the slot's
invariant by `Wg0.ref_step` / `Dequant.ref_step` (void after an undefined behaviour: the guard
counts it), given that the machine does not stop at the event. Warpgroup 0 does not stop
(`wg0_live`): its length loads read the launch's words (`Wg0.lenOk`, `Wg0.succ_live`); nor
does warpgroup 2 (`deq_live`, `Common/DequantWords.lean`). Their first states have the
invariant at the hand-off (`frag_init`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {X : Execution}

/-- **A step of warpgroup 0 or 2 is good**, from the slot's invariant at the successor. -/
theorem wg_good {i : Entry} {d : (frag P L g i).D} {n : Cls → Nat} {e : Event}
    (hfr : ∀ d' n', fresh (P := P) (L := L) (g := g) (.inr ⟨.inl i, d'⟩, n'))
    (hns : (frag P L g i).next d e ≠ some none)
    (hstay : ∀ d', (frag P L g i).next d e = some (some d') →
      fragJ P L g i d' (Code.bump cls n e)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl i, d⟩, n) e := by
  unfold Frame.StepGood
  rw [next_frag]
  rcases hs : (frag P L g i).next d e with _ | _ | d'
  · simp
  · exact absurd hs hns
  refine ⟨by simp, fun σ' h' => ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h'
  subst h'
  exact ⟨hstay d' hs, hfr d' _⟩

/-- **Warpgroup 0's length loads read the launch's words** at a followed state. -/
theorem wg0_live (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : (frag P L g .wg0).D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg0, d⟩, n)) : Wg0.LenOk P L g d e := by
  obtain ⟨⟨-, ⟨hR, -⟩, -, -⟩, -⟩ := id hJ
  have hloc : n (.wg0 .ub) = 0 := (state_count hσ _).trans (wg0_take_noUb hX he)
  obtain ⟨-, hl, -⟩ := hR (state_ub hX hσ he) hloc
  refine Wg0.lenOk (w := warpW L g) hp hX he hl fun hu => ?_
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    Frame.fired_siteU (fun _ _ => thread_sound hp) hX he hσ hu
  exact ⟨t, ins, o, hat, hinv, hc, hf⟩

/-- **A step of warpgroup 0 is good.** -/
theorem wg0_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : (frag P L g .wg0).D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg0, d⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg0, d⟩, n) e := by
  obtain ⟨⟨hb, ⟨hR, hT⟩, h2, hwg⟩, -⟩ := id hJ
  have hok := wg0_live hp hX he hσ hJ
  refine wg_good (fun _ _ => trivial) (Wg0.succ_live hok) fun d' hn => ?_
  refine ⟨Nat.le_trans hb (bump_ge n e .bar0), ⟨fun h0 => ?_, fun h0 => ?_⟩,
    Nat.le_trans h2 (bump_ge n e .shfl), hwg⟩
  · have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
    exact Wg0.ref_step hp (hR (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hok hn
  · have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
    exact Wg0.tmemAt_step (hT (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hn
      (not_ub_of_bump h0)

/-- **A step of warpgroup 2 is good**: its machine does not stop at the event (`deq_live`). -/
theorem dequant_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : (frag P L g .dequant).D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .dequant, d⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .dequant, d⟩, n)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .dequant, d⟩, n) e := by
  obtain ⟨⟨hb, hR, h2, hwg⟩, -⟩ := id hJ
  refine wg_good (fun _ _ => trivial) (deq_live hp hX he hσ) fun d' hn => ?_
  refine ⟨Nat.le_trans hb (bump_ge n e .bar0), fun h0 => ?_, Nat.le_trans h2 (bump_ge n e .shfl),
    hwg⟩
  have hev := ev_of_state hp hX he hσ hJ.1 (not_ub_of_bump h0)
  exact Dequant.ref_step hp (hR (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))) hev hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {X : Execution}

/-- **Every step from a followed state with `JF` is good**, once no earlier event is bad. -/
theorem step_good (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread P L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hJ : JF P L g σ)
    (hprev : Prev P L X (g, k)) : Frame.StepGood (thread P L) (JF P L) g σ e := by
  rcases σ with ⟨d | ⟨i | r, d⟩, n⟩
  · exact startup_step hp hX he hσ hJ hprev
  · cases i with
    | wg0 => exact wg0_step hp hX he hσ hJ
    | dequant => exact dequant_step hp hX he hσ hJ
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · exact head_step hp hX he hσ hJ hprev
      · cases j with
        | mma => exact mma_step hp hX he hσ hJ
        | idle => exact idle_step hJ
        | tma => exact tma_step hp hX he hσ hJ
        | index => exact index_step hp hX he hσ hJ
      · obtain ⟨⟨-, hW, -⟩, -⟩ := hJ
        exact hW.elim
  · obtain ⟨hW, -⟩ := hJ
    exact hW.elim

/-- **The thread machine follows every launched thread.** -/
theorem follow_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) :
    Follow P L X := by
  refine follow_iff.mpr fun g hg k => ?_
  obtain ⟨h1, h2⟩ := Frame.followedOn (C := thread P L) (J := JF P L)
    (Q := fun g => g < L.threads) (Frame.inductive_lex (Frame.collUpTo X)) (fun _ _ => jf_init)
    (fun g _ _ _ hg he hσ hJ hprev => step_good hp hX he hσ hJ hprev) hg k
  exact ⟨h1, fun d hd => (h2 d hd).1⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
