-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Objs
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # The index warp's events by pc class

An event of a state of the role (no undefined behaviour, at a pc of the role's code) is a poll of
a slot of `valid_coord_free` of the lane's CTA at pc 2446 (main loop) or 2534 (extra loop), named
barrier 12 at pc 2585, or neither a poll nor an exit (`ev_class`). The code at a wait site is an
acquiring poll (`wait_op`). -/

/-! # The index warp's polls by state

A state's event is a poll only at the two waits on `valid_coord_free` (`evK_wait_site`), and two
polls of one state name the same object with the same parity (`evK_wait_det`): the progress row
of the role (`Common/Export.lean`) reads the blocker of a waiting lane from its next event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- **A poll is fired only at a wait site.** -/
theorem evK_wait_site {d : D} {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (h : EvK P L g d e) (hk : e.kind = .wait l q ok a sc) : d.site = .wA ∨ d.site = .wB := by
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  unfold EvK at h
  cases hs : d.site <;> simp [hs, NcEv, NcAt, PollEv, ShflEv, StoreEv] at h ⊢

/-- **Two polls of one state name one object with one parity.** -/
theorem evK_wait_det {d : D} {e e' : Event} {l l' : Loc} {q q' : Nat} {ok ok' a a' : Bool}
    {sc sc' : MbarScope} (h : EvK P L g d e) (h' : EvK P L g d e')
    (hk : e.kind = .wait l q ok a sc) (hk' : e'.kind = .wait l' q' ok' a' sc') :
    l' = l ∧ q' = q := by
  have hw := evK_wait_site h hk
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk'
  subst hk hk'
  unfold EvK at h h'
  rcases hw with hs | hs <;> simp only [hs, PollEv] at h h' <;>
    obtain ⟨_, h⟩ | ⟨_, h⟩ := h <;> obtain ⟨_, h'⟩ | ⟨_, h'⟩ := h' <;>
    simp only [Kind.wait.injEq, reduceCtorEq] at h h' <;>
    exact ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {e : Event}

/-- The pc classes of the role's events. -/
def PcClass (L : Launch) (g : Nat) (e : Event) : Prop :=
  (e.pc = 2446 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.coordFree b)) q ok true .cta) ∨
    (e.pc = 2534 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.coordFree b)) q ok true .cta) ∨
    (e.pc = 2585 ∧ e.kind = .bar 12 none .sync) ∨
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit)

/-- An event that neither polls nor exits is in the last class. -/
theorem iPcClass_other {pc : Nat} {kd k' : Kind} (h : kd = k')
    (h1 : ∀ l q ok a sc, k' ≠ .wait l q ok a sc := by simp) (h2 : k' ≠ .exit := by simp) :
    PcClass L g ⟨pc, kd⟩ :=
  .inr (.inr (.inr ⟨h ▸ h1, h ▸ h2⟩))

/-- **The event of an index state by its pc class.** -/
theorem ev_class (hp : Pre P L m) {d : D} (hev : Ev P L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : e.pc < 2587) : PcClass L g e := by
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  unfold EvK at hk
  cases site with
  | wA | wB =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · first
      | exact .inl ⟨rfl, c.slot, _, ok, hk.trans (by rw [free_loc hp])⟩
      | exact .inr (.inl ⟨rfl, c.slot, _, ok, hk.trans (by rw [free_loc hp])⟩)
    · exact absurd hk (hub f)
  | bar => exact .inr (.inr (.inl ⟨rfl, hk⟩))
  | exit => simp [IxSite.pc] at hpc0
  | arrA | arrB => exact iPcClass_other hk
  | lenA | lenB =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact iPcClass_other hk
    · exact absurd hk (hub f)
  | pre | pf | xpre | xpf =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact iPcClass_other hk
    · exact absurd hk (hub f)
  | sA1 | sA2 | sB1 | sB2 =>
    rcases hk with ⟨_, _, _, _, _, hk⟩ | ⟨f, hk⟩
    · exact iPcClass_other hk
    · exact absurd hk (hub f)
  | stA | stB | bA | bB =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact iPcClass_other hk
    · exact absurd hk (hub f)

/-- **The code at a wait site is an acquiring poll.** -/
theorem wait_op {d : D} (hw : d.site = .wA ∨ d.site = .wB) :
    ∀ ins, kernel.code[d.site.pc]? = some ins → Sched.waitOp ins.op = true := by
  intro ins hc
  rcases hw with h | h <;> rw [h] at hc <;> simp only [IxSite.pc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
