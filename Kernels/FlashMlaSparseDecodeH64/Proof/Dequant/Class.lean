-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Warpgroup 2's events by pc class

An event of a state of the role (no undefined behaviour, at a pc of the role's code, so not the
exit) is a poll at one of the three wait sites, on its named object (`Objs.lean`): `bar_q_utccp`
with parity 0 at pc 2644, the slot's `rawReady` and `svDone` at pcs 2677 and 2684; named barrier
12 at pc 3610; or neither a poll nor an exit (`ev_class`). No reference invariant is needed: the
shape table names the objects. The code at a wait site is an acquiring poll (`wait_op`). -/

/-! # Warpgroup 2's polls by state

A state's event is a poll only at the three wait sites (`evK_wait_site`: `wq`, `wraw`, `wsv`),
and two polls of one state name the same object with the same parity (`evK_wait_det`): the
progress row of the role (`Common/Export.lean`) reads the blocker of a waiting lane from its next
event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {L : Launch} {g : Nat}

/-- **A poll is fired only at a wait site.** -/
theorem evK_wait_site {d : D} {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (h : EvK L g d e) (hk : e.kind = .wait l q ok a sc) :
    d.site = .wq ∨ d.site = .wraw ∨ d.site = .wsv := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site <;> simp [EvK, PollEv, LoadEv, StoreEv] at h ⊢

/-- **Two polls of one state name one object with one parity.** -/
theorem evK_wait_det {d : D} {e e' : Event} {l l' : Loc} {q q' : Nat} {ok ok' a a' : Bool}
    {sc sc' : MbarScope} (h : EvK L g d e) (h' : EvK L g d e')
    (hk : e.kind = .wait l q ok a sc) (hk' : e'.kind = .wait l' q' ok' a' sc') :
    l' = l ∧ q' = q := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk'
  subst hk hk'
  cases site <;> simp [EvK, PollEv, LoadEv, StoreEv] at h h' ⊢ <;>
    exact ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {e : Event}

/-- The pc classes of the role's events. -/
def PcClass (L : Launch) (g : Nat) (e : Event) : Prop :=
  (e.pc = 2644 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
    (e.pc = 2677 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.rawReady b)) q ok true .cta) ∨
    (e.pc = 2684 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.svDone b)) q ok true .cta) ∨
    (e.pc = 3610 ∧ e.kind = .bar 12 none .sync) ∨
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit)

/-- An event that neither polls nor exits is in the last class. -/
theorem pcClass_other {pc : Nat} {kd k' : Kind} (h : kd = k')
    (h1 : ∀ l q ok a sc, k' ≠ .wait l q ok a sc := by simp) (h2 : k' ≠ .exit := by simp) :
    PcClass L g ⟨pc, kd⟩ :=
  .inr (.inr (.inr (.inr ⟨h ▸ h1, h ▸ h2⟩)))

/-- **The event of a warpgroup-2 state by its pc class.** -/
theorem ev_class (hp : Pre P L m) {d : D} (hev : Ev L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : e.pc ≤ 3610) : PcClass L g e := by
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | wq =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inl ⟨rfl, ok, hk.trans (by rw [q_loc hp]; rfl)⟩
    · exact absurd hk (hub f)
  | wraw =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inr (.inl ⟨rfl, slotF sb, _, ok, hk.trans (by rw [raw_loc hp])⟩)
    · exact absurd hk (hub f)
  | wsv =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inr (.inr (.inl ⟨rfl, slotF sb, _, ok, hk.trans (by rw [sv_loc hp])⟩))
    · exact absurd hk (hub f)
  | bar => exact .inr (.inr (.inr (.inl ⟨rfl, hk⟩)))
  | exit => simp [Site.pc] at hpc0
  | smr => obtain ⟨_, hk⟩ := hk; exact pcClass_other hk
  | lenA | lenB =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | scale _ | raw _ _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | store _ _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | fpx | arrD | arrF => exact pcClass_other hk

/-- **The code at a wait site is an acquiring poll.** -/
theorem wait_op {d : D} (hw : d.site = .wq ∨ d.site = .wraw ∨ d.site = .wsv) :
    ∀ ins, kernel.code[d.site.pc]? = some ins → Sched.waitOp ins.op = true := by
  intro ins hc
  rcases hw with h | h | h <;> rw [h] at hc <;> simp only [Site.pc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
