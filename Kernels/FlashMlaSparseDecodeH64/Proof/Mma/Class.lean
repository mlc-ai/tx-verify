-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The MMA warp's events by pc class

An event of a state of the role (no hand-back, no undefined behaviour, at a pc of the role's code)
before undefined behaviour is a poll at one of the four wait sites, on its named object
(`Objs.lean`): `bar_q_tma` and `bar_q_utccp` with parity 0 at pcs 1931 and 1983, the block's stage
of `dequantReady` and `soReady` at pcs 2012 and 2107; or neither a poll nor an exit (`ev_class`).
The code at a wait site is an acquiring poll (`wait_op`). -/

/-! # The MMA warp's polls by state

A state's event (but a hand-back's) is a poll only at the four wait sites (`evK_wait_site`),
and two polls of one state name the same object with the same parity (`evK_wait_det`): the
progress row of the role (`Common/Export.lean`) reads the blocker of a waiting lane from its next
event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- **A poll is fired only at a wait site.** -/
theorem evK_wait_site {d : D} {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (hl : ∀ s, d.site ≠ .leave s) (h : EvK L g d e) (hk : e.kind = .wait l q ok a sc) :
    d.site = .qWait ∨ d.site = .qCopyWait ∨ d.site = .kvWait ∨ d.site = .soWait := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at h hl ⊢

/-- **Two polls of one state name one object with one parity.** -/
theorem evK_wait_det {d : D} {e e' : Event} {l l' : Loc} {q q' : Nat} {ok ok' a a' : Bool}
    {sc sc' : MbarScope} (hl : ∀ s, d.site ≠ .leave s) (h : EvK L g d e) (h' : EvK L g d e')
    (hk : e.kind = .wait l q ok a sc) (hk' : e'.kind = .wait l' q' ok' a' sc') :
    l' = l ∧ q' = q := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk'
  subst hk hk'
  cases site <;> simp [EvK, PollEv, CommitEv, MmaEv] at h h' hl ⊢ <;>
    exact ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {e : Event}

/-- The stage of a block. -/
def stage (r : Nat) : Fin 2 := ⟨r % 2, Nat.mod_lt _ (by decide)⟩

/-- The pc classes of the role's events. -/
def PcClass (L : Launch) (g : Nat) (e : Event) : Prop :=
  (e.pc = 1931 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qTma) 0 ok true .cta) ∨
    (e.pc = 1983 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
    (e.pc = 2012 ∧ ∃ b q ok,
      e.kind = .wait (MbarRow.loc L g (.dequantReady b)) q ok true .cta) ∨
    (e.pc = 2107 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.soReady b)) q ok true .cta) ∨
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit)

/-- An event that neither polls nor exits is in the last class. -/
theorem pcClass_other {pc : Nat} {kd k' : Kind} (h : kd = k')
    (h1 : ∀ l q ok a sc, k' ≠ .wait l q ok a sc := by simp) (h2 : k' ≠ .exit := by simp) :
    PcClass L g ⟨pc, kd⟩ :=
  .inr (.inr (.inr (.inr ⟨h ▸ h1, h ▸ h2⟩)))

/-- **The event of an MMA state by its pc class.** -/
theorem ev_class (hp : Pre P L m) {d : D} {n : Cnt → Nat} (hR : Ref L g d n) (hu : n .ub = 0)
    (hl : ∀ s, d.site ≠ .leave s) (hev : Ev L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : e.pc ≤ 2160) : PcClass L g e := by
  obtain ⟨hpc, hk⟩ := hev
  have hc := hR hu
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  unfold PcClass
  subst hpc
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site with
  | qWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inl ⟨rfl, ok, hk.trans (by rw [qTma_loc hp]; rfl)⟩
    · exact absurd hk (hub f)
  | qCopyWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inr (.inl ⟨rfl, ok, hk.trans (by rw [qUt_loc hp]; rfl)⟩)
    · exact absurd hk (hub f)
  | kvWait =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (core_loop rfl).mp hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · refine .inr (.inr (.inl
        ⟨rfl, stage cnt.toNat, (truncBits 32 (parW par)).toNat % 2, ok, ?_⟩))
      refine hk.trans ?_
      simp only at hpha
      rw [hpha, ← ready_loc hp]
      rfl
    · exact absurd hk (hub f)
  | soWait =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (core_loop rfl).mp hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · refine .inr (.inr (.inr (.inl
        ⟨rfl, stage cnt.toNat, (truncBits 32 (parW par)).toNat % 2, ok, ?_⟩)))
      refine hk.trans ?_
      simp only at hpha
      rw [hpha, ← so_loc hp]
      rfl
    · exact absurd hk (hub f)
  | exit => simp [Site.pc] at hpc0
  | leave s => exact absurd rfl (hl s)
  | trap => obtain ⟨f, hk⟩ := hk; exact absurd hk (hub f)
  | elect =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | loadTopk | loadExtra =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | qLoad =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | qCopy =>
    rcases hk with ⟨_, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | qk | pv =>
    rcases hk with ⟨_, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | qCopyCommit | qkCommit | pvCommit =>
    rcases hk with ⟨_, hk, -⟩ | ⟨f, hk⟩
    · exact pcClass_other hk
    · exact absurd hk (hub f)
  | _ => exact pcClass_other hk

/-- **The code at a wait site is an acquiring poll.** -/
theorem wait_op {d : D}
    (hw : d.site = .qWait ∨ d.site = .qCopyWait ∨ d.site = .kvWait ∨ d.site = .soWait) :
    ∀ ins, kernel.code[d.site.pc]? = some ins → Sched.waitOp ins.op = true := by
  intro ins hc
  rcases hw with h | h | h | h <;> rw [h] at hc <;> simp only [Site.pc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
