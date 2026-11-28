-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # The TMA warp's events by pc class

An event of a state of the role (no hand-back, no undefined behaviour, at a pc of the role's code)
before undefined behaviour is a poll at one of the four wait sites, on its named object
(`Objs.lean`): `bar_q_utccp` and `bar_last_store_done` with parity 0 at pcs 2205 and 2209, a slot
of `coordReady` and of `rawFree` at pcs 2234 and 2245; or neither a poll nor an exit
(`ev_class`). The code at a wait site is an acquiring poll (`wait_op`). -/

/-! # The TMA warp's polls by state

A state's event (but a hand-back's) is a poll only at the four wait sites (`evK_wait_site`), and
two polls of one state name the same object with the same parity (`evK_wait_det`): the progress
row of the role (`Common/Export.lean`) reads the blocker of a waiting lane from its next event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- **A poll is fired only at a wait site.** -/
theorem evK_wait_site {d : D} {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (hl : ∀ s, d.site ≠ .leave s) (h : EvK L g d e) (hk : e.kind = .wait l q ok a sc) :
    d.site = .qWait ∨ d.site = .storeWait ∨ d.site = .coordWait ∨ d.site = .rawWait := by
  tma_state d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases s <;> simp [EvK, Poll, RdAt] at h hl ⊢

/-- **Two polls of one state name one object with one parity.** -/
theorem evK_wait_det {d : D} {e e' : Event} {l l' : Loc} {q q' : Nat} {ok ok' a a' : Bool}
    {sc sc' : MbarScope} (hl : ∀ s, d.site ≠ .leave s) (h : EvK L g d e) (h' : EvK L g d e')
    (hk : e.kind = .wait l q ok a sc) (hk' : e'.kind = .wait l' q' ok' a' sc') :
    l' = l ∧ q' = q := by
  tma_state d
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk'
  subst hk hk'
  cases s <;> simp [EvK, Poll, RdAt] at h h' hl ⊢ <;>
    exact ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {e : Event}

/-- The pc classes of the role's events. -/
def PcClass (L : Launch) (g : Nat) (e : Event) : Prop :=
  (e.pc = 2205 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .qUtccp) 0 ok true .cta) ∨
    (e.pc = 2209 ∧ ∃ ok, e.kind = .wait (MbarRow.loc L g .lastStoreDone) 0 ok true .cta) ∨
    (e.pc = 2234 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.coordReady b)) q ok true .cta) ∨
    (e.pc = 2245 ∧ ∃ b q ok, e.kind = .wait (MbarRow.loc L g (.rawFree b)) q ok true .cta) ∨
    ((∀ l q ok a sc, e.kind ≠ .wait l q ok a sc) ∧ e.kind ≠ .exit)

/-- An event that neither polls nor exits is in the last class. -/
theorem tPcClass_other {pc : Nat} {kd k' : Kind} (h : kd = k')
    (h1 : ∀ l q ok a sc, k' ≠ .wait l q ok a sc := by simp) (h2 : k' ≠ .exit := by simp) :
    PcClass L g ⟨pc, kd⟩ :=
  .inr (.inr (.inr (.inr ⟨h ▸ h1, h ▸ h2⟩)))

/-- **The event of a TMA state by its pc class.** -/
theorem ev_class (hp : Pre P L m) {d : D} {n : Cnt → Nat} (hR : Ref L g d n) (hu : n .ub = 0)
    (hl : ∀ s, d.site ≠ .leave s) (hev : Ev L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc0 : e.pc < 2332) : PcClass L g e := by
  obtain ⟨hpc, hk⟩ := hev
  have hc := hR hu
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  tma_state d
  cases s with
  | qWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inl ⟨rfl, ok, hk.trans (by rw [qUtW_loc hp]; rfl)⟩
    · exact absurd hk (hub f)
  | storeWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · exact .inr (.inl ⟨rfl, ok, hk.trans (by rw [lastW_loc hp]; rfl)⟩)
    · exact absurd hk (hub f)
  | coordWait =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -, -, -⟩, -⟩ := (core_loop rfl).mp hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · refine .inr (.inr (.inl ⟨rfl, MbarRow.slot4 cnt.toNat,
        (truncBits 32
          (prW ⟨.coordWait, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩)).toNat % 2, ok,
        hk.trans ?_⟩))
      rw [ready_of hslot, ← ready_loc hp (MbarRow.slot4 cnt.toNat)]
      rfl
    · exact absurd hk (hub f)
  | rawWait =>
    obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, -⟩ := (core_loop rfl).mp hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · refine .inr (.inr (.inr (.inl ⟨rfl, MbarRow.slot2 cnt.toNat,
        (truncBits 32
          (pfW ⟨.rawWait, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩)).toNat % 2, ok,
        hk.trans ?_⟩)))
      rw [free_of hbuf, ← free_loc hp (MbarRow.slot2 cnt.toNat)]
      rfl
    · exact absurd hk (hub f)
  | exit => simp [Site.pc] at hpc0
  | leave s => exact absurd rfl (hl s)
  | elect =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact tPcClass_other hk
    · exact absurd hk (hub f)
  | loadTopk | loadExtra =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · exact tPcClass_other hk
    · exact absurd hk (hub f)
  | coord0 _ | coord1 _ | coord2 _ | coord3 _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact tPcClass_other hk
    · exact absurd hk (hub f)
  | gather _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · exact tPcClass_other hk
    · exact absurd hk (hub f)
  | rawArrive | coordFree | outBar => exact tPcClass_other hk

/-- **The code at a wait site is an acquiring poll.** -/
theorem wait_op {d : D}
    (hw : d.site = .qWait ∨ d.site = .storeWait ∨ d.site = .coordWait ∨ d.site = .rawWait) :
    ∀ ins, kernel.code[d.site.pc]? = some ins → Sched.waitOp ins.op = true := by
  intro ins hc
  rcases hw with h | h | h | h <;> rw [h] at hc <;> simp only [Site.pc] at hc <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
