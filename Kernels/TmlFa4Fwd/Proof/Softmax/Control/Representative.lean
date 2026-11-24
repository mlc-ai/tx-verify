-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Shape
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow
noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {m : Mem0} {d d' : D} {e : Event} {n : Cnt → Nat}

/-- Sites at which changing a payload preserves the protocol step. -/
def payloadSite (s : Site) : Prop :=
  (∃ r c, s = .sld r c) ∨ ∃ b c, s = .bld b c

set_option hygiene false in
local macro "event_effect " h:term : tactic =>
  `(tactic| (rw [show e = ⟨e.pc,_⟩ from congrArg (Event.mk e.pc) $h]; rfl))

/-- A data-machine step representing a defined control step. Its input may differ only at
a data instruction, preserving event counts and the scheduler collectives. -/
def Represents (p : Params) (L : Launch) (g : Nat) (d d' : D) (e : Event) : Prop :=
  ∃ (a : Softmax.D) (ev : Event), Softmax.Ev p L g d.scheduler ev ∧
    (∀ f, ev.kind ≠ .ub f) ∧ Softmax.succ p L g d.scheduler ev = some (some a) ∧
    a.site = d'.site ∧ (erase a).v = d'.v ∧ a.k = d'.k ∧
    (∀ c, cls L g c ev = cls L g c e) ∧
    (ev = e ∨ (payloadSite d.site ∧
      ev.counts = e.counts ∧ Execution.isShfl ev = Execution.isShfl e ∧
      isFullVote ev = isFullVote e))

private theorem transport (_hp : Pre p L m) (_hJ : Ref p L g (d,n)) {a : Softmax.D} {ev : Event}
    (he : Softmax.Ev p L g d.scheduler ev) (hu : ∀ f, ev.kind ≠ .ub f)
    (hs : Softmax.succ p L g d.scheduler ev = some (some a))
    (hsite : a.site = d'.site) (hv : (erase a).v = d'.v) (hk : a.k = d'.k)
    (hb : ∀ c, cls L g c ev = cls L g c e)
    (hm : ev = e ∨ (payloadSite d.site ∧
      ev.counts = e.counts ∧ Execution.isShfl ev = Execution.isShfl e ∧
      isFullVote ev = isFullVote e)) :
    Represents p L g d d' e :=
  ⟨a,ev,he,hu,hs,hsite,hv,hk,hb,hm⟩

private def masked : Value := .bits 32 0xff80ff80
private def bytes := masked.toBytes.map some
private theorem rebuild_masked : rebuild 3 bytes = .ok masked :=
  PTX.Proof.rebuild_scalar (by decide) rfl

theorem represents (hp : Pre p L m) (hJ : Ref p L g (d,n)) (he : Ev p L g d e)
    (hu : ∀ f, e.kind ≠ .ub f) (hn : succ p L g d e = some (some d')) :
    Represents p L g d d' e := by
  have direct (hs : (Softmax.succ p L g d.scheduler e).map (Option.map erase) = some (some d')) :
      Represents p L g d d' e := by
    obtain ⟨x,hx,hm⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨a,rfl,rfl⟩ := Option.map_eq_some_iff.mp hm
    exact transport hp hJ he hu hx rfl rfl rfl (fun _ => rfl) (.inl rfl)
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | sld r c =>
    simp only [succ] at hn
    split at hn
    · rename_i addr vals sh hkind
      let ev : Event := ⟨e.pc, .tc (.ld addr [] sh)⟩
      have hx : ∃ xs, flAll [] = some xs := flAll_some_of (by simp)
      obtain ⟨xs,hxs⟩ := hx
      have hshape : Softmax.Ev p L g ⟨.sld r c,v.scheduler,k,acc⟩ ev := .inl ⟨_,_,_,rfl⟩
      cases r <;> cases hn <;>
        exact transport hp hJ hshape (fun _ h => by cases h)
          (by simp only [D.scheduler, Softmax.succ, ev, hxs]; rfl) rfl rfl rfl
          (fun c => by cases c <;> simp only [cls,hkind,ev])
          (.inr ⟨.inl ⟨_,_,rfl⟩, by event_effect hkind,
            by event_effect hkind, by event_effect hkind⟩)
    · cases hn
  | bld b c =>
    simp only [succ] at hn
    split at hn
    · rename_i addr bs hkind
      let ev : Event := ⟨e.pc,.rd addr bytes⟩
      have hshape : Softmax.Ev p L g ⟨.bld b c,v.scheduler,k,acc⟩ ev := .inl ⟨_,_,rfl⟩
      have hok : biasOk masked = true := rfl
      split at hn <;> rename_i hsub <;> cases hn <;>
        exact transport hp hJ hshape (fun _ h => by cases h)
          (by simp only [D.scheduler, Softmax.succ, ev, rebuild_masked, hok, hsub, ↓reduceIte]; rfl)
          rfl rfl rfl (fun c => by cases c <;> simp only [cls,hkind,ev])
          (.inr ⟨.inr ⟨_,_,rfl⟩, by event_effect hkind,
            by event_effect hkind, by event_effect hkind⟩)
    · cases hn
  | _ => exact direct hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
