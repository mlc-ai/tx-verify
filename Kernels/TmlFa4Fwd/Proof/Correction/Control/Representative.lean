-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.RefStep
import Kernels.TmlFa4Fwd.Proof.Correction.RefNext
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event} {n : Cnt → Nat}

/-- Sites at which changing a payload preserves the protocol step. -/
def payloadSite (s : Site) : Prop :=
  (∃ st, s = .rscale st ∨ s = .fsum st ∨ s = .fmax st ∨ s = .rvote st) ∨
    (∃ st c, s = .rld st c) ∨ ∃ st j, s = .fld st j

set_option hygiene false in
local macro "event_effect " h:term : tactic =>
  `(tactic| (rw [show e = ⟨e.pc,_⟩ from congrArg (Event.mk e.pc) $h]; rfl))

/-- A data-machine step representing a defined control step. Its input may differ only at
a data instruction, preserving event counts and the scheduler collectives. -/
def Represents (p : Params) (L : Launch) (g : Nat) (d d' : D) (e : Event) : Prop :=
  ∃ (a : Correction.D) (ev : Event), Correction.Ev p L g d.scheduler ev ∧
    (∀ f, ev.kind ≠ .ub f) ∧ Correction.succ p L g d.scheduler ev = some (some a) ∧
    a.site = d'.site ∧ (erase a).v = d'.v ∧ a.k = d'.k ∧
    (∀ c, cls L g c ev = cls L g c e) ∧
    (ev = e ∨ (payloadSite d.site ∧
      ev.counts = e.counts ∧ Execution.isShfl ev = Execution.isShfl e ∧
      isFullVote ev = isFullVote e))

private theorem transport {a : Correction.D} {e' : Event} (_hJ : Ref p L g (d,n))
    (he : Correction.Ev p L g d.scheduler e') (hu : ∀ f, e'.kind ≠ .ub f)
    (hs : Correction.succ p L g d.scheduler e' = some (some a)) (hd : erase a = d')
    (hb : ∀ c, cls L g c e' = cls L g c e)
    (hm : e' = e ∨ (payloadSite d.site ∧
      e'.counts = e.counts ∧ Execution.isShfl e' = Execution.isShfl e ∧
      isFullVote e' = isFullVote e)) :
    Represents p L g d d' e :=
  ⟨a,e',he,hu,hs,congrArg D.site hd,congrArg D.v hd,congrArg D.k hd,hb,hm⟩

private def sampleBytes := (fv 0).toBytes.map some
private theorem sample_rd : rebuild 3 sampleBytes = .ok (fv 0) :=
  PTX.Proof.rebuild_scalar (by decide) rfl

private theorem sample_ld (sz : Nat) : ∃ f, flN sz (List.replicate sz (fv 0)) = some f := by
  have h : (List.range sz).all (fun i =>
      (fl32 ((List.replicate sz (fv 0)).getD i (.pred false))).isSome) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have hlt := List.mem_range.mp hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hlt, ↓reduceIte,
      Option.getD_some]
    rfl
  unfold flN
  rw [ite_eq_left h]
  exact ⟨_, rfl⟩

set_option hygiene false in
local macro "stat_ref " dst:term:max " using " set:term:max : tactic =>
  `(tactic| (
    simp only [succ] at hn
    split at hn
    · rename_i a bs hkind
      cases hn
      refine transport (a := ⟨$dst, $set v.scheduler 0 st, 0⟩) hJ
        (e' := ⟨e.pc,.rd a sampleBytes⟩) (.inl ⟨_,_,rfl⟩)
        (fun f h => by cases h) ?_ ?_ (fun c => by cases c <;> simp only [cls,hkind])
        (.inr ⟨.inl ⟨st, by simp⟩, by event_effect hkind, by event_effect hkind, by event_effect
            hkind⟩)
      · simp only [D.scheduler, Correction.succ, sample_rd, real32, scale32, max32_fv, fv] <;> rfl
      · fin_cases st <;> rfl
    · cases hn))

theorem represents (hJ : Ref p L g (d,n)) (he : Ev p L g d e) (hu : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g d e = some (some d')) : Represents p L g d d' e := by
  have direct (hev : Correction.Ev p L g d.scheduler e)
      (hs : (Correction.succ p L g d.scheduler e).map (Option.map erase) = some (some d')) :
      Represents p L g d d' e := by
    obtain ⟨x, hx, hm⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨a, rfl, ha⟩ := Option.map_eq_some_iff.mp hm
    exact transport hJ hev hu hx ha (fun _ => rfl) (.inl rfl)
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rscale st => stat_ref (.rvote st) using setS
  | fsum st => stat_ref (.fmax st) using setRs
  | fmax st => stat_ref (.farr st) using setRm
  | rvote st =>
    obtain ⟨pred,b,hk⟩ := he
    let pred' := Assumption.erealCompare .lt ((sOf v.scheduler st).real : EReal) (1 : ℝ)
    let ev : Event := ⟨e.pc, .vote (2^32-1) pred' b⟩
    have h := hn
    simp only [succ, Correction.succ, D.scheduler, hk, Option.map_some, Option.some.injEq] at h
    exact transport hJ (e' := ev) ⟨b,rfl⟩ (fun _ he => by cases he) rfl h
      (fun c => by cases c <;> simp only [cls,hk,ev])
      (.inr ⟨.inl ⟨_, .inr (.inr (.inr rfl))⟩, by event_effect hk, by event_effect hk,
          by event_effect hk⟩)
  | rld st c =>
    obtain ⟨_, _, hQ⟩ := hJ
    have hk : k = 0 := hQ.sub rfl
    subst k
    simp only [succ] at hn
    split at hn
    · rename_i a vals sh heq
      cases hn
      obtain ⟨f,hf⟩ := sample_ld 16
      let ev : Event := ⟨e.pc,.tc (.ld a (List.replicate 16 (fv 0)) sh)⟩
      refine transport (d := ⟨.rld st c,v,0⟩) (a := ⟨.rldw st c,{v.scheduler with xs := f},1⟩)
        ⟨_,_,hQ⟩ (e' := ev) (.inl ⟨_,_,_,rfl⟩) (fun _ h => by cases h)
        ?_ rfl (fun c => by cases c <;> simp only [cls,heq,ev])
        (.inr ⟨.inr (.inl ⟨_,_,rfl⟩), by event_effect heq, by event_effect heq, by event_effect
            heq⟩)
      simp only [D.scheduler, Correction.succ, ev, ↓reduceIte, hf]
    · cases hn
  | fld st j =>
    simp only [succ] at hn
    split at hn
    · rename_i a vals sh heq
      cases hn
      obtain ⟨f,hf⟩ := sample_ld 8
      let ev : Event := ⟨e.pc,.tc (.ld a (List.replicate 8 (fv 0)) sh)⟩
      refine transport (a := ⟨.fwl st j,{v.scheduler with ys := f},0⟩) hJ (e' :=
          ev) (.inl ⟨_,_,_,rfl⟩) (fun _ h => by cases h)
        ?_ rfl (fun c => by cases c <;> simp only [cls,heq,ev])
        (.inr ⟨.inr (.inr ⟨_,_,rfl⟩), by event_effect heq, by event_effect heq, by event_effect
            heq⟩)
      simp only [D.scheduler, Correction.succ, ev, hf]
    · cases hn
  | fdone st i =>
    apply direct he
    fin_cases st <;> fin_cases i
    · exact hn
    · exact hn
    · exact hn
    · change (if 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ) then some (some _) else some none).map _ = _
      rw [ite_eq_left ⟨le_refl _,le_refl _⟩]
      exact hn
  | lse i =>
    apply direct he
    fin_cases i
    · change (if 0 ≤ (0 : ℝ) then some (some _) else some none).map _ = _
      rw [ite_eq_left (le_refl _)]
      exact hn
    · exact hn
  | _ => exact direct he hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
