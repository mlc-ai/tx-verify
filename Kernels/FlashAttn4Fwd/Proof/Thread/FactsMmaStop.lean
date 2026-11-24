-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase

@[expose] public section

/-! # Where the MMA warp's machine stops

The MMA warp's part of `Cross.NextStopsAtExitOrBadRead` (`Cross.NextStops_mma`). An event at a
followed MMA state fires from its site's instruction (`Frame.fired_site`):

* an event that ends the thread is the exit, since no MMA site has an undefined-behaviour
  template (`Mma.tmpl_ok`);
* a continuing event is of its site's kind, so `Mma.next` rejects it only at the read-back,
  when its bytes rebuild to nothing, or at the hand-off poll, when the carried address has no
  bit pattern (`Mma.next_none_site`). The first is a read the machine does not follow; for the
  second, the carried address is the value the read-back's bytes rebuild to
  (`Mma.Counts.baseRead`), so that read is one. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 1000000 in
/-- **The successor function rejects a continuing event** only at the read-back, when its
bytes rebuild to nothing, or at the hand-off poll, when the carried address has no bit
pattern. -/
theorem next_none_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState}
    {ins : Instr} {e : Event} (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u))
    (hn : next L g d e = none) :
    (d.site = .ldBase ∧ ∃ a bs, e.kind = .rd a bs ∧ ∀ v, rebuild 3 bs ≠ .ok v) ∨
      (d.site = .waitDealloc ∧ d.base.regBits = none) := by
  have hev := site_event hpre hg h hc hf
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site with
  | qWait k =>
    obtain ⟨ok, acq, sc, hk⟩ := hev
    simp only [next, hk] at hn
    split_ifs at hn
  | kvWait k =>
    obtain ⟨ok, acq, sc, hk⟩ := hev
    simp only [next, hk] at hn
    split_ifs at hn
  | pWait k =>
    obtain ⟨ok, acq, sc, hk⟩ := hev
    simp only [next, hk] at hn
    split_ifs at hn
  | p2Wait k lead =>
    obtain ⟨ok, acq, sc, hk⟩ := hev
    simp only [next, hk] at hn
    split_ifs at hn
  | waitDealloc =>
    obtain ⟨ok, acq, sc, hk⟩ := hev
    simp only [next, hk] at hn
    split_ifs at hn with hok hb
    exact .inr ⟨rfl, Option.not_isSome_iff_eq_none.mp hb⟩
  | ldBase =>
    code_at hc
    subst hc
    obtain ⟨a, bs, rfl, -⟩ := fires_load rfl rfl hf
    refine .inl ⟨rfl, a, bs, rfl, fun v hv => ?_⟩
    simp [next, hv] at hn
  | shflQ =>
    code_at hc
    subst hc
    obtain ⟨av, bv, cv, recv, ok, rfl, -⟩ := fires_shfl (p := none) hf
    simp only [next] at hn
    split_ifs at hn
  | shfl k =>
    fin_cases k <;> code_at hc <;> subst hc <;>
      obtain ⟨av, bv, cv, recv, ok, rfl, -⟩ := fires_shfl (p := none) hf <;>
      simp only [next] at hn <;> split_ifs at hn
  | elM b =>
    fin_cases b <;> code_at hc <;> subst hc <;>
      obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf <;> simp [next] at hn
  | elC c =>
    fin_cases c <;> code_at hc <;> subst hc <;>
      obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf <;> simp only [next] at hn <;>
      split_ifs at hn
  | exit =>
    code_at hc
    subst hc
    simp [eventTmpl, Fires] at hf
  | _ => first | (simp only [next] at hn; simp at hn) | (simp only [next] at hn; split_ifs at hn)

end Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The MMA warp's part of `Cross.NextStopsAtExitOrBadRead`.** -/
theorem Cross.NextStops_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    ∀ {g i : Nat} {d : Mma.D} {e : Event}, g < L.threads →
      St L X g i = some (some (.inr (.mma d))) → X.get (g, i) = some e →
      (code L g).next (.inr (.mma d)) e = none →
      (∃ pc, e = ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j := by
  intro g i d e hg hσ he hn
  have hσ' : Frame.stateAt (code L) X g i = some (some (.inr (.mma d))) := hσ
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ'
  have hn' : Mma.next L g d e = none := by
    simpa [code, Option.map_eq_none_iff] using hn
  have hw : warpOf L g = 12 := Cross.role_of_state hpre hX hg hσ'
  cases o with
  | none =>
    rcases fires_none_ends hf with ⟨f, hk⟩ | hk
    · obtain ⟨pc, k⟩ := e
      simp only at hk
      subst hk
      exact absurd (fires_ub hf rfl) (Mma.tmpl_ok hpre hg hat.2.1 hat.2.2.2.2 hinv.2 hc f)
    · exact .inl ⟨e.pc, by rw [← hk]⟩
  | some u =>
    rcases Mma.next_none_site hpre hg hat.2.2.2.2 hc hf hn' with
      ⟨hs, a, bs, hk, hbs⟩ | ⟨hs, hb⟩
    · have hs0 : t.sub = 0 := by
        rw [hat.2.1]
        show Mma.Site.sub d.site = 0
        rw [hs]
        rfl
      have hloc := Mma.ldBase_site hpre hs hs0 hat.2.2.2.2 hc hf
      obtain ⟨a', bs', hk', hl, hsz⟩ := hloc
      rw [hk] at hk'
      obtain ⟨rfl, rfl⟩ := Kind.rd.inj hk'
      refine .inr ⟨i, le_refl i, .inr (.inr (.inl ⟨e.pc, a, bs, ?_, hw, hl, hsz,
        fun v hv => absurd hv (hbs v)⟩))⟩
      rw [he, ← hk]
    · have hi : i < (X.tr g).length := by
        by_contra hc'
        have he' : (X.tr g)[i]? = some e := he
        rw [List.getElem?_eq_none (by omega)] at he'
        cases he'
      have hJ : Mma.Counts L g d ((X.tr g).take i) :=
        RunInv.holds hpre hX hg (roleJ_run hpre hg) hi hσ'
      obtain ⟨x, hx, a, bs, hk, hl, hsz, hr⟩ := hJ.baseRead (by rw [hs]; decide)
      obtain ⟨j, hj, hxj⟩ := mem_take_get hx
      refine .inr ⟨j, by omega, .inr (.inr (.inl ⟨x.pc, a, bs, ?_, hw, hl, hsz,
        fun v hv => ?_⟩))⟩
      · rw [hxj, ← hk]
      · rw [hr] at hv
        obtain rfl := Except.ok.inj hv
        exact hb

end
end PTX.Kernels.FlashAttn4Fwd.Proof
