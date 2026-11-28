-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbRole
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictGlue
public import Lemmas.Kernel.StrictSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Steps
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.StepFor
import Lemmas.Flow.RoleStep

@[expose] public section

/-! # An event at a state of warpgroup 1 fires from a strictly good concrete state

`strict_event`: an event fired from a state of the head, the idle code, the MMA warp or the TMA
warp of a followed lane is its site's event, fired from a concrete state that is strictly good
(`Code.Good`), not a fault alternative (`Frame.strict_site`, with `thread_prev`: the step before it
is strict for its event). For a TMA state the step before it from a TMA state is the caller's
(`htma`). The machine dies at the event only where the sub-role's own machine does
(`thread_next_none_sub`, `thread_next_none_head`). -/

/-! # The step before a state of warpgroup 1's head, idle code, MMA or TMA warp is strict

`thread_prev`: when the thread machine's step from `dj` on event `e` reaches a state `σ` of the
head, the idle code, the MMA warp or the TMA warp, the step is strict for that event
(`Code.StepFor`). The predecessors are the startup (strict), the head (its shuffle is strict for
the words it reaches these roles by: `Wg1.stepFor_hsh`), the idle code, the MMA warp and the TMA
warp's election (a lane that loses it returns to the idle code). The TMA warp's other steps are
tolerant: for a TMA target `σ` the step from a TMA state is the caller's (`htma`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The shapes of a state of the head, the idle code, the MMA warp or the TMA warp. -/
theorem strict_shapes {σ : (thread P L g).D}
    (h : InRole P L g .wg1 σ ∨ InRole P L g .mma σ ∨ InRole P L g .tma σ) :
    (∃ s, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inl s⟩) ∨
    (∃ s, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.idle, s⟩⟩) ∨
    (∃ d, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.mma, d⟩⟩) ∨
    (∃ d, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩) := by
  rcases h with h | h | h <;> cases h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, rfl⟩))
  · exact .inr (.inr (.inr ⟨_, rfl⟩))

/-- Only the election leads the TMA warp to a hand-back state. -/
private theorem tma_leave_elect {d d3 : Tma.D} {e : Event} {s : IdleSite}
    (hn : Tma.succ P L g d e = some (some d3)) (hs : d3.site = .leave s) :
    d.site = .elect := by
  obtain ⟨site, a⟩ := d
  obtain ⟨site3, b⟩ := d3
  cases site <;> simp only [Tma.succ] at hn ⊢
  all_goals try simp only [Tma.poll, Tma.rdAny, Tma.afterQuad, Tma.ncWord, Tma.afterTopk, Tma.lensD,
    Tma.loopEntry, Tma.loopEnd, Tma.word32] at hn
  all_goals try (repeat' split at hn)
  all_goals simp_all [Tma.afterGather, Tma.afterCoord]
  all_goals (obtain ⟨hn, -⟩ := hn; split_ifs at hn)

/-- A word `7` does not reach the head, the idle code, the MMA warp or the TMA warp. -/
private theorem hsh_not7 {e : Event} {d' : (wg1Code P L g).D}
    (hn : (wg1Code P L g).next (Sum.inl Wg1.Site.hsh) e = some (some d'))
    (hd : (∃ s, d' = Sum.inl s) ∨ (∃ s, d' = .inr ⟨Sum.inl SubEntry.idle, s⟩) ∨
      (∃ d, d' = .inr ⟨Sum.inl SubEntry.mma, d⟩) ∨ (∃ d, d' = .inr ⟨Sum.inl SubEntry.tma, d⟩)) :
    ∀ md av bv cv x ok, e = ⟨Wg1.Site.pc P L g .hsh, .shfl md av bv cv (.bits 32 x) ok⟩ →
      ¬ Arith32.scmpi .eq .b x 7 = true := by
  intro md av bv cv x ok he c7
  subst he
  dsimp only [wg1Code, Code.roleLoop, Code.loopGlue, wg1HeadCode, Wg1.code] at hn
  simp only [Wg1.succ, Wg1.dispatch, c7, ↓reduceIte, Option.map_some, Option.some.injEq,
    Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel] at hn
  split at hn <;> split at hn <;> rcases hd with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
    simp_all

/-- A step of a sub-role's state in warpgroup 1's dispatch level. -/
private theorem wg1_next_inr {i : SubEntry} {d2 : (subFrag P L g i).D} {e : Event}
    {d' : (wg1Code P L g).D}
    (h : (wg1Code P L g).next (.inr ⟨Sum.inl i, d2⟩) e = some (some d')) :
    ∃ d3, (subFrag P L g i).next d2 e = some (some d3) ∧
      (subBack P L g i d3 = none → d' = .inr ⟨Sum.inl i, d3⟩) := by
  change (((subFrag P L g i).next d2 e).map (Option.map _)) = _ at h
  rcases hq : (subFrag P L g i).next d2 e with _ | _ | d3
  · rw [hq] at h; cases h
  · rw [hq] at h; cases h
  · rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨d3, rfl, fun hb => ?_⟩
    rw [← h]
    simp [Code.backEnter, hb]

/-- **The step before a state of the head, the idle code, the MMA or the TMA warp is strict.** -/
theorem thread_prev (hp : Pre P L m) {dj σ : (thread P L g).D} {e : Event}
    (hn : (thread P L g).next dj e = some (some σ))
    (hσ : InRole P L g .wg1 σ ∨ InRole P L g .mma σ ∨ InRole P L g .tma σ)
    (htma : (∃ d, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩) →
      ∀ d n, dj = (.inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩, n) →
        (thread P L g).StepFor dj e) :
    (thread P L g).StepFor dj e := by
  intro t u ins hat hinv hc hf
  obtain ⟨x, n⟩ := dj
  have hsh := strict_shapes hσ
  rcases x with d | ⟨i, y⟩
  · exact thread_start_stepFor hp ins hat hinv hc hf
  · obtain ⟨d', hd', hs1⟩ := Code.roleThread_next_role hn
    rcases i with i | r
    · cases i
      · exfalso
        rcases hsh with ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ <;> rw [h] at hs1 <;> cases hs1
      · have hshape : (∃ s, d' = Sum.inl s) ∨ (∃ s, d' = .inr ⟨Sum.inl SubEntry.idle, s⟩) ∨
            (∃ d, d' = .inr ⟨Sum.inl SubEntry.mma, d⟩) ∨
            (∃ d, d' = .inr ⟨Sum.inl SubEntry.tma, d⟩) := by
          rcases hsh with ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ <;> rw [h] at hs1 <;>
            obtain rfl := eq_of_heq (Sigma.mk.inj (Sum.inr.inj hs1)).2 <;> simp
        rcases y with h | ⟨j, d2⟩
        · refine thread_wg1_stepFor (wg1_inl_stepFor fun hx => ?_) ins hat hinv hc hf
          cases h
          · exact (Wg1.stepAt_head0 .smr rfl (by decide)).stepFor e
          · exact Wg1.stepFor_hsh hp e (hsh_not7 hd' hshape)
          all_goals simp [Wg1.exitOf] at hx
        · rcases j with j | r
          · cases j
            · exact thread_wg1_stepFor (wg1_inr_stepFor fun _ =>
                (Mma.stepAt hp d2).stepFor e) ins hat hinv hc hf
            · obtain ⟨d3, hd3, hb3⟩ := wg1_next_inr hd'
              by_cases hT : ∃ d, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩
              · exact htma hT d2 n rfl ins hat hinv hc hf
              · by_cases hb : subBack P L g .tma d3 = none
                · exfalso
                  exact hT ⟨d3, by rw [hs1, hb3 hb]⟩
                · have hl : d3.site = .leave (idleFirst P L g) := by
                    by_contra hne
                    exact hb (by simp [subBack, hne])
                  have hel := tma_leave_elect (P := P) (L := L) (g := g) hd3 hl
                  exact thread_wg1_stepFor (wg1_inr_stepFor fun _ =>
                    (Tma.stepAt_elect hp d2 hel).stepFor e) ins hat hinv hc hf
            · exfalso
              obtain ⟨d3, hd3, hb3⟩ := wg1_next_inr hd'
              rw [hb3 rfl] at hshape
              rcases hshape with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
            · exact thread_wg1_stepFor (wg1_inr_stepFor fun _ =>
                (Wg1.stepAt_idle hp d2).stepFor e) ins hat hinv hc hf
          · exfalso
            cases hd'
      · exfalso
        rcases hsh with ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ <;> rw [h] at hs1 <;> cases hs1
    · exfalso
      cases hd'

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **An event at a state of the head, the idle code, the MMA or the TMA warp fires from a
strictly good concrete state.** -/
theorem strict_event (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} {σ : (thread P L g).D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ))
    (hR : InRole P L g .wg1 σ ∨ InRole P L g .mma σ ∨ InRole P L g .tma σ)
    (htma : ∀ j dj ej, j + 1 = k → (X.tr g)[j]? = some ej →
      Frame.stateAt (thread P L) X g j = some (some dj) →
      (thread P L g).next dj ej = some (some σ) →
      (∃ d, σ.1 = .inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩) →
      ∀ d n, dj = (.inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl SubEntry.tma, d⟩⟩, n) →
        (thread P L g).StepFor dj ej) :
    ∃ t o ins, (thread P L g).Good (some σ) t ∧
      kernel.code[(thread P L g).pc σ]? = some ins ∧
      Fires ((thread P L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e o :=
  Frame.strict_site (fun _ _ => thread_sound hp) hX he hσ fun j dj ej hj hej hs hn =>
    thread_prev hp hn hR (htma j dj ej hj hej hs hn)

/-- **The same for a state of the head, the idle code or the MMA warp**: the step before it is
strict. -/
theorem strict_event_nontma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} {σ : (thread P L g).D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ))
    (hR : InRole P L g .wg1 σ ∨ InRole P L g .mma σ) :
    ∃ t o ins, (thread P L g).Good (some σ) t ∧
      kernel.code[(thread P L g).pc σ]? = some ins ∧
      Fires ((thread P L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e o := by
  refine strict_event hp hX he hσ (by tauto) fun j dj ej _ _ _ _ hT => ?_
  obtain ⟨d, hd⟩ := hT
  exfalso
  rcases hR with h | h <;> cases h <;> cases hd

/-- A dead step of the thread machine at a sub-role's state is the sub-role's. -/
theorem thread_next_none_sub {i : SubEntry} {d : (subFrag P L g i).D} {n : Cls → Nat}
    {e : Event}
    (h : (thread P L g).next (.inr ⟨Sum.inl Entry.wg1, .inr ⟨Sum.inl i, d⟩⟩, n) e = none) :
    (subFrag P L g i).next d e = none := by
  have h1 := Code.counted_next_eq_none_iff.mp h
  have h2 : (wg1Code P L g).next (.inr ⟨Sum.inl i, d⟩) e = none := by
    simpa only [Code.glue_next_inr, Option.map_eq_none_iff] using h1
  change (((subFrag P L g i).next d e).map (Option.map _)) = none at h2
  simpa using h2

/-- A dead step of the thread machine at a head state is the head's. -/
theorem thread_next_none_head {s : Wg1.Site} {n : Cls → Nat} {e : Event}
    (h : (thread P L g).next (.inr ⟨Sum.inl Entry.wg1, .inl s⟩, n) e = none) :
    Wg1.succ s e = none := by
  have h1 := Code.counted_next_eq_none_iff.mp h
  have h2 : (wg1Code P L g).next (.inl s) e = none := by
    simpa only [Code.glue_next_inr, Option.map_eq_none_iff] using h1
  change ((Wg1.succ s e).map (Option.map _)) = none at h2
  simpa using h2

/-- The thread machine's death at event `k`, as the dead step of its state. -/
theorem next_none_of_stops {k : Nat} {e : Event} {σ : (thread P L g).D}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (thread P L) X g k = some (some σ))
    (hs : StopsAt P L X g k) : (thread P L g).next σ e = none := by
  have h1 := stopsAt_iff.mp hs
  rw [Frame.stateAt_succ (C := thread P L) (show (X.tr g)[k]? = some e from he), hσ] at h1
  exact h1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
