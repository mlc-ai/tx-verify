-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollShapePc

@[expose] public section

/-! # `WarpCollFacts.shape`

The `n`-th warp collective of a lane of warp `key` is at time `S key n` of the warp collectives'
schedule (`Cross.WarpSched`: its `atEv` clause for a collective of the trace, its `endAt`
clause for the state at the trace's end). Its position is the position of that time
(`state_pc`, `collPc`), and its static part is that position's (`fired_shape`, `out_shape`,
`pcShape`), whose masks are full (`pcShape_full`). So `F key n` is the position of the time
`S key n` with the static part of that position. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Cross Sched

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`WarpCollFacts.shape`.** -/
theorem WarpCollFacts_shape (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L) {S : Nat × Nat → Nat → Nat}
    (hs : WarpSched L X S) :
    ∃ F : Nat × Nat → Nat → Nat × Sched.CollShape,
      (∀ key n, (F key n).2.Full) ∧
      (∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
        X.get (g, k) = some e → Sched.isWarpColl e = true →
        Sched.kindShape e.kind = some (F (warpKey L g) (((X.tr g).take k).countP
            Sched.isWarpColl)).2) ∧
      (∀ {g : Nat} {d : ThreadD} {t : TState} {m : Tmpl}, g < L.threads →
        St L X g (X.tr g).length = some (some d) → nextKind d = .warp → (code L g).AtD d t →
        out kernel asms L g t = .ev m → (∃ f, m = .ub f) ∨
          (t.pc = (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1 ∧
            Sched.tmplShape m = some (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).2)) := by
  refine ⟨fun key n => (collPc (Work.n L) (S key n), pcShape (collPc (Work.n L) (S key n))),
    fun _ _ => pcShape_full _, ?_, ?_⟩
  · intro g k e d hg hσ he hw
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨hkw, hsh⟩ := fired_shape hpre hX hok hg hσ he hw
    obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hg hk.le hσ
    rw [hsh, state_pc hinv hkw,
      show stateTime L g d = _ from hs.sched.atEv hg trivial hσ he hw]
  · intro g d t m hg hσ hk hat hout
    rcases out_shape hat hk hout with hub | ⟨hpc, hsh⟩
    · exact .inl hub
    obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hg le_rfl hσ
    have hp : t.pc = collPc (Work.n L) (S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)) := by
      rw [hpc, state_pc hinv hk, hs.endAt hg hσ hk]
    exact .inr ⟨hp, by rw [hsh, hp]⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
