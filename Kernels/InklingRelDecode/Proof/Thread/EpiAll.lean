-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiStores
public import Kernels.InklingRelDecode.Proof.Thread.EpiSound
public import Lemmas.Flow.Step.SiteIte

@[expose] public section

/-! # The epilogue's obligations at every site

`stepAt_all` is the code machine's obligation for every state, by `site_cases`: the barriers, the
register increase, the write of the dispatch table, the guarded release and the return need no
site text; the poll of `o_final` (`EpiPoll`), the broadcast and the load (`EpiSteps0`), the
load's wait and the stores (`EpiStores`, with the packs, products and address arithmetic of
`EpiPm`, `EpiSegs`) have their own step lemmas (`stepOk_of`). `site_ok_all` (every site is an
event instruction whose guard holds by its facts: the stores' row-valid `%p175`, `LsePart`'s
storing lane `%p174`, the release's `%p3`, true by the invariant) is its `site` field. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

/-- A step lemma of the form `Step` (with the warp register the thread's) as the machine's
`StepOk`. -/
theorem stepOk_of {d0 d : D}
    (hs : ∀ {t e u ins}, Inv d → d.pr.w = g % L.block / 32 → At t d.site.pc (facts d) →
      kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step L g d e u) :
    (code asms L g d0).StepOk d where
  step := by
    intro t e u ins h hi hc hf
    rcases hs hi.1 hi.2 h hc hf with (hn | ⟨d', t', hn, hr, ht, hi'⟩) | ⟨hn, hd⟩
    · exact .inl (.inl hn)
    · exact .inl (.inr ⟨d', t', hn, hr,
        ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi', by rw [next_pr hn]; exact hi.2⟩)
    · exact .inr ⟨hn, hd⟩

/-- The guard `%p174` of the store of `LsePart` holds at its site. -/
theorem guard_lse {d : D} (hi : Inv d) (hs : d.site = .stLse) : valueOf d 174 = .pred true := by
  show Value.pred (d.pr.lead && d.pr.rv) = _
  rw [hi.lead hs, hi.rv (hs ▸ trivial)]
  rfl

set_option hygiene false in
/-- The successor's invariant: the same data at another site (the release only with `%p3`). -/
macro "epi_inv" : tactic => `(tactic| (
  intro hi
  refine ⟨?_, hi.2⟩
  (try split) <;> exact inv_site hi.1 _ (fun h => absurd h (by simp [LoadedSite]))
    (fun h => absurd h (by simp)) (fun h => absurd h (by simp [StoreSite]))
    (fun h => absurd h (by simp))
    (by first | (intro h; cases h; done) | (intro _; simp only; assumption))))

/-- The guard of a site: `%p3` at the release, the row-valid `%p175` at a store of `OPart`,
`%p174` at the store of `LsePart`, all from the invariant. -/
macro "epi_guard" : tactic => `(tactic| first
  | rfl
  | exact congrArg Value.pred ((‹Inv _ ∧ _›).1.dealloc rfl)
  | exact congrArg Value.pred ((‹Inv _ ∧ _›).1.rv trivial)
  | exact guard_lse (‹Inv _ ∧ _›).1 rfl
  | fail "epi_guard")

/-- **The machine's obligation at every state**: `site_cases` over the sites, except the
sites with their own step lemmas (the poll, the broadcast, the load and its wait: `EpiPoll`,
`EpiSteps0`, `EpiStores`; the stores: `EpiStores`). -/
theorem stepAt_all (d0 d : D) : (code asms L g d0).StepAt d := by
  obtain ⟨s, pr, o, sk⟩ := d
  site_cases s except [
      .wait => stepOk_of fun hi _ h hc hf => step_wait pr o sk hi h hc hf,
      .shfl => stepOk_of fun hi hw h hc hf => step_shfl pr o sk hi hw h hc hf,
      .ld => stepOk_of fun hi _ h hc hf => step_ld pr o sk hi h hc hf,
      .waitLd => stepOk_of fun hi _ h hc hf => step_waitLd pr o sk hi h hc hf,
      .stLse => stepOk_of fun hi _ h hc hf => step_stLse pr o sk hi h hc hf,
      .stO _ => stepOk_of fun hi _ h hc hf => step_stO _ pr o sk hi h hc hf]
    trans [next]
    seg_by (intro t h; epi_seg h)
    inv_by (epi_inv)
    guard_by (epi_guard)

/-- **Every site is an event instruction whose guard holds by the facts** (the `site` field of
`stepAt_all`, at a launch where the warp register is the thread's warp: the facts do not depend on
the launch). -/
theorem site_ok_all {d : D} (hi : Inv d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts d) ins.guard :=
  (stepAt_all (L := { grid := 1, block := d.pr.w * 32 + 32, params := fun _ => none })
    (g := d.pr.w * 32) d d).site ⟨hi, by
      show d.pr.w = d.pr.w * 32 % (d.pr.w * 32 + 32) / 32
      rw [Nat.mod_eq_of_lt (by omega)]
      omega⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
