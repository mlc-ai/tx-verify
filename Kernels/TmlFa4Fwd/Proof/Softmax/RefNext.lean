-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef
public import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
import Kernels.TmlFa4Fwd.Proof.Softmax.RefStep
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' reference invariant and its step

`Ref` is the count conjuncts (`RefCounts`); `Expect` is what an event must return: a 32-bit word
at the scheduler's reads and shuffles and at the request's reads. `ref_next` is the `ref_next`
obligation of the counted machine: under `Ref`, an expected event of the state's shape that is no
undefined behaviour does not stop the machine and leads to a state satisfying `Ref`. The machine
stops only on a word of another kind (rule M1) and at a plain load's implicit wait at a sub-step
other than 1, which `Ref` excludes. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The first state satisfies the reference invariant. -/
theorem ref_init : Ref p L g (MC p L g).init := ⟨refCounts_init p L g⟩

set_option hygiene false in
/-- A branch of a stopping step contradicts the sub-step or the expected value. -/
macro "ns_close" : tactic => `(tactic| (
  first
    | (cases h; done)
    | (exfalso; simp_all; done)
    | (exfalso
       obtain ⟨_, hx⟩ := hE _ _ ‹_›
       simp_all; done)
    | (exfalso
       obtain ⟨_, hx⟩ := hE _ _ _ _ _ _ ‹_›
       simp_all; done)))

set_option hygiene false in
/-- Unfold a stopping step at a site with literal fields and close its branches. -/
macro "ns_all" : tactic => `(tactic| (
  simp only [ExpectD] at hE
  simp only [succ, word32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit, passStart,
    afterTiles, afterRound, afterFirst, afterBias, afterPlain, plainEntry, afterLoads, pstNext,
    Epilogue.Scan.late, Epilogue.loopOf, Fin.isValue, ↓reduceIte, Bool.false_eq_true] at h
  repeat' (first | (cases h; done) | split at h |
    simp only [Option.map_some, Option.map_none, reduceCtorEq] at h)
  all_goals ns_close))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_word (sk : Epilogue.Scan)
    {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.word sk, v, k, acc⟩ e)
    (h : succ p L g ⟨.word sk, v, k, acc⟩ e = some none) : False := by
  cases sk <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_down (sk : Epilogue.Scan)
    {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.down sk, v, k, acc⟩ e)
    (h : succ p L g ⟨.down sk, v, k, acc⟩ e = some none) : False := by
  cases sk <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_total (sk : Epilogue.Scan)
    {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.total sk, v, k, acc⟩ e)
    (h : succ p L g ⟨.total sk, v, k, acc⟩ e = some none) : False := by
  cases sk <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_up (sk : Epilogue.Scan) (j : Fin 5)
    {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.up sk j, v, k, acc⟩ e)
    (h : succ p L g ⟨.up sk j, v, k, acc⟩ e = some none) : False := by
  cases sk <;> fin_cases j <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_vote (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.vote l, v, k, acc⟩ e)
    (h : succ p L g ⟨.vote l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pre (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pre l, v, k, acc⟩ e)
    (h : succ p L g ⟨.pre l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_tiles (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.tiles l, v, k, acc⟩ e)
    (h : succ p L g ⟨.tiles l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_wend (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.wend l, v, k, acc⟩ e)
    (h : succ p L g ⟨.wend l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_barEnd (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.barEnd l, v, k, acc⟩ e)
    (h : succ p L g ⟨.barEnd l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_exit (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.exit l, v, k, acc⟩ e)
    (h : succ p L g ⟨.exit l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_wb (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.wb l, v, k, acc⟩ e)
    (h : succ p L g ⟨.wb l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_fence (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.fence l, v, k, acc⟩ e)
    (h : succ p L g ⟨.fence l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_bsync (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.bsync l, v, k, acc⟩ e)
    (h : succ p L g ⟨.bsync l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_barr (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.barr l, v, k, acc⟩ e)
    (h : succ p L g ⟨.barr l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_stat (l : Bool) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.stat l, v, k, acc⟩ e)
    (h : succ p L g ⟨.stat l, v, k, acc⟩ e = some none) : False := by
  cases l <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_ws (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.ws r, v, k, acc⟩ e)
    (h : succ p L g ⟨.ws r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_narr (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.narr r, v, k, acc⟩ e)
    (h : succ p L g ⟨.narr r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_parr (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.parr r, v, k, acc⟩ e)
    (h : succ p L g ⟨.parr r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pws (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pws r, v, k, acc⟩ e)
    (h : succ p L g ⟨.pws r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pel (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pel r, v, k, acc⟩ e)
    (h : succ p L g ⟨.pel r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_parr2 (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.parr2 r, v, k, acc⟩ e)
    (h : succ p L g ⟨.parr2 r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pwend (r : Rd) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pwend r, v, k, acc⟩ e)
    (h : succ p L g ⟨.pwend r, v, k, acc⟩ e = some none) : False := by
  cases r <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pst (r : Rd) (q : Fin 4) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pst r q, v, k, acc⟩ e)
    (h : succ p L g ⟨.pst r q, v, k, acc⟩ e = some none) : False := by
  cases r <;> fin_cases q <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_pwst (r : Rd) (j : Fin 2)
    {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.pwst r j, v, k, acc⟩ e)
    (h : succ p L g ⟨.pwst r j, v, k, acc⟩ e = some none) : False := by
  cases r <;> fin_cases j <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem not_stop_fin (j : Fin 2) {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hE : ExpectD p L g ⟨.fin j, v, k, acc⟩ e)
    (h : succ p L g ⟨.fin j, v, k, acc⟩ e = some none) : False := by
  fin_cases j <;> ns_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **Under `Ref`, an expected event does not stop the machine.** -/
theorem not_stop {d : D} {e : Event} {n : Cnt → Nat} (hJ : Ref p L g (d, n))
    (hE : ExpectD p L g d e) (h : succ p L g d e = some none) : False := by
  obtain ⟨⟨rb, rp, hQ⟩⟩ := hJ
  have hw := hQ.wait
  obtain ⟨s, v, k, acc⟩ := d
  simp only at hw
  cases s with
  | word sk => exact not_stop_word sk hE h
  | down sk => exact not_stop_down sk hE h
  | total sk => exact not_stop_total sk hE h
  | up sk j => exact not_stop_up sk j hE h
  | vote l => exact not_stop_vote l hE h
  | pre l => exact not_stop_pre l hE h
  | tiles l => exact not_stop_tiles l hE h
  | wend l => exact not_stop_wend l hE h
  | barEnd l => exact not_stop_barEnd l hE h
  | exit l => exact not_stop_exit l hE h
  | wb l => exact not_stop_wb l hE h
  | fence l => exact not_stop_fence l hE h
  | bsync l => exact not_stop_bsync l hE h
  | barr l => exact not_stop_barr l hE h
  | stat l => exact not_stop_stat l hE h
  | bld l c =>
    simp only [ExpectD] at hE
    simp only [succ] at h
    split at h
    · rename_i a bs hk
      obtain ⟨x, hx, hok⟩ := hE a bs hk
      simp only [hx, hok, ↓reduceIte] at h
      split at h <;> cases h
    · cases h
  | ws r => exact not_stop_ws r hE h
  | narr r => exact not_stop_narr r hE h
  | parr r => exact not_stop_parr r hE h
  | pws r => exact not_stop_pws r hE h
  | pel r => exact not_stop_pel r hE h
  | parr2 r => exact not_stop_parr2 r hE h
  | pwend r => exact not_stop_pwend r hE h
  | sld r c =>
    simp only [ExpectD] at hE
    simp only [succ] at h
    split at h
    · rename_i a vals sh hk
      obtain ⟨xs, hxs⟩ := flAll_some_of (hE a vals sh hk)
      rw [hxs] at h
      cases r <;> simp at h
    · cases h
  | pst r q => exact not_stop_pst r q hE h
  | pwst r j => exact not_stop_pwst r j hE h
  | sldw c =>
    have := hw c rfl
    subst this
    simp only [succ] at h
    split at h <;> first | (cases h; done) | (exfalso; simp_all)
  | fin j => exact not_stop_fin j hE h
  | _ => ns_all

set_option hygiene false in
/-- Close a dying step: the event is undefined behaviour or the exit, or its kind (from the shape
table) and the expected value make the successor exist. -/
macro "ne_all" : tactic => `(tactic| (
  simp only [ExpectD] at hE
  simp only [Ev, rdOrUb, tcLdOrUb, Epilogue.Ev, Site.toE, hub, exists_false, or_false] at hev
  repeat' (obtain ⟨_, hev⟩ := hev)
  first
    | exact Or.inr hev
    | (simp only [succ] at h
       try simp only [hev] at h
       first
         | (cases h; done)
         | (obtain ⟨_, hx⟩ := hE _ _ hev
            simp only [hx] at h
            first | (cases h; done) | (split at h <;> cases h))
         | (obtain ⟨_, hx⟩ := hE _ _ _ _ _ _ hev
            simp only [hx, word32] at h
            cases h)
         | (obtain ⟨_, hx, h1, h2⟩ := hE _ _ _ _ _ _ hev
            simp only [hx, afterTiles, scAt, D.mk', h1, h2, ↓reduceIte, Option.map_some,
              Bool.false_eq_true] at h
            cases h)
         | (split at h <;> cases h))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **No death before the exit**: an expected event of the state's shape whose successor is
`none` (the thread has no rule to continue) is undefined behaviour or the exit. -/
theorem next_ends {d : D} {e : Event} (hE : ExpectD p L g d e) (hev : Ev p L g d e)
    (h : succ p L g d e = none) : Ends e := by
  by_cases hub : ∃ f, e.kind = .ub f
  · exact Or.inl hub
  simp only [not_exists] at hub
  obtain ⟨s, v, k, acc⟩ := d
  cases s with
  | word sk | down sk | total sk => cases sk <;> ne_all
  | up sk j => cases sk <;> fin_cases j <;> ne_all
  | vote l | pre l | tiles l | wend l | barEnd l | exit l | wb l | fence l | bsync l
  | barr l | stat l => cases l <;> ne_all
  | bld l c =>
    simp only [ExpectD] at hE
    simp only [Ev, rdOrUb, hub, exists_false, or_false] at hev
    obtain ⟨a, bs, hk⟩ := hev
    obtain ⟨x, hx, hok⟩ := hE a bs hk
    simp only [succ, hk, hx, hok, ↓reduceIte] at h
    split at h <;> cases h
  | ws r | narr r | parr r | pws r | pel r | parr2 r | pwend r | sld r _ => cases r <;> ne_all
  | pst r q =>
    cases r <;> fin_cases q <;> simp [succ, pstNext] at h <;> split at h <;> simp at h
  | pwst r j => cases r <;> fin_cases j <;> ne_all
  | fin j => fin_cases j <;> ne_all
  | _ => ne_all

/-- **The `ref_next` obligation of the softmax warps**: at a counted state satisfying `Ref`, an
expected event of the state's shape that is no undefined behaviour neither stops the counted
machine nor leads to a state that breaks `Ref`. -/
theorem ref_next (hp : Pre p L m) {dn : D × (Cnt → Nat)} {e : Event} (hJ : Ref p L g dn)
    (hE : Expect p L g dn e) (hev : Ev p L g dn.1 e) (hub : ∀ f, e.kind ≠ .ub f) :
    (MC p L g).next dn e ≠ some none ∧
      ∀ dn', (MC p L g).next dn e = some (some dn') → Ref p L g dn' := by
  obtain ⟨d, n⟩ := dn
  refine ⟨fun h => not_stop hJ hE (Code.counted_next_none_iff.mp h), fun dn' h => ?_⟩
  obtain ⟨hn, h2⟩ := Code.counted_next_some h
  obtain ⟨⟨rb, rp, hQ⟩⟩ := hJ
  obtain ⟨rb', rp', hQ'⟩ := counts_step hp hQ hev hub hn
  obtain ⟨d', n'⟩ := dn'
  simp only at h2 hQ' ⊢
  subst h2
  exact ⟨⟨rb', rp', hQ'⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
