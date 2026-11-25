-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ProgressStep

@[expose] public section

/-!
# The progress contract at a thread's last state: whole-warp events and stopped machines

The fields of `Proof/Schedule/Contract.lean: RefProgress` that are the scheduling library's
facts about whole-warp events, word for word, and the field about a thread whose machine has
stopped. Most of them speak about the state after a thread's LAST event (position
`(X.tr g).length`), which `stage` covers.

* `collEvent_at`, `collTmpl_at`, `collKind_at`: fields `collShape` and `collKind`. A shuffle or
  an election is fired only at a shuffle or an election site, all of which are at instructions
  up to 312, so the state is in the startup phase (`Stage.of_pc_startup`) and the startup's
  statements apply (`Startup.collShape_startup`, `collTmpl_startup`, `collKind_startup`). The
  function of the field is `collF`: the instruction and the static part of the `n`-th
  collective of a warp (`Startup.collShapeAt`).
* `matrixShape_at`, `matrixPrev_at`: fields `matrixShape` and `matrixPrev`. A matrix site is at
  an instruction of the compute loop, so the state is in the Compute phase
  (`Stage.of_pc_compute`), whose statements apply.
* `dead_unblocking`, `deadReleased_at`: field `deadReleased`. A machine stops (its successor
  along an event is `none`) only at a data condition of the Conversion, the CarryLoad, the
  Compute or the Store phase (`dead_cases`, `Tracked.lean`). The event before the stop is no
  `bar.sync` and no bulk-group wait: after each of those the machine has a successor state
  (`next_bar_some`; `Conversion.st_bar_1` at instruction 621; `Store.store_good` at 3093), and
  the program fires no other blocking kind of event. So the thread's last event never blocks,
  and the thread is released (`Sched.released_of_unblocking`).

Everything is in the sub-namespace `Assembly.Progress`; `hub` is as in `ProgressState.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress
open PTX PTX.Proof PTX.Flow PTX.Sched
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls coll_pc matrix_pc_range wkey)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The instruction and the static part of the `n`-th warp collective of a warp**, as the
function the field `collShape` asks for: the key of a warp is its block and its index in the
block, and the collectives depend on the index only. -/
def collF (c : Nat × Nat) (n : Nat) : Nat × CollShape := Startup.collShapeAt c.2 n

theorem collF_full (c : Nat × Nat) (n : Nat) : (collF c n).2.Full :=
  Startup.collShapeAt_full c.2 n

/-- The function of the field at a thread's warp key is the startup's at the thread's warp. -/
theorem collF_wkey (hpre : Pre P L mem0) (g n : Nat) :
    collF (wkey L g) n = Startup.collShapeAt (warp g) n := by
  simp only [collF, wkey, warp_eq hpre]

/-- **After a `bar.sync` other than those of the instructions 621 and 3113 the machine has a
successor state**, whatever the registers. -/
theorem next_bar_some (j : Fin 10) (h4 : j ≠ 4) (h7 : j ≠ 7) (w : Nat → BitVec 64)
    (p : Nat → Bool) (x : Nat → Value) (e : Event) :
    ∃ d', Thread.next L g ⟨.bar j, w, p, x⟩ e = some (some d') := by
  fin_cases j
  · exact ⟨_, Thread.next_bar_0 w p x e⟩
  · exact ⟨_, Thread.next_bar_1 w p x e⟩
  · exact ⟨_, Thread.next_bar_2 w p x e⟩
  · exact ⟨_, Thread.next_bar_3 w p x e⟩
  · exact absurd rfl h4
  · exact ⟨_, Thread.next_bar_5 w p x e⟩
  · exact ⟨_, Thread.next_bar_6 w p x e⟩
  · exact absurd rfl h7
  · exact ⟨_, Thread.next_bar_8 w p x e⟩
  · exact ⟨_, Thread.next_bar_9 w p x e⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-! ### Shuffles and elections -/

/-- **Field `collShape`, events**: a shuffle or an election of a thread has the static part of
the collective of its ordinal in the thread's warp. -/
theorem collEvent_at {k : Nat} {e : Event} {d : D} (hσ : At (code L) X g k d)
    (he : X.get (g, k) = some e) (hc : isWarpColl e = true) :
    kindShape e.kind = some (collF (wkey L g) (((X.tr g).take k).countP isWarpColl)).2 := by
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hkind := Compute.firedOnly_isWarpColl e _ hc (site_fires (sounds hpre) hX he hσ)
  have hp := collAll_le _ (coll_pc (cls_of_collKind hkind)).1
  have hI := (stage hpre hX hg (Nat.le_of_lt hklt) hσ).of_pc_startup (by omega)
  rw [collF_wkey hpre]
  exact Startup.collShape_startup hpre hX hg he hσ hI hc

/-- **Field `collShape`, templates**: at a thread's last state, when it is at a shuffle or an
election, the template of the instruction is undefined behaviour or the collective of the
thread's ordinal: its instruction and its static part. -/
theorem collTmpl_at {d : D} {t : TState} {m : Tmpl}
    (hσ : At (code L) X g (X.tr g).length d) (hc : siteCls d.site = .coll)
    (hat : (code L g).AtD d t) (hinv : (code L g).inv d)
    (hout : out kernel Assumptions.all L g t = .ev m) :
    (∃ f, m = .ub f) ∨
      (t.pc = (collF (wkey L g) ((X.tr g).countP isWarpColl)).1 ∧
        tmplShape m = some (collF (wkey L g) ((X.tr g).countP isWarpColl)).2) := by
  have hp := collAll_le _ (coll_pc hc).1
  have hI := (stage hpre hX hg le_rfl hσ).of_pc_startup (by omega)
  have h := Startup.collTmpl_startup hpre hg hI (coll_site hc) hat hinv hout
  rw [List.take_length] at h
  rw [collF_wkey hpre]
  exact h

/-- **Field `collKind`**: the template at a collective state, when it has a static part, is a
shuffle or an election. -/
theorem collKind_at {d : D} {t : TState} {m : Tmpl} {s : CollShape}
    (hσ : At (code L) X g (X.tr g).length d) (hc : siteCls d.site = .coll)
    (hat : (code L g).AtD d t) (hinv : (code L g).inv d)
    (hout : out kernel Assumptions.all L g t = .ev m) (hs : tmplShape m = some s) :
    s.tag ≤ 1 := by
  have hp := collAll_le _ (coll_pc hc).1
  have hI := (stage hpre hX hg le_rfl hσ).of_pc_startup (by omega)
  exact Startup.collKind_startup hpre hg hI (coll_site hc) hat hinv hout hs

/-! ### Matrix events -/

/-- **Field `matrixShape`**: at a thread's last state, when it is at a matrix event, the
template is undefined behaviour or the matrix event of the instruction whose ordinal among the
182 matrix instructions is the number of the thread's matrix events modulo 182. -/
theorem matrixShape_at {d : D} {t : TState} {m : Tmpl}
    (hσ : At (code L) X g (X.tr g).length d) (hm : siteCls d.site = .matrix)
    (hat : (code L g).AtD d t) (hout : out kernel Assumptions.all L g t = .ev m) :
    (∃ f, m = .ub f) ∨
      ∃ pc op own k, Top.matrixSites[(X.tr g).countP isMatrix % 182]? = some (pc, op) ∧
        t.pc = pc ∧ m = .matrix op own k := by
  have hp := matrix_pc_range hm
  obtain ⟨-, j0, s0, -, -, -, hI⟩ :=
    (stage hpre hX hg le_rfl hσ).of_pc_compute (by omega) (by omega)
  exact Compute.matrixShape_compute hpre hg hI hm hat hout

/-- **Field `matrixPrev`**: the event before a matrix event never blocks. -/
theorem matrixPrev_at {d : D} (hσ : At (code L) X g (X.tr g).length d)
    (hm : siteCls d.site = .matrix) {q : Event}
    (hq : X.get (g, (X.tr g).length - 1) = some q) : Unblocking q.kind := by
  have hp := matrix_pc_range hm
  obtain ⟨-, j0, s0, past, -, hin, hI⟩ :=
    (stage hpre hX hg le_rfl hσ).of_pc_compute (by omega) (by omega)
  exact Compute.matrixPrev_compute hpre hX hg past.state hin hσ hI hm hq

/-! ### A stopped machine -/

/-- **The event before a machine's stop never blocks**: an event of a launched thread, other
than its `ret`, along which the machine's successor is `none` is no `bar.sync` and no
bulk-group wait. -/
theorem dead_unblocking {i : Nat} {d : D} {e : Event} (he : X.get (g, i) = some e)
    (hd : At (code L) X g i d) (hn : Thread.next L g d e = none)
    (hx : ∀ pc, e ≠ ⟨pc, .exit⟩) : Unblocking e.kind := by
  have hfire := site_fires (sounds hpre) hX he hd
  have hcases := dead_cases hpre hX hg he hd hn hx
  have hrange : 387 ≤ d.site.pc ∧ d.site.pc ≤ 3112 := by
    rcases hcases with ⟨j0, hI⟩ | ⟨j0, hI⟩ | ⟨-, j0, hI⟩ | ⟨-, hI⟩
    · have := pc_conversion hI
      omega
    · have := pc_carryLoad hI
      omega
    · have := pc_compute hI
      omega
    · have := pc_store_inv hI
      omega
  have hconv : d.site.pc = 621 → ∃ j0, Conversion.Inv P X g j0 i d := by
    intro h
    rcases hcases with hI | ⟨j0, hI⟩ | ⟨-, j0, hI⟩ | ⟨-, hI⟩
    · exact hI
    · have := pc_carryLoad hI
      omega
    · have := pc_compute hI
      omega
    · have := pc_store_inv hI
      omega
  have hstore : d.site.pc = 3093 → Store.Inv P X g i d := by
    intro h
    rcases hcases with ⟨j0, hI⟩ | ⟨j0, hI⟩ | ⟨-, j0, hI⟩ | ⟨-, hI⟩
    · have := pc_conversion hI
      omega
    · have := pc_carryLoad hI
      omega
    · have := pc_compute hI
      omega
    · exact hI
  refine Compute.unblocking_of_fired hfire ?_ ?_
  · intro hk
    obtain ⟨j, hj⟩ := site_of_bar hk
    obtain ⟨site, w, p, x⟩ := d
    obtain rfl : site = .bar j := hj
    by_cases h4 : j = 4
    · subst h4
      obtain ⟨j0, pos, hr, -⟩ := hconv rfl
      have hs : Site.bar 4 = pos.site := hr.site
      cases pos with
      | fence => cases hs
      | ld j u => cases hs
      | st j u => cases hs
      | bar jj =>
        have hv : (4 : Nat) = 3 + jj.val := congrArg Fin.val (Site.bar.inj hs)
        obtain rfl : jj = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
        obtain ⟨d0, h1, -⟩ := Conversion.st_bar_1 hpre hg hr
        have h2 := (Thread.next_bar_4 w p x e).symm.trans hn
        rw [h1] at h2
        cases h2
    · by_cases h7 : j = 7
      · subst h7
        have h3113 : (Site.bar 7).pc = 3113 := rfl
        have := hrange.2
        dsimp only at this
        omega
      · obtain ⟨d', hd'⟩ := next_bar_some (L := L) (g := g) j h4 h7 w p x e
        rw [hd'] at hn
        cases hn
  · intro hk
    obtain ⟨j, hj⟩ := site_of_bulkWait hk
    obtain ⟨site, w, p, x⟩ := d
    obtain rfl : site = .bulkWait j := hj
    fin_cases j
    · have hI := hstore rfl
      obtain ⟨pos, hr, -, -, hnx⟩ := Store.store_good hpre hX hg he hd hI
      rcases hnx with ⟨d', hd'⟩ | ⟨hread, -⟩
      · rw [hd'] at hn
        cases hn
      · have hs : Site.bulkWait 0 = pos.site := hr.site
        cases pos <;> first | (cases hs; done) | cases hread
    · have h2 := (Thread.next_bulkWait_1 w p x e).symm.trans hn
      cases h2

/-- **Field `deadReleased`**: a pending thread whose machine has stopped is released, given
that the thread has no undefined-behaviour event (its machine then stopped at its last event,
which never blocks). -/
theorem deadReleased_at (hub : ∀ k, NoUb X g k) (hp : Frame.Pending L X g)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = none) : Step.Released L X g := by
  obtain ⟨i, d, hi, hd, hnone⟩ := Frame.first_stop (tracked hpre hX) hg hσ
  obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi⟩
  have hlast : i + 1 = (X.tr g).length := by
    by_contra hne
    have hlt : i + 1 < (X.tr g).length := by omega
    obtain ⟨e', he'⟩ : ∃ e', X.get (g, i + 1) = some e' := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨d', hd'⟩ := Frame.event_state (sounds hpre) hX (tracked hpre hX) he'
      fun pc f h => hub (i + 2) (i + 1) (by omega) pc f (h ▸ he')
    rw [hnone] at hd'
    cases hd'
  have hn : Thread.next L g d e = none := by
    rw [Frame.stateAt_succ he, hd] at hnone
    exact hnone
  have hq : X.get (g, (X.tr g).length - 1) = some e := by
    rw [← hlast]
    exact he
  have hx : ∀ pc, e ≠ ⟨pc, .exit⟩ := by
    rintro pc rfl
    refine hp.2.2 pc ?_
    rw [List.getLast?_eq_getElem?]
    exact hq
  exact released_of_unblocking hq (dead_unblocking hpre hX hg he hd hn hx)

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Progress
