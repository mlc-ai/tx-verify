-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompNext
public import Lemmas.Flow.Compose

@[expose] public section

/-!
# The worker thread machine: the obligation of every state

`stepAt` proves `Code.StepAt` for every state of `code L g Q` (`WCompBase.lean`) by delegating to
the role machines:

* a worker state (`.worker w`) by `Worker.site_ok` and `Worker.step`; the dispatch (`.ldRole`)
  turns the worker's successor, the entry of a role, into the role's first state with the
  entries of `WCompEntry.lean` (`roleStart_good`);
* the idle role by `Worker.Idle.stepAt`, and its last event (`setmaxnreg.inc`) by
  `Worker.Idle.return_loop`;
* the loader by `Loader.step`, and its last event by `loader_return`;
* the MMA warp by `Mma.step`, and its last event by `mma_return`;
* the exit by `exit_bar_step` (the `bar.sync 0`, then the skipped `tcgen05.dealloc`) and, for
  the `ret`, because no event follows it.

The hypotheses are those of the role machines: the launch satisfies `Pre` (the MMA warp's steps
read it; the worker's start reads the CTA shape and the parameters), and the thread is in warp 4
or above. `Pre` also gives the shared base as a 32-bit number, which the MMA warp's return needs
(`Loader.baseW L` is that number). -/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {e : Event} {t u : TState} {ins : Instr}

/-! ### Concrete states of the composed states -/

theorem good_worker {w : Worker.D} (h : At t w.site.pc (Worker.facts L g w))
    (hi : Worker.Inv L g w) : (code L g Q).Good (some (.worker w)) t :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, hi⟩

theorem good_idle {d : Worker.Idle.D} (h : At t d.site.pc (Worker.Idle.facts L g d))
    (hi : Inv L g (.idle d)) : (code L g Q).Good (some (.idle d)) t :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, hi⟩

theorem good_exit {x : ExitD} (h : At t x.site.pc (exitFacts L g x))
    (hi : Inv L g (.exit x)) : (code L g Q).Good (some (.exit x)) t :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, hi⟩

/-! ### The successors of a state, by the state's own machine -/

theorem next_worker_ne {w : Worker.D} (hs : w.site ≠ .ldRole) :
    (code L g Q).next (.worker w) e = (Worker.next L g w e).map (Option.map .worker) := by
  obtain ⟨s, P⟩ := w
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_loader_ne {d : Loader.D} (P : Pro) (hs : d.site ≠ .setMaxInc) :
    (code L g Q).next (.loader d P) e =
      (Loader.next L g d e).map (Option.map (fun d' => .loader d' P)) := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_mma_ne {d : Mma.D} (P : Pro) (hs : d.site ≠ .setMaxRegInc) :
    (code L g Q).next (.mma d P) e =
      (Mma.next L g d e).map (Option.map (fun d' => .mma d' P)) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

theorem next_idle_ne {d : Worker.Idle.D} (hs : d.site ≠ .inc) :
    (code L g Q).next (.idle d) e = (Worker.Idle.next d e).map (Option.map .idle) := by
  obtain ⟨s, P⟩ := d
  cases s <;> first | rfl | exact absurd rfl hs

/-! ### The dispatch -/

/-- The state a role's entry gives: the role's first state, whose concrete states are those of
the worker's entry state, or no state the machine follows. -/
theorem roleStart_good (hsb : L.sharedBase < 2 ^ 32) {P : Pro} {s : Worker.Site}
    (hs : s = .toLoader ∨ s = .toMma ∨ s = .toIdle ∨ s = .toExit ∨ s = .bad0)
    (hi : Worker.Inv L g ⟨s, P⟩) (h : At t s.pc (Worker.facts L g ⟨s, P⟩)) :
    roleStart L g P s = some none ∨
      ∃ d, roleStart L g P s = some (some d) ∧ (code L g Q).Good (some d) t := by
  have hb : Loader.baseW L = BitVec.ofNat 64 L.sharedBase := baseW_eq hsb
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := loader_entry hi h
    exact .inr ⟨.loader (Loader.D.start L g (handoffPro L g P)) (handoffPro L g P),
      by simp [roleStart], ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩, h2⟩⟩
  · cases htm : tmOf (P.rest 463) with
    | none => exact .inl (by simp [roleStart, htm])
    | some tm =>
      by_cases hc : tm + 512 ≤ 2 ^ 16
      · obtain ⟨h1, h2⟩ := mma_entry hi h htm (by omega) hc hb
        refine .inr ⟨.mma ⟨.setMaxReg, 0, 0, tm, Pro.val L g (handoffPro L g P)⟩
          (handoffPro L g P), ?_, ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩, h2⟩⟩
        simp only [roleStart, htm, hc, ↓reduceIte]
      · exact .inl (by simp only [roleStart, htm, hc, ↓reduceIte])
  · obtain ⟨h1, h2⟩ := idle_entry hi h
    exact .inr ⟨.idle (Worker.Idle.D.start P), by simp [roleStart], good_idle h1 h2⟩
  · obtain ⟨h1, h2⟩ := exit_entry hi h
    exact .inr ⟨.exit ⟨.bar, P⟩, by simp [roleStart], good_exit h1 h2⟩
  · exact .inr ⟨.worker ⟨.bad0, P⟩, by simp [roleStart], good_worker h hi⟩

/-- The dispatch's successor is one of the role entries. -/
theorem ldRole_some {P : Pro} {d' : Worker.D}
    (h : Worker.next L g ⟨.ldRole, P⟩ e = some (some d')) :
    d'.P = P ∧ (d'.site = .toLoader ∨ d'.site = .toMma ∨ d'.site = .toIdle ∨
      d'.site = .toExit ∨ d'.site = .bad0) := by
  unfold Worker.next at h
  simp only at h
  split at h
  · exact dispatch_some h
  · cases h

/-- With a base word that has room for the 512 columns, every role entry is followed. -/
theorem roleStart_ne {P : Pro} (hb : baseOk P) {s : Worker.Site}
    (hs : s = .toLoader ∨ s = .toMma ∨ s = .toIdle ∨ s = .toExit ∨ s = .bad0) :
    roleStart L g P s ≠ some none := by
  obtain ⟨tm, htm, hc⟩ := hb
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · simp [roleStart]
  · simp only [roleStart, htm, hc, ↓reduceIte]
    simp
  · simp [roleStart]
  · simp [roleStart]
  · simp [roleStart]

/-- **The dispatch follows every role byte on every warp**, when the inherited Tensor Memory
base word has room for the 512 columns (`baseOk`). -/
theorem ldRole_next_follows {P : Pro} (hb : baseOk P) :
    next L g (.worker ⟨.ldRole, P⟩) e ≠ some none := by
  simp only [next, dispatch]
  cases h : Worker.next L g ⟨.ldRole, P⟩ e with
  | none => simp
  | some o =>
    cases o with
    | none =>
      exfalso
      simp only [Worker.next] at h
      split at h
      · unfold Worker.dispatch at h
        repeat' split at h
        all_goals simp at h
      · simp at h
    | some d' =>
      obtain ⟨-, hs⟩ := ldRole_some h
      exact roleStart_ne hb hs

/-! ### The states -/

/-- A worker state: the prologue and the dispatch. -/
theorem stepAt_worker (hsb : L.sharedBase < 2 ^ 32) (w : Worker.D) :
    (code L g Q).StepAt (.worker w) where
  site hi := Worker.site_ok hi
  step := by
    intro t e u ins h hi hc hf
    have h' : At t w.site.pc (Worker.facts L g w) := h
    have hi' : Worker.Inv L g w := hi
    have hc' : kernel.code[w.site.pc]? = some ins := hc
    have hf' : Fires w.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
    by_cases hs : w.site = .ldRole
    · obtain ⟨site, P⟩ := w
      simp only at hs
      subst hs
      have hnext : (code L g Q).next (.worker ⟨.ldRole, P⟩) e = dispatch L g P e := rfl
      rcases Worker.step hi' h' hc' hf' with (hn | ⟨d', t', hn, hr, ht', hi''⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (hnext.trans (by unfold dispatch; rw [hn])))
      · obtain ⟨hP, hsite⟩ := ldRole_some hn
        obtain ⟨s, P'⟩ := d'
        simp only at hP hsite ht' hi'' ⊢
        subst hP
        rcases roleStart_good (Q := Q) hsb hsite hi'' ht' with hn' | ⟨d'', hn', hg⟩
        · exact .inl (.inl (hnext.trans (by unfold dispatch; rw [hn]; exact hn')))
        · exact .inl (.inr ⟨d'', t', hnext.trans (by unfold dispatch; rw [hn]; exact hn'), hr,
            hg⟩)
      · exact .inr ⟨hnext.trans (by unfold dispatch; rw [hn]), hd⟩
    · rcases Worker.step hi' h' hc' hf' with (hn | ⟨d', t', hn, hr, ht', hi''⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by rw [next_worker_ne hs, hn]; rfl))
      · exact .inl (.inr ⟨.worker d', t', by rw [next_worker_ne hs, hn]; rfl, hr,
          good_worker ht' hi''⟩)
      · exact .inr ⟨by rw [next_worker_ne hs, hn]; rfl, hd⟩

/-- An idle state. -/
theorem stepAt_idle (d : Worker.Idle.D) : (code L g Q).StepAt (.idle d) where
  site _ := (Worker.Idle.stepAt (L := L) (g := g) d.P d).site trivial
  step := by
    intro t e u ins h hi hc hf
    have h' : At t d.site.pc (Worker.Idle.facts L g d) := h
    have hc' : kernel.code[d.site.pc]? = some ins := hc
    have hf' : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
    by_cases hs : d.site = .inc
    · obtain ⟨site, P⟩ := d
      simp only at hs
      subst hs
      obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_setMaxReg_3)
      obtain rfl := fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf'
      have hn : (code L g Q).next (.idle ⟨.inc, P⟩) e =
          some (some (.worker ⟨.loop, Worker.bumpPro P⟩)) := rfl
      exact .inl (.inr ⟨.worker ⟨.loop, Worker.bumpPro P⟩, _, hn, .refl,
        good_worker (Worker.Idle.return_loop (At.next h')) ⟨hi.1, hi.2.1, hi.2.2.bumpPro⟩⟩)
    · rcases (Worker.Idle.stepAt (g := g) d.P d).step ins h' trivial hc' hf' with
        (hn | ⟨d', t', hn, hr, ht', -⟩) | ⟨hn, hd⟩ <;> change Worker.Idle.next d e = _ at hn
      · exact .inl (.inl (by rw [next_idle_ne hs, hn]; rfl))
      · have hP : d'.P = d.P := by
          obtain ⟨s, P⟩ := d
          cases s <;> simp only [Worker.Idle.next, Option.some.injEq] at hn <;>
            first | (subst hn; rfl) | cases hn
        have hi1 : Inv L g (.idle d) := hi
        exact .inl (.inr ⟨.idle d', t', by rw [next_idle_ne hs, hn]; rfl, hr,
          good_idle ht' ⟨hi1.1, hi1.2.1, hP ▸ hi1.2.2⟩⟩)
      · exact .inr ⟨by rw [next_idle_ne hs, hn]; rfl, hd⟩

/-- A loader state. -/
theorem stepAt_loader (d : Loader.D) (P : Pro) : (code L g Q).StepAt (.loader d P) where
  site hi := Loader.site_ok hi.1
  step := by
    intro t e u ins h hi hc hf
    obtain ⟨hl, hpro, hR, hw, ht⟩ := hi
    have h' : Loader.AtS L g d t := h
    have hc' : kernel.code[d.site.pc]? = some ins := hc
    have hf' : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      obtain ⟨t', hr, ht', hi'⟩ := loader_return
        (d := ⟨.setMaxInc, pro, i, n, p0, p1, ln⟩) rfl hR hpro ⟨hl, hpro, hR, hw, ht⟩
        (Loader.AtS.at h' rfl rfl) hc' hf'
      have hn : (code L g Q).next (.loader ⟨.setMaxInc, pro, i, n, p0, p1, ln⟩ P) e =
          some (some (.worker ⟨.loop, Worker.bumpPro P⟩)) := rfl
      exact .inl (.inr ⟨.worker ⟨.loop, Worker.bumpPro P⟩, t', hn, hr, good_worker ht' hi'⟩)
    · rcases Loader.step hl h' hc' hf' with (hn | ⟨hn, hd⟩) | ⟨d', t', hn, hr, ht', hi'⟩
      · exact .inl (.inl (by rw [next_loader_ne P hs, hn]; rfl))
      · exact .inr ⟨by rw [next_loader_ne P hs, hn]; rfl, hd⟩
      · exact .inl (.inr ⟨.loader d' P, t', by rw [next_loader_ne P hs, hn]; rfl, hr, ht',
          hi', fun r h1 h2 => (loader_next_pro hn r h1 h2).trans (hpro r h1 h2), hR, hw, ht⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.WComp
