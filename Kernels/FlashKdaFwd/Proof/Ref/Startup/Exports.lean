-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Shfl

@[expose] public section

/-! # Exports of the startup phase: facts about the events of a consistent execution

What the layers above read off the reference invariant of the startup phase (instructions 0 to
387). Every theorem is about one event `X.get (g, k) = some e` of a launched thread whose
machine state before it is `s` (`Frame.stateAt (code L) X g k = some (some s)`), under the
hypotheses of `startup_inv` (the precondition and consistency), and has
two alternatives: the closed form, or `Left P L X g k`: the thread left the startup phase at or
before position `k` (then the event belongs to a later phase, whose exports describe it).

* `event_at`: the event is the closed-form event `Ev` of a position whose register facts and
  ledger hold; it is not undefined behaviour (`noUb_startup`).
* `mbInit_startup`: an `mbarrier.init` event initializes the barrier at shared offset
  `initOff j` of the thread's own block with the count `initCnt j`; the thread is thread 0 of
  its block for the ten pipeline barriers and thread 128 for the state barrier; it has
  performed 0, 1 or 2 `bar.sync 0` (pipeline barriers of the load ring, of the store ring, the
  state barrier) and `j` initializations (0 for the state barrier) before.
* `bar_startup`: a barrier event is `bar.sync 0`, the `j`-th of the thread, at instruction
  85, 110 or 379.
* `arrive_startup`: an arrival is thread 128's first, on the state barrier, expecting 65536
  bytes with count 1, after two `bar.sync 0`.
* `issue_startup`: a tensor load issue is thread 128's `j`-th (`j < 16`), the copy
  `stateSpec P L g j` through the map of the initial state (parameter object 8), after the
  arrival and two `bar.sync 0`.
* `read_startup`: a read is of the eight bytes of an entry `i ≤ N` of the offsets array.
* `wait_startup`: a poll is of the state barrier of the thread's block with parity 0,
  acquiring, after three `bar.sync 0` and no successful poll.
* `scan_head`: the closed form of the registers the scan loop carries, at its head.
* `left_exit`: what holds when the thread has left the phase (the exit state).

Roles (which thread can be where) are the `tid g = …` and `warp g = …` conjuncts; they rest on
what the shuffles return (`Shfl.lean`) and on the assumption `electZero`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The thread that initializes a barrier: thread 0 of its block for the ten pipeline
barriers, thread 128 for the state barrier. -/
theorem init_owner (j : Fin 11) {d : D} (h : AtPos P g (.init j) d) :
    tid g = if j.val < 10 then 0 else 128 := by
  fin_cases j <;> simp only [AtPos, finVal] at h <;> simp [h]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **An event at a state of the phase is the closed-form event of its position.** -/
theorem event_at {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ pos, RefAt P g pos s ∧ ledOf ((X.tr g).take k) = led g pos ∧ Ev P L g pos e) ∨
      Left P L X g k := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases startup_inv hpre hX hg hk hσ with ⟨pos, hr, hl⟩ | h
  · obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = pos.site := hr.site
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    exact .inl ⟨pos, hr, hl, ev_full hpre hg pos hr hat hc hf⟩
  · exact .inr h

/-- **No event of the phase is undefined behaviour.** -/
theorem noUb_startup {k pc : Nat} {f : Fault} {s : D} (he : X.get (g, k) = some ⟨pc, .ub f⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, -, -, hev⟩ | h
  · exact absurd rfl (hev.noUb pc f)
  · exact h

/-- **Every `mbarrier.init` of the phase.** -/
theorem mbInit_startup {k pc n : Nat} {m : Loc} {s : D}
    (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ j : Fin 11, pc = (Site.mbarInit j).pc ∧
        m = ⟨.shared, g / L.block, P.sharedBase + initOff j.val⟩ ∧ n = initCnt j.val ∧
        tid g = (if j.val < 10 then 0 else 128) ∧
        ledOf ((X.tr g).take k) = led g (.init j)) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨rfl, hk⟩ := hev
    cases hk
    exact ⟨j, rfl, rfl, rfl, init_owner j hr.pos, hl⟩
  · exact .inr h

/-- **Every barrier event of the phase** is `bar.sync 0`, at the position of its ordinal. -/
theorem bar_startup {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (id = 0 ∧ cnt = none ∧ mode = .sync ∧ ∃ j : Fin 3, pc = (Pos.bar j).site.pc ∧
        (ledOf ((X.tr g).take k)).bars = j.val) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨rfl, hk⟩ := hev
    cases hk
    refine ⟨rfl, rfl, rfl, j, rfl, ?_⟩
    rw [hl]
    fin_cases j <;> simp [led]
  · exact .inr h

/-- **The arrival on the state barrier**: thread 128's first, expecting 65536 bytes. -/
theorem arrive_startup {k pc tx c : Nat} {m : Loc} {rel : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx c rel sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (pc = 327 ∧ m = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ ∧ tx = 65536 ∧ c = 1 ∧
        rel = true ∧ sc = .cta ∧ tid g = 128 ∧
        ledOf ((X.tr g).take k) = ⟨2, 1, 0, 0, 0, 3⟩) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨rfl, hk⟩ := hev
    cases hk
    have ht : tid g = 128 := by
      have := hr.pos
      simp only [AtPos] at this
      exact this.2.2.2.2.1
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ht, hl⟩
  · exact .inr h

/-- **The sixteen loads of the initial state**: thread 128's; the `j`-th has `j`
predecessors and is the copy `stateSpec P L g j` through the map of parameter object 8. -/
theorem issue_startup {k pc a : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ j : Fin 16, pc = (Pos.copy j).site.pc ∧ a = P.objectBase 8 ∧
        sp = stateSpec P L g j.val ∧ tid g = 128 ∧
        ledOf ((X.tr g).take k) = ⟨2, 1, 1, j.val, 0, 3⟩) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨rfl, hk⟩ := hev
    cases hk
    have ht : tid g = 128 := by
      have := hr.pos
      simp only [AtPos] at this
      exact this.2.2.2.1
    exact ⟨j, rfl, rfl, rfl, ht, hl⟩
  · exact .inr h

/-- **The reads of the phase** are the 21 loads of the offsets array: eight bytes of an entry
`i ≤ N`, at one of the load instructions of the assumption `inputReadOnly`. -/
theorem read_startup {k pc : Nat} {a : Acc} {bs : List (Option Byte)} {s : D}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ i ≤ P.sequences, a = { loc := P.offsetLoc i, size := 8 } ∧ bs.length = 8 ∧
        Assumptions.inputReadSites.contains pc = true) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨i, hi, bs', hl', rfl, hk⟩ := hev
    cases hk
    exact ⟨i, hi, rfl, hl', load_site j⟩
  · exact .inr h

/-- **The poll of the state barrier**: of the thread's own block, parity 0, acquiring, after
three `bar.sync 0` and before any successful poll. -/
theorem wait_startup {k pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (pc = 384 ∧ m = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ ∧ q = 0 ∧ acq = true ∧
        sc = .cta ∧ (ledOf ((X.tr g).take k)).bars = 3 ∧
        (ledOf ((X.tr g).take k)).polls = 0) ∨ Left P L X g k := by
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · refine .inl ?_
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    obtain ⟨ok', rfl, hk⟩ := hev
    cases hk
    exact ⟨rfl, rfl, rfl, rfl, rfl, by rw [hl]; rfl, by rw [hl]; rfl⟩
  · exact .inr h

/-- **The loop head of the scan** (instruction 129, at the load of instruction 131): with `i`
the sequence index the loop has reached, the carried registers are `%r1791 = %r1792 = i`,
`%r1793` = the number of tiles of the sequences before `i`, `%rd1166` = entry `i` of the
offsets array, and the pointer `%rd20 = cu_seqlens + 8 i`. -/
theorem scan_head {k : Nat} {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hs : s.site = .load 3) :
    (∃ i, i % 8 = 0 ∧ i + 8 ≤ seqOf P g ∧ s.w 2097 = W i ∧ s.w 2098 = W i ∧
        s.w 2099 = W (firstTile P.length i) ∧ s.w 3412 = W (firstToken P.length i) ∧
        s.w 2266 = W (P.offsetsBase + 8 * i)) ∨ Left P L X g k := by
  rcases startup_inv hpre hX hg hk hσ with ⟨pos, hr, hl⟩ | h
  · refine .inl ?_
    have hsite := hr.site
    rw [hs] at hsite
    rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Pos.site] at hsite <;>
      try cases hsite
    have hj : j = 3 := Fin.ext (by
      have := congrArg Fin.val (Site.load.inj hsite)
      simpa using this.symm)
    subst hj
    have h := hr.pos
    simp only [AtPos, finVal, Loop8] at h
    obtain ⟨-, -, -, -, i, ⟨h1, h2, -, -, h3, h4⟩, h5, h6, h7⟩ := h
    exact ⟨i, h1, h2, h3, h5, h6, h7, h4⟩
  · exact .inr h

end

/-- **After the phase**: the exit state and its ledger held at an earlier position. -/
theorem left_exit {k : Nat} (h : Left P L X g k) :
    ∃ j ≤ k, ∃ s0, Frame.stateAt (code L) X g j = some (some s0) ∧ Exit P g s0 ∧
      ledOf ((X.tr g).take j) = ledExit g :=
  let ⟨j, hj, s0, h1, h2, h3⟩ := h
  ⟨j, hj, s0, h1, h2, h3⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
