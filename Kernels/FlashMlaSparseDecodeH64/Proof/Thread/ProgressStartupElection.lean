-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressMmaElection
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

import Lemmas.Order.ElectOrdinal
import Lemmas.Step.WarpShfl

public section

/-! # The prologue's two full-warp elections -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem election_template {g : Nat} {u : TState} {ins : Instr}
    (second : Bool) (s : Site) (hS : s = (if second then .elect1 else .elect0))
    (ha : (Machine.code P L g).AtD (.prologue s) u)
    (hc : kernel.code[s.pc]? = some ins) :
    ∃ k, eventTmpl Assumptions.all L g u ins.op = .elect (2 ^ 32 - 1) k := by
  subst s
  have hMask : (4294967295#64).toNat = 2 ^ 32 - 1 := by decide +kernel
  cases second
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
    have hr : u.regs 522 = some (b32 4294967295) :=
      holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 522 ∈ liveAll 16))
    have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
    simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits, hMask,
      ite_eq_left (full_member L g)]
    exact ⟨_, rfl⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
    have hr : u.regs 525 = some (b32 4294967295) :=
      holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 525 ∈ liveAll 31))
    have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
    simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits, hMask,
      ite_eq_left (full_member L g)]
    exact ⟨_, rfl⟩

/-- At its prologue election site, the frozen instruction emits a matching full-mask event. -/
theorem startup_election_event {g i : Nat} {e : Event} (second : Bool)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i =
      some (some (.prologue (if second then .elect1 else .elect0)))) :
    ∃ inst leader, e = ⟨(if second then 31 else 16), .elect (2 ^ 32 - 1) inst leader⟩ := by
  obtain ⟨_, _, _, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hState
  obtain ⟨k, hTemplate⟩ := election_template second _ rfl ha hc
  rw [hTemplate] at hf
  obtain ⟨inst, leader, hShape, _⟩ := hf
  refine ⟨inst, leader, hShape.trans ?_⟩
  cases second <;> rfl

/-- The first election always carries warp zero to the second election. -/
theorem startup_election_second {g : Nat} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (hg : warpOf L g = 0) (he : X.get (g, 2) = some e) :
    Frame.stateAt (Machine.code P L) X g 3 = some (some (.prologue .elect1)) := by
  have hLen : 2 < (X.tr g).length := PTX.len_of_get he
  have h1 : 1 < (X.tr g).length := by omega
  have hOne : X.get (g, 1) = some (X.tr g)[1] := List.getElem?_eq_getElem h1
  have hFirst : Frame.stateAt (Machine.code P L) X g 2 = some (some (.prologue .elect0)) := by
    simpa only [hg, ↓reduceIte] using
      PrologueShuffleTrace.state_two hpre hX (fun h hh => (hs h hh).machine) hOne
  obtain ⟨_, _, rfl⟩ := startup_election_event false hX hs he hFirst
  change Frame.stateAt (Machine.code P L) X g (2 + 1) = _
  rw [Frame.stateAt_succ he, hFirst]
  rfl

/-- A warp at one of the two launch elections can append the whole instance. -/
theorem startup_election_extension {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hg : g < L.threads) (second : Bool)
    (hall : ∀ h, SameWarp L g h →
      Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
        Frame.stateAt (Machine.code P L) X h (X.tr h).length =
          some (some (.prologue (if second then .elect1 else .elect0)))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let s : Site := if second then .elect1 else .elect0
  refine full_election_batch (site := s.pc) hX (by rw [hpre.block]) hg
    (fun h hw => .inl (ClosingProgress.nonempty_tail (hall h hw).2.2 (by cases second <;> simp)))
    (fun h hw => (hall h hw).2.1) ?_
  intro h hw
  obtain ⟨hp, _, hState⟩ := hall h hw
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, _, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  obtain ⟨k, hTemplate⟩ := election_template second s rfl ha hc
  rw [hTemplate] at hout
  exact ⟨t, u, k, hRun, hTau, ha.1, hout⟩

private theorem at_two {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hWarp : warpOf L g = 0) (hLen : 2 ≤ (X.tr g).length) :
    Frame.stateAt (Machine.code P L) X g 2 = some (some (.prologue .elect0)) := by
  have h1 : 1 < (X.tr g).length := by omega
  have he : X.get (g, 1) = some (X.tr g)[1] := List.getElem?_eq_getElem h1
  simpa only [hWarp, ↓reduceIte] using
    PrologueShuffleTrace.state_two hpre hX (fun h hh => (hs h hh).machine) he

private theorem election_peer_le {g h : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hw : SameWarp L g h) (hg : warpOf L g = 0) (hh : warpOf L h = 0)
    (hMin : 2 ≤ (X.tr g).length) (hMax : (X.tr g).length ≤ 3) :
    (X.tr h).length ≤ (X.tr g).length := by
  by_contra! hMore
  let j := (X.tr g).length
  obtain ⟨e, he⟩ : ∃ e, X.get (h, j) = some e :=
    ⟨(X.tr h)[j], List.getElem?_eq_getElem hMore⟩
  have hOther : ∃ tag mask inst leader, X.Elect (h, j) tag mask inst leader ∧
      mask = 2 ^ 32 - 1 ∧ (j = 3 → tag = 31) := by
    have hRange : j = 2 ∨ j = 3 := by omega
    rcases hRange with hJ | hJ
    · rw [hJ] at he
      obtain ⟨inst, leader, hShape⟩ := startup_election_event false hX hs he
        (at_two hpre hX hs hh (by omega))
      refine ⟨16, _, inst, leader, ?_, rfl, by omega⟩
      change X.get (h, j) = some _
      rw [hJ]
      rw [hShape] at he
      exact he
    · rw [hJ] at he
      have h2 : 2 < (X.tr h).length := by omega
      have hf : X.get (h, 2) = some (X.tr h)[2] := List.getElem?_eq_getElem h2
      obtain ⟨inst, leader, hShape⟩ := startup_election_event true hX hs he
        (startup_election_second hpre hX hs hh hf)
      refine ⟨31, _, inst, leader, ?_, rfl, fun _ => rfl⟩
      change X.get (h, j) = some _
      rw [hJ]
      rw [hShape] at he
      exact he
  obtain ⟨tag, _, inst, leader, helect, rfl, hTag⟩ := hOther
  have hw' : SameWarp L h g := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  obtain ⟨i, tag', tagG, mask, maskG, x, l, lG, he', hi⟩ :=
    ElectOrd.partner hX hw' helect (full_member L g)
  obtain ⟨rfl, _, _, _⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ he' hi hw'
  obtain rfl : tag' = tag := congrArg Event.pc (Option.some.inj (he'.symm.trans helect))
  have hLt : i < (X.tr g).length := PTX.len_of_get hi
  have hiLt : i < 3 := by omega
  interval_cases i
  · have h := PrologueShuffleTrace.first_event hpre hX (fun z hz => (hs z hz).machine) hi
    cases h
  · have h := PrologueShuffleTrace.second_event hpre hX (fun z hz => (hs z hz).machine) hi
    cases h
  · obtain ⟨_, _, h⟩ := startup_election_event false hX hs hi (at_two hpre hX hs hg hMin)
    have hEq := congrArg Event.pc h
    have hJ : j = 3 := by omega
    have hNe := hTag hJ
    simp [hNe] at hEq

/-- All peers at a pending warp-zero election are at the same event position. -/
theorem startup_election_peers {g : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hg : warpOf L g = 0) (second : Bool)
    (hLen : (X.tr g).length = (if second then 3 else 2)) :
    ∀ h, SameWarp L g h → Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length =
         some (some (.prologue (if second then .elect1 else .elect0))) := by
  intro h hw
  let sound := fun z hz => (hs z hz).machine
  have hh : warpOf L h = 0 := by
    have hWarp : warpOf L h = warpOf L g := by
      simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm
    exact hWarp.trans hg
  have hg2 : 2 ≤ (X.tr g).length := by cases second <;> simp_all
  have hg3 : (X.tr g).length ≤ 3 := by cases second <;> simp_all
  have hUp := election_peer_le hpre hX hs hw hg hh hg2 hg3
  have h1 : 1 < (X.tr g).length := by omega
  have he : X.get (g, 1) = some (X.tr g)[1] := List.getElem?_eq_getElem h1
  have hK := PrologueShuffleTrace.early_shuffle_ordinal hpre hX sound (by decide) he
  obtain ⟨⟨_, _, _, _, _, _, _, he'⟩, _⟩ := id hK
  obtain ⟨i, hi⟩ := (PTX.Step.shfl_lane_of_ready hX he' hK hw).resolve_right
     (PrologueShuffleTrace.not_exited_before_second hpre hX sound)
  have hCount : 1 < (X.tr h).countP Execution.isShfl := PTX.Step.ShflK.lt_count hi
  have hH := List.countP_le_length (p := Execution.isShfl) (l := X.tr h)
  have hw' : SameWarp L h g := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  have hDown := election_peer_le hpre hX hs hw' hh hg (by omega) (by omega)
  have hEq := le_antisymm hUp hDown
  have hLast (e : Event) (he : X.get (h, (X.tr h).length - 1) = some e) :
      e.kind ≠ .exit ∧ e.kind.resume ≠ .blocking false := by
    rw [hEq, hLen] at he
    cases second
    · have h := PrologueShuffleTrace.second_event hpre hX sound he
      rw [h]
      simp [Kind.resume]
    · obtain ⟨_, _, rfl⟩ := startup_election_event false hX hs he
        (at_two hpre hX hs hh (by omega))
      simp [Kind.resume]
  refine ⟨⟨hw.1.2.1, ?_, ?_⟩, .of_get (fun e he => (hLast e he).2), ?_⟩
  · rintro ⟨_, _, hCanceled⟩
    obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
    exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
  · intro tag he
    rw [List.getLast?_eq_getElem?] at he
    exact (hLast _ he).1 rfl
  · rw [hEq, hLen]
    cases second
    · exact at_two hpre hX hs hh (by omega)
    · have h2 : 2 < (X.tr h).length := by simp [hEq, hLen]
      have hf : X.get (h, 2) = some (X.tr h)[2] := List.getElem?_eq_getElem h2
      exact startup_election_second hpre hX hs hh hf


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
