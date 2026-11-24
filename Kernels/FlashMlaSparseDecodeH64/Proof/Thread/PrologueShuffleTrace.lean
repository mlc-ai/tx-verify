-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Shuffle

@[expose] public section

/-! # The two broadcasts at the start of every thread trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueShuffleTrace

open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 10000

private theorem fired_broadcast {L : Launch} {g src dst pred pc value : Nat}
    {t : TState} {e : Event} {o : Option TState}
    (hb : L.block % 32 = 0) (hr : t.regs src = some (b32 value))
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.shfl .idx, some (.int .b 32), [some dst, some pred],
        [.reg src, .imm 0, .imm 31], some (.imm (-1))⟩)) e o) :
    ∃ recv ok, e = ⟨pc, .shfl .idx (b32 value) 0 31 recv ok⟩ := by
  simp only [eventTmpl, warpTmpl_shfl_idx, shflTmpl, readBits, readValue, readReg, hr, b32,
    Value.bytes, hb, pure, Except.pure] at hf
  rw [ite_eq_left (by decide), ite_eq_left trivial,
    show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 by decide,
    show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide] at hf
  obtain ⟨recv, ok, he, _⟩ := hf
  exact ⟨recv, ok, he⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem first_shape (hpre : Pre P L mem0)
    {g : Nat} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.prologue .shfl0)) e o) :
    ∃ recv ok, e = ⟨Site.shfl0.pc, .shfl .idx (b32 (wgOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change At t Site.shfl0.pc (facts L g .shfl0) at hat
  change Fires t.pc (match kernel.code[Site.shfl0.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hat.1, show Site.shfl0.pc = 6 from rfl, Flow.code_shfl_0] at hf
  have hr : t.regs 519 = some (b32 (wgOf L g)) :=
    holds_mem hat.2.2.2.2
      (mem_factsFrom (val := valueOf L g) (by table_decide : (519 : Nat) ∈ liveAll 6))
  exact fired_broadcast (by rw [hpre.block]) hr hf

private theorem second_shape (hpre : Pre P L mem0)
    {g : Nat} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.prologue .shfl1)) e o) :
    ∃ recv ok, e = ⟨Site.shfl1.pc, .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change At t Site.shfl1.pc (facts L g .shfl1) at hat
  change Fires t.pc (match kernel.code[Site.shfl1.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hat.1, show Site.shfl1.pc = 9 from rfl, Flow.code_shfl_1] at hf
  have hr : t.regs 464 = some (b32 (warpOf L g)) :=
    holds_mem hat.2.2.2.2
      (mem_factsFrom (val := valueOf L g) (by table_decide : (464 : Nat) ∈ liveAll 9))
  exact fired_broadcast (by rw [hpre.block]) hr hf

private theorem sameWarp_warp (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) :
    warpOf L h = warpOf L g := by
  have heq := hw.2.symm
  simpa only [warpOf, tidOf_eq hpre, hpre.block] using heq

private theorem sameWarp_wg (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) :
    wgOf L h = wgOf L g := by
  have heq := congrArg (· / 4) (sameWarp_warp hpre hw)
  simpa only [warpOf, wgOf, Nat.div_div_eq_div_mul] using heq

private theorem first_shape_at (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    {g : Nat} {e : Event} (he : X.get (g, 0) = some e) :
    ∃ recv ok, e = ⟨Site.shfl0.pc, .shfl .idx (b32 (wgOf L g)) 0 31 recv ok⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := ((hs g hg).produces (hX.thr g hg)).fired_at he
    (Frame.stateAt_zero (C := Machine.code P L) (X := X) (g := g))
  exact first_shape hpre hf

private theorem earlier {g i j : Nat} {e : Event} (he : X.get (g, i) = some e) (hj : j ≤ i) :
    ∃ f, X.get (g, j) = some f := by
  have hlen : i < (X.tr g).length := PTX.len_of_get he
  change ∃ f, (X.tr g)[j]? = some f
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

private theorem shfl_count_succ {g k pc : Nat} {m : ShflMode} {a recv : Value} {b c : Nat}
    {ok : Bool} (he : X.get (g, k) = some ⟨pc, .shfl m a b c recv ok⟩) :
    ((X.tr g).take (k + 1)).countP Execution.isShfl =
      ((X.tr g).take k).countP Execution.isShfl + 1 := by
  rw [List.take_add_one, show (X.tr g)[k]? = _ from he, Option.toList_some,
    List.countP_append]
  rfl

private theorem shfl_count_mono {g i j : Nat} (h : i ≤ j) :
    ((X.tr g).take i).countP Execution.isShfl ≤ ((X.tr g).take j).countP Execution.isShfl :=
  (List.take_isPrefix_take.mpr (Or.inl h)).countP_le

private theorem broadcast_value (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) {g i n pc : Nat}
    {a recv : Value} {ok : Bool} {v : Nat → Value}
    (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .shfl .idx a 0 31 recv ok⟩)
    (hk : X.ShflK (g, i) n)
    (hwarp : ∀ h, SameWarp L g h → v h = v g)
    (hpeer : ∀ h, SameWarp L g h → ∀ j pc' b' c' r' o',
      X.ShflK (h, j) n → X.get (h, j) = some ⟨pc', .shfl .idx recv b' c' r' o'⟩ →
      recv = v h)
    (hexit : ∀ h, SameWarp L g h → ¬ ShflExited X h n) :
    recv = v g ∧ ok = true := by
  obtain ⟨hok, hs⟩ := hX.shfl g i n pc .idx a 0 31 recv ok he hk
  have hz : shflSource .idx (PTX.laneOf L g) 0 31 = (0, true) := by simp [shflSource]
  rw [hz] at hok hs
  simp only [Nat.add_zero] at hs
  obtain ⟨hw, _⟩ := laneZero_sameWarp (by rw [hpre.block]; decide) hg
  rcases hs with ⟨j, pc', b', c', r', o', hj, he'⟩ | hx
  · exact ⟨(hpeer _ hw j pc' b' c' r' o' hj he').trans (hwarp _ hw), hok⟩
  · exact (hexit _ hw hx).elim

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
include hpre hX hs

/-- The first broadcast returns the launched thread's own warpgroup index. -/
theorem first_event {g : Nat} {e : Event} (he : X.get (g, 0) = some e) :
    e = ⟨Site.shfl0.pc, .shfl .idx (b32 (wgOf L g)) 0 31 (b32 (wgOf L g)) true⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨recv, ok, rfl⟩ := first_shape_at hpre hX hs he
  obtain ⟨rfl, rfl⟩ := first_shfl_value hX (by rw [hpre.block]; decide)
    (fun _ _ _ hf => first_shape_at hpre hX hs hf)
    (fun _ _ hw => congrArg b32 (sameWarp_wg hpre hw)) hg he
  rfl

/-- After the first broadcast, the thread machine has reached the second broadcast. -/
theorem state_one {g : Nat} {e : Event} (he : X.get (g, 0) = some e) :
    Frame.stateAt (Machine.code P L) X g 1 = some (some (.prologue .shfl1)) := by
  have he' := first_event hpre hX hs he
  rw [Frame.stateAt_succ he, Frame.stateAt_zero, he']
  simp [Machine.code, Code.toMachine, Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next,
    b32]

private theorem second_shape_at {g : Nat} {e : Event} (he : X.get (g, 1) = some e) :
    ∃ recv ok, e = ⟨Site.shfl1.pc, .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨f, hf⟩ := earlier he (show 0 ≤ 1 by decide)
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hfired⟩ := ((hs g hg).produces (hX.thr g hg)).fired_at he (state_one hpre hX hs hf)
  exact second_shape hpre hfired

private theorem second_ordinal {g : Nat} {e : Event} (he : X.get (g, 1) = some e)
    : X.ShflK (g, 1) 1 := by
  obtain ⟨f, hf⟩ := earlier he (show 0 ≤ 1 by decide)
  obtain ⟨a, p, rfl⟩ := first_shape_at hpre hX hs hf
  obtain ⟨b, q, rfl⟩ := second_shape_at hpre hX hs he
  exact ⟨⟨_, _, _, _, _, _, _, he⟩, shfl_count_succ hf⟩

/-- Either of the common broadcast positions carries the corresponding shuffle ordinal. -/
theorem early_shuffle_ordinal {g n : Nat} {e : Event} (hn : n ≤ 1) (he : X.get (g, n) = some e) :
    X.ShflK (g, n) n := by
  rcases n with _ | n
  · obtain ⟨recv, ok, rfl⟩ := first_shape_at hpre hX hs he
    exact ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  · obtain rfl : n = 0 := by omega
    exact second_ordinal hpre hX hs he

theorem not_exited_before_second {g : Nat} : ¬ ShflExited X g 1 := by
  rintro ⟨k, pc, he, hcount⟩
  have hk0 : 0 < k := by
    by_contra hle
    have hzero : k = 0 := by omega
    subst k
    obtain ⟨_, _, he⟩ := first_shape_at hpre hX hs he
    cases he
  have hk1 : 1 < k := by
    by_contra hle
    have hone : k = 1 := by omega
    subst k
    obtain ⟨_, _, he⟩ := second_shape_at hpre hX hs he
    cases he
  obtain ⟨f, hf⟩ := earlier he (show 1 ≤ k by omega)
  have hn : ((X.tr g).take 1).countP Execution.isShfl = 1 := (second_ordinal hpre hX hs hf).2
  obtain ⟨_, _, rfl⟩ := second_shape_at hpre hX hs hf
  have htwo : ((X.tr g).take 2).countP Execution.isShfl = 2 := by
    rw [show (2 : Nat) = 1 + 1 by decide, shfl_count_succ hf, hn]
  have hm := shfl_count_mono (X := X) (g := g) (show 2 ≤ k by omega)
  rw [htwo] at hm
  omega

/-- The second broadcast returns the launched thread's own warp index. -/
theorem second_event {g : Nat} {e : Event} (he : X.get (g, 1) = some e) :
    e = ⟨Site.shfl1.pc, .shfl .idx (b32 (warpOf L g)) 0 31 (b32 (warpOf L g)) true⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨recv, ok, rfl⟩ := second_shape_at hpre hX hs he
  have nth : ∀ h < L.threads, ∀ i pc m a b c r o, X.ShflK (h, i) 1 →
      X.get (h, i) = some ⟨pc, .shfl m a b c r o⟩ → a = b32 (warpOf L h) := by
    intro h _ i pc m a b c r o hi he'
    have hlen : 1 ≤ i :=
      hi.2.symm.le.trans (List.countP_le_length.trans (List.length_take_le _ _))
    obtain ⟨f, hf⟩ := earlier he' hlen
    have hi1 := shfl_index_unique hi (second_ordinal hpre hX hs hf)
    subst i
    obtain ⟨_, _, h⟩ := second_shape_at hpre hX hs he'
    exact (Kind.shfl.inj (congrArg Event.kind h)).2.1
  obtain ⟨rfl, rfl⟩ := nth_shfl_value hX (by rw [hpre.block]; decide) nth
    (fun _ _ hw => congrArg b32 (sameWarp_warp hpre hw))
    (fun _ _ => not_exited_before_second hpre hX hs) hg he (second_ordinal hpre hX hs he)
  rfl

/-- The next state is warp zero's first election or the other warps' CTA barrier. -/
theorem state_two {g : Nat} {e : Event} (he : X.get (g, 1) = some e) :
    Frame.stateAt (Machine.code P L) X g 2 =
      some (some (.prologue (if warpOf L g = 0 then .elect0 else .barrier))) := by
  obtain ⟨f, hf⟩ := earlier he (show 0 ≤ 1 by decide)
  rw [show (2 : Nat) = 1 + 1 by decide, Frame.stateAt_succ he, state_one hpre hX hs hf,
    second_event hpre hX hs he]
  simp [Machine.code, Code.toMachine, Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next,
    b32]

omit hpre hX hs in
private theorem warp_nonzero_of_wg1 {g : Nat} (hgroup : wgOf L g = 1) :
    warpOf L g ≠ 0 := by
  unfold wgOf at hgroup
  unfold warpOf
  omega

private theorem before_group_one_gate {g : Nat} {e : Event} (he : X.get (g, 1) = some e)
    (hgroup : wgOf L g = 1) :
    Frame.stateAt (Machine.code P L) X g 2 = some (some (.prologue .barrier)) := by
  simpa only [warp_nonzero_of_wg1 hgroup, ↓reduceIte] using state_two hpre hX hs he

/-- Warpgroup one reaches its register-count hand-off after its CTA barrier. -/
theorem state_three {g : Nat} {e : Event} (he : X.get (g, 2) = some e) (hgroup : wgOf L g = 1) :
    Frame.stateAt (Machine.code P L) X g 3 = some (some (.prologue (.handoff 1))) := by
  obtain ⟨f, hf⟩ := earlier he (show 1 ≤ 2 by decide)
  change Frame.stateAt (Machine.code P L) X g (2 + 1) = _
  rw [Frame.stateAt_succ he, before_group_one_gate hpre hX hs hf hgroup]
  simp [Machine.code, Code.toMachine, Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next,
    hgroup]

/-- After its hand-off, warpgroup one reaches its warp-index broadcast. -/
theorem state_four {g : Nat} {e : Event} (he : X.get (g, 3) = some e) (hgroup : wgOf L g = 1) :
    Frame.stateAt (Machine.code P L) X g 4 = some (some .head) := by
  obtain ⟨f, hf⟩ := earlier he (show 2 ≤ 3 by decide)
  rw [show (4 : Nat) = 3 + 1 by decide, Frame.stateAt_succ he,
    state_three hpre hX hs hf hgroup]
  simp [Machine.code, Code.toMachine, Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next,
    hgroup, Machine.roleStart]

private theorem group_one_gate_event {g : Nat} {e : Event} (he : X.get (g, 2) = some e)
    (hgroup : wgOf L g = 1) :
    e = ⟨Site.barrier.pc, .bar 0 none .sync⟩ := by
  obtain ⟨f, hf⟩ := earlier he (show 1 ≤ 2 by decide)
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, t, ⟨hat, _⟩, hfired⟩ := ((hs g hg).produces (hX.thr g hg)).fired_at he
    (before_group_one_gate hpre hX hs hf hgroup)
  have hpc : t.pc = Site.barrier.pc := hat.1
  change Fires t.pc (match kernel.code[97]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hfired
  rw [hpc, Flow.code_bar_0] at hfired
  exact hfired.1

private theorem group_one_handoff_event {g : Nat} {e : Event} (he : X.get (g, 3) = some e)
    (hgroup : wgOf L g = 1) :
    ∃ inst, e = ⟨(Site.handoff 1).pc, .setMaxReg false 72 inst⟩ := by
  obtain ⟨f, hf⟩ := earlier he (show 2 ≤ 3 by decide)
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, t, ⟨hat, _⟩, hfired⟩ := ((hs g hg).produces (hX.thr g hg)).fired_at he
    (state_three hpre hX hs hf hgroup)
  have hpc : t.pc = (Site.handoff 1).pc := hat.1
  change Fires t.pc (match kernel.code[1842]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hfired
  rw [hpc, Flow.code_setMaxReg_1] at hfired
  have hf : ∃ inst, e = ⟨(Site.handoff 1).pc, .setMaxReg false 72 inst⟩ ∧
      o = some (PTX.next t) := hfired
  obtain ⟨inst, heq, _⟩ := hf
  exact ⟨inst, heq⟩

private theorem head_shape_at {g : Nat} {e : Event} (he : X.get (g, 4) = some e)
    (hgroup : wgOf L g = 1) :
    ∃ recv ok, e = ⟨1843, .shfl .idx (b32 (warpOf L g)) 0 31 recv ok⟩ := by
  obtain ⟨f, hf⟩ := earlier he (show 3 ≤ 4 by decide)
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, t, ⟨hat, _⟩, hfired⟩ := ((hs g hg).produces (hX.thr g hg)).fired_at he
    (state_four hpre hX hs hf hgroup)
  change At t 1843 (Wg1Mma.facts P L g Wg1Mma.init) at hat
  change Fires t.pc (match kernel.code[1843]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hfired
  rw [hat.1, Flow.code_shfl_2] at hfired
  have htm := Wg1Mma.event_head P L g hat (by rw [hpre.block])
  change Fires 1843 (eventTmpl Wg1Mma.asms L g t
    (.warp ⟨.shfl .idx, some (.int .b 32), [some 558, some 10],
      [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩)) e o at hfired
  rw [htm] at hfired
  obtain ⟨recv, ok, heq, _⟩ := hfired
  exact ⟨recv, ok, heq⟩

/-- The completed prologue prefix of warpgroup one contains exactly two broadcasts. -/
theorem head_prefix_count {g : Nat} {e : Event} (he : X.get (g, 3) = some e) (hgroup : wgOf L g = 1)
    :
    ((X.tr g).take 4).countP Execution.isShfl = 2 := by
  obtain ⟨f, hf⟩ := earlier he (show 1 ≤ 3 by decide)
  obtain ⟨b, hb⟩ := earlier he (show 2 ≤ 3 by decide)
  have hfirst : ((X.tr g).take 1).countP Execution.isShfl = 1 := (second_ordinal hpre hX hs hf).2
  obtain ⟨_, _, rfl⟩ := second_shape_at hpre hX hs hf
  obtain rfl := group_one_gate_event hpre hX hs hb hgroup
  obtain ⟨_, rfl⟩ := group_one_handoff_event hpre hX hs he hgroup
  have htwo : ((X.tr g).take 2).countP Execution.isShfl = 2 := by
    rw [show (2 : Nat) = 1 + 1 by decide, shfl_count_succ hf, hfirst]
  change ((X.tr g).take (3 + 1)).countP Execution.isShfl = 2
  rw [List.take_add_one, show (X.tr g)[3]? = _ from he, Option.toList_some, List.countP_append]
  have hthree : ((X.tr g).take (2 + 1)).countP Execution.isShfl = 2 := by
    rw [List.take_add_one, show (X.tr g)[2]? = _ from hb, Option.toList_some,
      List.countP_append, htwo]
    rfl
  rw [hthree]
  rfl

/-- The dispatch broadcast is the third shuffle of a warpgroup-one thread. -/
theorem head_ordinal {g : Nat} {e : Event} (he : X.get (g, 4) = some e) (hgroup : wgOf L g = 1) :
    X.ShflK (g, 4) 2 := by
  obtain ⟨f, hf⟩ := earlier he (show 3 ≤ 4 by decide)
  obtain ⟨_, _, rfl⟩ := head_shape_at hpre hX hs he hgroup
  exact ⟨⟨_, _, _, _, _, _, _, he⟩, head_prefix_count hpre hX hs hf hgroup⟩

/-- A warpgroup-one lane before the dispatch broadcast still has a live role. -/
theorem dispatch_prefix_pending {g : Nat} (hg : g < L.threads) (hgroup : wgOf L g = 1)
    (hLen : (X.tr g).length ≤ 4) (hNoClc : ∀ i s tg, ¬ X.ClcIssue i s tg) :
    Frame.Pending L X g := by
  refine ⟨hg, ?_, ?_⟩
  · rintro ⟨_, _, hCanceled⟩
    obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
    exact hNoClc i sp targets hi
  · intro tag hLast
    rw [List.getLast?_eq_getElem?] at hLast
    generalize hi : (X.tr g).length - 1 = i at hLast
    have hPos := (List.getElem?_eq_some_iff.mp hLast).1
    have hiLt : i < 4 := by omega
    interval_cases i
    · obtain ⟨_, _, h⟩ := first_shape_at hpre hX hs hLast
      cases h
    · obtain ⟨_, _, h⟩ := second_shape_at hpre hX hs hLast
      cases h
    · cases group_one_gate_event hpre hX hs hLast hgroup
    · obtain ⟨_, h⟩ := group_one_handoff_event hpre hX hs hLast hgroup
      cases h

/-- Before dispatch, a lane is at one of the prologue sites or at the register request return. -/
theorem dispatch_prefix_tail {g : Nat} (hgroup : wgOf L g = 1) (hLen : (X.tr g).length ≤ 4) :
    (∃ s, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.prologue s))) ∨
    (Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some .head) ∧
      ∃ tag inc n inst, SetMaxNReg.Request X (g, (X.tr g).length - 1) tag inc n inst) := by
  have get (j : Nat) (hj : j < (X.tr g).length) : ∃ e, X.get (g, j) = some e :=
    ⟨(X.tr g)[j], List.getElem?_eq_getElem hj⟩
  generalize he : (X.tr g).length = i at hLen ⊢
  interval_cases i
  · exact .inl ⟨.shfl0, Frame.stateAt_zero⟩
  · obtain ⟨e, he'⟩ := get 0 (by omega)
    exact .inl ⟨.shfl1, state_one hpre hX hs he'⟩
  · obtain ⟨e, he'⟩ := get 1 (by omega)
    exact .inl ⟨.barrier, before_group_one_gate hpre hX hs he' hgroup⟩
  · obtain ⟨e, he'⟩ := get 2 (by omega)
    exact .inl ⟨.handoff 1, state_three hpre hX hs he' hgroup⟩
  · obtain ⟨e, he'⟩ := get 3 (by omega)
    obtain ⟨j, rfl⟩ := group_one_handoff_event hpre hX hs he' hgroup
    exact .inr ⟨state_four hpre hX hs he' hgroup, _, _, _, j, he'⟩

private theorem not_exited_before_head {g : Nat} (hgroup : wgOf L g = 1) : ¬ ShflExited X g 2 := by
  rintro ⟨k, pc, he, hcount⟩
  by_cases hk : k ≤ 4
  · interval_cases k
    · obtain ⟨_, _, h⟩ := first_shape_at hpre hX hs he
      cases h
    · obtain ⟨_, _, h⟩ := second_shape_at hpre hX hs he
      cases h
    · have h := group_one_gate_event hpre hX hs he hgroup
      cases h
    · obtain ⟨_, h⟩ := group_one_handoff_event hpre hX hs he hgroup
      cases h
    · obtain ⟨_, _, h⟩ := head_shape_at hpre hX hs he hgroup
      cases h
  · obtain ⟨f, hf⟩ := earlier he (show 4 ≤ k by omega)
    have htwo : ((X.tr g).take 4).countP Execution.isShfl = 2 :=
      (head_ordinal hpre hX hs hf hgroup).2
    obtain ⟨_, _, rfl⟩ := head_shape_at hpre hX hs hf hgroup
    have hm := shfl_count_mono (X := X) (g := g) (show 4 + 1 ≤ k by omega)
    rw [shfl_count_succ hf, htwo] at hm
    omega

/-- Warpgroup one's third broadcast returns its own warp index and a valid source. -/
theorem head_event {g : Nat} {e : Event} (he : X.get (g, 4) = some e) (hgroup : wgOf L g = 1) :
    e = ⟨1843, .shfl .idx (b32 (warpOf L g)) 0 31 (b32 (warpOf L g)) true⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨recv, ok, rfl⟩ := head_shape_at hpre hX hs he hgroup
  have hrecv : recv = b32 (warpOf L g) ∧ ok = true := by
    refine broadcast_value hpre hX hg he (head_ordinal hpre hX hs he hgroup)
      (v := fun h => b32 (warpOf L h)) (fun _ hw => congrArg b32 (sameWarp_warp hpre hw)) ?_ ?_
    · intro h hw j pc b c r o hj he'
      have hwg := (sameWarp_wg hpre hw).trans hgroup
      have hlen : 2 ≤ j :=
        hj.2.symm.le.trans (List.countP_le_length.trans (List.length_take_le _ _))
      have hge : 4 ≤ j := by
        by_contra! hn
        interval_cases j
        · cases group_one_gate_event hpre hX hs he' hwg
        · obtain ⟨_, h⟩ := group_one_handoff_event hpre hX hs he' hwg
          cases h
      obtain ⟨f, hf⟩ := earlier he' hge
      have hj4 := shfl_index_unique hj (head_ordinal hpre hX hs hf hwg)
      subst j
      obtain ⟨_, _, h⟩ := head_shape_at hpre hX hs he' hwg
      exact (Kind.shfl.inj (congrArg Event.kind h)).2.1
    · intro h hw
      exact not_exited_before_head hpre hX hs ((sameWarp_wg hpre hw).trans hgroup)
  obtain ⟨rfl, rfl⟩ := hrecv
  rfl

/-- Warpgroup one's broadcast dispatches the thread to its actual warp's role. -/
theorem state_five {g : Nat} {e : Event} (he : X.get (g, 4) = some e) (hgroup : wgOf L g = 1) :
    Frame.stateAt (Machine.code P L) X g 5 = some (Machine.headStart P L g) := by
  obtain ⟨f, hf⟩ := earlier he (show 3 ≤ 4 by decide)
  rw [show (5 : Nat) = 4 + 1 by decide, Frame.stateAt_succ he,
    state_four hpre hX hs hf hgroup, head_event hpre hX hs he hgroup]
  simp only [Option.bind_some, Code.toMachine, Machine.code, Machine.next, and_self,
    ↓reduceIte]
  cases Machine.headStart P L g <;> rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueShuffleTrace
