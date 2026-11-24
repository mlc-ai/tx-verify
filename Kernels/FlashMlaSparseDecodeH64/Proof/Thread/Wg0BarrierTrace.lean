-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue

@[expose] public section

/-! # Sources of the softmax warpgroup's named barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0BarrierTrace

open PTX PTX.Proof PTX.Flow

/-- Only these sites use the softmax warpgroup's 128-thread barrier. -/
def Bar9Site : Wg0.Site → Prop
  | .wg0Sync | .wg0Sync2 | .lseBar | .lseBar2 | .epiBar _ => True
  | _ => False

private theorem barId_eq {L : Launch} {g pc ra rc value id : Nat} {aligned : Bool}
    {t : TState} {e : Event} {o : Option TState} {count : Option Nat} {mode : BarMode}
    (hr : t.regs ra = some (b32 value)) (hbound : value < 16)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.barSyncN (.reg ra) (.reg rc) aligned)) e o) (hk : e.kind = .bar id count mode) :
    id = value := by
  have hr := readBits_b32 (L := L) (g := g) hr (by omega)
  have hval : (BitVec.ofNat 64 value).toNat = value := by simp; omega
  simp only [eventTmpl, barTmpl, hr, hval, show ¬ 16 ≤ value by omega, ↓reduceIte] at hf
  cases hc : readBits L g t 32 (.reg rc) with
  | error f =>
    rw [hc] at hf
    rw [congrArg Event.kind hf.1] at hk
    cases hk
  | ok v =>
    rw [hc] at hf
    dsimp only at hf
    split at hf
    · exact (Kind.bar.inj (hk.symm.trans (congrArg Event.kind hf.1))).1
    · rw [congrArg Event.kind hf.1] at hk
      cases hk

private theorem bar_regs_template {L : Launch} {g rId rCount id n : Nat}
    {t : TState} {aligned : Bool}
    (hId : t.regs rId = some (b32 id)) (hCount : t.regs rCount = some (b32 n))
    (hi : id < 16) (hn : n < 2 ^ 31) (h32 : n % 32 = 0) (hne : n ≠ 0)
    (hblock : n ≠ L.block) :
    eventTmpl Assumptions.all L g t (.barSyncN (.reg rId) (.reg rCount) aligned) =
      .bar id (PTX.next t) (some n) .sync := by
  have ha := readBits_b32 (L := L) (g := g) hId (by omega)
  have hb := readBits_b32 (L := L) (g := g) hCount (by omega)
  have hId' : (BitVec.ofNat 64 id).toNat = id := by simp; omega
  have hCount' : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  simp only [eventTmpl, barTmpl, ha, hb, hId', hCount', show ¬ 16 ≤ id by omega,
    ↓reduceIte, h32, hne, hblock, or_self, ne_eq, not_false_eq_true, implies_true, and_self]

variable {P : Params} {L : Launch}

/-- Every softmax barrier-9 instruction has its exact 128-participant template. -/
theorem bar9_template {mem0 : Mem0} {g : Nat} {d : Wg0.D} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (ha : (Wg0.code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hsite : Bar9Site d.site) :
    eventTmpl Assumptions.all L g t ins.op = .bar 9 (PTX.next t) (some 128) .sync := by
  have named {rId rCount : Nat} {aligned : Bool}
      (hr : t.regs rId = some (b32 9)) (hn : t.regs rCount = some (b32 128)) :
      eventTmpl Assumptions.all L g t (.barSyncN (.reg rId) (.reg rCount) aligned) =
        .bar 9 (PTX.next t) (some 128) .sync :=
    bar_regs_template hr hn (by decide) (by decide) (by decide) (by decide)
      (by rw [hpre.block]; decide)
  cases hs : d.site <;> simp [Bar9Site, hs] at hsite
  case wg0Sync =>
    have hpc : d.site.pc = 256 := by rw [hs]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    exact named (Wg0.reg_value ha (r := 972) (by rw [hpc]; decide +kernel))
      (Wg0.reg_value ha (r := 973) (by rw [hpc]; decide +kernel))
  case wg0Sync2 =>
    have hpc : d.site.pc = 569 := by rw [hs]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_3)
    exact named (Wg0.reg_value ha (r := 998) (by rw [hpc]; decide +kernel))
      (Wg0.reg_value ha (r := 999) (by rw [hpc]; decide +kernel))
  case lseBar =>
    have hpc : d.site.pc = 1154 := by rw [hs]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_4)
    exact named (Wg0.reg_value ha (r := 1725) (by rw [hpc]; decide +kernel))
      (Wg0.reg_value ha (r := 1726) (by rw [hpc]; decide +kernel))
  case lseBar2 =>
    have hpc : d.site.pc = 1156 := by rw [hs]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_5)
    exact named (Wg0.reg_value ha (r := 1725) (by rw [hpc]; decide +kernel))
      (Wg0.reg_value ha (r := 1726) (by rw [hpc]; decide +kernel))
  case epiBar j =>
    rw [hs] at hc
    have he : kernel.code[(Wg0.Site.epiBar j).pc]? = some ⟨none, Wg0.epiBarOp j⟩ := by
      fin_cases j
      · exact Flow.code_bar_6
      · exact Flow.code_bar_7
      · exact Flow.code_bar_8
      · exact Flow.code_bar_9
    obtain rfl := Option.some.inj (hc.symm.trans he)
    exact Wg0.event_epiBar hpre ha hs

/-- The peer barrier targets the current pair of warps with 64 participants. -/
theorem pair_bar_template {mem0 : Mem0} {g : Nat} {d : Wg0.D} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (ha : (Wg0.code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hd : d.site = .pairBar) :
    eventTmpl Assumptions.all L g t ins.op =
      .bar (10 + warpOf L g % 2) (PTX.next t) (some 64) .sync := by
  have hpc : d.site.pc = 475 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_2)
  have hr : t.regs 996 = some (b32 (10 + warpOf L g % 2)) :=
    Wg0.reg_value ha (by rw [hpc]; decide +kernel)
  have hn : t.regs 997 = some (b32 64) :=
    Wg0.reg_value ha (by rw [hpc]; decide +kernel)
  exact bar_regs_template hr hn (by omega) (by decide) (by decide) (by decide)
    (by rw [hpre.block]; decide)

/-- Firing any softmax barrier-9 site produces the same named barrier event. -/
theorem bar9_kind {mem0 : Mem0} {g : Nat} {d : Wg0.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hsite : Bar9Site d.site) : e.kind = .bar 9 (some 128) .sync := by
  obtain ⟨t, ⟨ha, _⟩, hFire⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hFire
  cases hCode : kernel.code[d.site.pc]? with
  | none =>
    obtain ⟨ins, hValid, _, _⟩ := Wg0.site_event P L g d
    change kernel.code[d.site.pc]? = some ins at hValid
    rw [hCode] at hValid
    cases hValid
  | some ins =>
    rw [hCode] at hFire
    change Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e o at hFire
    rw [bar9_template hpre ha hCode hsite] at hFire
    exact congrArg Event.kind hFire.1

/-- The actual arrivals of named barrier 9 come from softmax warpgroup states and use its
128-thread sync operand. -/
theorem bar9_fired {mem0 : Mem0} {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {count : Option Nat} {mode : BarMode} (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .bar 9 count mode) :
    ∃ q, d = .wg0 q ∧ Bar9Site q.site ∧ warpOf L g < 4 ∧ count = some 128 ∧ mode = .sync := by
  have hs := RingGateEvents.bar_site hf hk
  cases d
  case prologue q =>
    change q = .barrier at hs
    subst q
    obtain ⟨_, _, hfire⟩ := RingGateEvents.fired_at_code hf Flow.code_bar_0
    have he := (Kind.bar.inj (hk.symm.trans (congrArg Event.kind hfire.1))).1
    change (9 : Nat) = 0 at he
    cases he
  case wg0 q =>
    have hi : Wg0.Inv P L g q := (Exists.choose_spec hf).1.2
    have finish (hq : Bar9Site q.site) (he : e.kind = .bar 9 (some 128) .sync) :
        ∃ q', Machine.ThreadD.wg0 q = .wg0 q' ∧ Bar9Site q'.site ∧
          warpOf L g < 4 ∧ count = some 128 ∧ mode = .sync :=
      ⟨q, rfl, hq, hi.warpLt, (Kind.bar.inj (hk.symm.trans he)).2⟩
    rcases hs with hs | hs | hs | hs | hs | hs | ⟨j, hs⟩
    · exact finish (by rw [hs]; trivial) (bar9_kind hpre hf (by rw [hs]; trivial))
    · have hpc : q.site.pc = 475 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_2)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 996 = some (b32 (10 + warpOf L g % 2)) :=
        Wg0.reg_value hat (r := 996) (by rw [hpc]; decide +kernel)
      have he := barId_eq hr (by omega) hfire hk
      omega
    · exact finish (by rw [hs]; trivial) (bar9_kind hpre hf (by rw [hs]; trivial))
    · exact finish (by rw [hs]; trivial) (bar9_kind hpre hf (by rw [hs]; trivial))
    · exact finish (by rw [hs]; trivial) (bar9_kind hpre hf (by rw [hs]; trivial))
    · have hpc : q.site.pc = 1835 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_10)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 2425 = some (b32 12) :=
        Wg0.reg_value hat (r := 2425) (by rw [hpc]; decide +kernel)
      have he := barId_eq hr (by decide) hfire hk
      cases he
    · exact finish (by rw [hs]; trivial) (bar9_kind hpre hf (by rw [hs]; trivial))
  case mma q =>
    have hpc : q.site.pc = 2160 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_11)
    change (Wg1Mma.code P L g).AtD q t at hat
    have hr : t.regs 918 = some (b32 12) :=
      Wg1Mma.atD_reg hat (r := 918) hpc (by decide +kernel)
    cases barId_eq hr (by decide) hfire hk
  case tma q =>
    have hpc : q.site.pc = 2330 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_12)
    change (Wg1Tma.code P L g).AtD q t at hat
    have hr : t.regs 790 = some (b32 12) :=
      Wg1Tma.atD_regAt hat hpc (by decide +kernel)
    cases barId_eq hr (by decide) hfire hk
  case index q =>
    have hpc : q.site.pc = 2585 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_13)
    change (Wg1Index.code P L g).AtD q t at hat
    have hr : t.regs 659 = some (b32 12) :=
      Wg1Index.AtD.reg hat (r := 659) (by rw [hpc]; decide +kernel)
    cases barId_eq hr (by decide) hfire hk
  case idle q =>
    have hpc : q.pc = 2604 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.pc]? = some _
      simpa only [hpc] using Flow.code_bar_14)
    change (Thread.code L g).AtD q t at hat
    have hm : Holds t.regs (Thread.facts L g q) := hat.2.2.2.2
    change q = .sync at hs
    rw [hs] at hm
    have hr : t.regs 923 = some (b32 12) :=
      holds_mem hm (mem_factsFrom (val := Thread.valueOf L g) (by decide +kernel))
    cases barId_eq hr (by decide) hfire hk
  case wg2 q =>
    have hpc : q.site.pc = 3610 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_15)
    change (Wg2.code P L g).AtD q t at hat
    have hr : t.regs 2878 = some (b32 12) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    cases barId_eq hr (by decide) hfire hk
  all_goals exact hs.elim

/-- A barrier-9 event in a consistent trace fixes the role state and the sync operand. -/
theorem bar9_at {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event} {count : Option Nat}
    {mode : BarMode} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, k) = some e) (hk : e.kind = .bar 9 count mode) :
    ∃ q, Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 q)) ∧
      Bar9Site q.site ∧ warpOf L g < 4 ∧ count = some 128 ∧ mode = .sync := by
  have hg := Frame.lt_of_get hX he
  rcases (hs.produces (hX.thr g hg)).fired he with
    ⟨state, o, hstate, hfired⟩ | ⟨_, _, _, hbad⟩
  · cases state with
    | none => exact ((ht g k hg) hstate).elim
    | some d =>
      obtain ⟨q, rfl, hq, hw, hc, hm⟩ := bar9_fired hpre hfired hk
      exact ⟨q, hstate, hq, hw, hc, hm⟩
  · rw [hbad] at hk
    cases hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0BarrierTrace
