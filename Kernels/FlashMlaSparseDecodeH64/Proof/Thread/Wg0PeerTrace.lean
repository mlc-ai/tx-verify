-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Ordinals
public import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead

@[expose] public section

/-! # Trace positions and actual accesses of the peer exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeerTrace

open PTX PTX.Flow Ledger PTX.Proof

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

section
variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The actual peer barrier uses the participant warp's parity and a 64-thread count. -/
theorem pair_kind {g : Nat} {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) (hsite : d.site = .pairBar)
    : e.kind = .bar (10 + warpOf L g % 2) (some 64) .sync := by
  have hpc : d.site.pc = 475 := by rw [hsite]; rfl
  obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_bar_2)
  change (Wg0.code P L g).AtD d t at hat
  have hid := Wg0.reg_value hat (r := 996) (by rw [hpc]; decide +kernel)
  have hcnt := Wg0.reg_value hat (r := 997) (by rw [hpc]; decide +kernel)
  have ha := readBits_b32 (L := L) (g := g) hid (by omega)
  have hb := readBits_b32 (L := L) (g := g) hcnt (by decide)
  exact congrArg Event.kind (fires_barTmpl_at ha hb
    (by omega) (by decide) (by decide) (by decide) (by rw [hpre.block]; decide) hfire)

/-- Only the pair-exchange barriers issue named barriers 10 and 11. -/
theorem pair_fired {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState} {p : Fin 2}
    {count : Option Nat} {mode : BarMode} (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .bar (10 + p.val) count mode) :
    ∃ q, d = .wg0 q ∧ q.site = .pairBar ∧ warpOf L g < 4 ∧ warpOf L g % 2 = p.val ∧
      count = some 64 ∧ mode = .sync := by
  have hp := p.isLt
  have hs := RingGateEvents.bar_site hf hk
  cases d
  case prologue q =>
    change q = .barrier at hs
    subst q
    obtain ⟨_, _, hfire⟩ := RingGateEvents.fired_at_code hf Flow.code_bar_0
    have he := (Kind.bar.inj (hk.symm.trans (congrArg Event.kind hfire.1))).1
    change 10 + p.val = 0 at he
    omega
  case wg0 q =>
    have hi : Wg0.Inv P L g q := (Exists.choose_spec hf).1.2
    by_cases hpair : q.site = .pairBar
    · have he := Kind.bar.inj (hk.symm.trans (pair_kind hpre hf hpair))
      exact ⟨q, rfl, hpair, hi.warpLt, by omega, he.2⟩
    · have hkind : e.kind = .bar 9 (some 128) .sync ∨
          e.kind = .bar 12 (some 384) .sync := by
        rcases hs with hs | hs | hs | hs | hs | hs | ⟨j, hs⟩
        · exact .inl (Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial))
        · contradiction
        · exact .inl (Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial))
        · exact .inl (Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial))
        · exact .inl (Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial))
        · have hpc : q.site.pc = 1835 := by rw [hs]; rfl
          obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
            change kernel.code[q.site.pc]? = some _
            simpa only [hpc] using Flow.code_bar_10)
          change (Wg0.code P L g).AtD q t at hat
          have hr : t.regs 2425 = some (b32 12) :=
            Wg0.reg_value hat (by rw [hpc]; decide +kernel)
          have he := barId_eq hr (by decide) hfire hk
          omega
        · exact .inl (Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial))
      rcases hkind with he | he
      all_goals have hId := (Kind.bar.inj (hk.symm.trans he)).1
      all_goals omega
  case mma q =>
    have hpc : q.site.pc = 2160 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_11)
    change (Wg1Mma.code P L g).AtD q t at hat
    have hr : t.regs 918 = some (b32 12) :=
      Wg1Mma.atD_reg hat (r := 918) hpc (by decide +kernel)
    have he := barId_eq hr (by decide) hfire hk
    omega
  case tma q =>
    have hpc : q.site.pc = 2330 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_12)
    change (Wg1Tma.code P L g).AtD q t at hat
    have hr : t.regs 790 = some (b32 12) :=
      Wg1Tma.atD_regAt hat hpc (by decide +kernel)
    have he := barId_eq hr (by decide) hfire hk
    omega
  case index q =>
    have hpc : q.site.pc = 2585 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_13)
    change (Wg1Index.code P L g).AtD q t at hat
    have hr : t.regs 659 = some (b32 12) :=
      Wg1Index.AtD.reg hat (r := 659) (by rw [hpc]; decide +kernel)
    have he := barId_eq hr (by decide) hfire hk
    omega
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
    have he := barId_eq hr (by decide) hfire hk
    omega
  case wg2 q =>
    have hpc : q.site.pc = 3610 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_15)
    change (Wg2.code P L g).AtD q t at hat
    have hr : t.regs 2878 = some (b32 12) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    have he := barId_eq hr (by decide) hfire hk
    omega
  all_goals exact hs.elim

/-- A pair-barrier event in a consistent trace fixes its actual role state. -/
theorem pair_at {X : Execution} {g k : Nat} {e : Event} {p : Fin 2} {count : Option Nat}
    {mode : BarMode} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, k) = some e) (hk : e.kind = .bar (10 + p.val) count mode) :
    ∃ q, Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 q)) ∧
      q.site = .pairBar ∧ warpOf L g < 4 ∧ warpOf L g % 2 = p.val ∧
      count = some 64 ∧ mode = .sync := by
  have hg := Frame.lt_of_get hX he
  rcases (hs.produces (hX.thr g hg)).fired he with
    ⟨state, o, hstate, hfired⟩ | ⟨_, _, _, hbad⟩
  · cases state with
    | none => exact ((ht g k hg) hstate).elim
    | some d =>
      obtain ⟨q, rfl, hq, hw, hp, hc, hm⟩ := pair_fired hpre hfired hk
      exact ⟨q, hstate, hq, hw, hp, hc, hm⟩
  · rw [hbad] at hk
    cases hk

private theorem pair_false {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : ∀ q, d = .wg0 q → q.site ≠ .pairBar) :
    Execution.isBarId (10 + warpOf L g % 2) e = false := by
  cases he : Execution.isBarId (10 + warpOf L g % 2) e
  · rfl
  · obtain ⟨_, _, _, hk⟩ := NamedBar.isBarId_form he
    let p : Fin 2 := ⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩
    obtain ⟨q, hq, hs, _, _, _, _⟩ := pair_fired (p := p) hpre hf (congrArg Event.kind hk)
    exact (hn q hq hs).elim

private theorem count_at {X : Execution} {g k : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0)
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init (X.tr g))
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (Execution.isBarId (10 + warpOf L g % 2)) = ordinal d :=
  Ledger.wg0 (Z := (· = (.bar (10 + warpOf L g % 2))))
    (fun _ _ _ _ hf hc => by subst hc; exact pair_false hpre hf fun _ h => by cases h)
    ht (fun d n => n (.bar (10 + warpOf L g % 2)) = ordinal d)
    (fun n hn => (hn _ rfl).trans (Wg0Ordinals.init_zero P L g).2.1.symm)
    (fun d _ n e o hf hs hc => by
      have hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o := hf
      simp only [bump_apply, hc, (Wg0Ordinals.step hs).2.1, Cls.test]
      by_cases hc : d.site = .pairBar
      · simp [Execution.isBarId, pair_kind hpre hf hc, hc]
      · simp [pair_false hpre hf (fun q h => by cases h; exact hc), hc]) hst

/-- The actual pair barrier prefix has the ordinal of the current state. -/
theorem count_at_wg0 {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (Execution.isBarId (10 + warpOf L g % 2)) = ordinal d :=
  count_at hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hst

/-- The pair barrier count at a followed softmax tail has the state's ordinal. -/
theorem count_at_wg0_tail {X : Execution} {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads)
    (hst : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d))) :
    (X.tr g).countP (Execution.isBarId (10 + warpOf L g % 2)) = ordinal d := by
  have h := count_at hpre (hs.produces (hX.thr g hg)) hst
  simpa only [List.take_length] using h

/-- The pair barrier's source ordinal is the block carried by the tracked barrier state. -/
theorem pairOrdinal {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .pairBar) :
    ((X.tr g).take k).countP (Execution.isBarId (10 + warpOf L g % 2)) = d.block := by
  have hc := count_at hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hst
  change _ = ordinal d at hc
  simpa only [ordinal, hsite, completedPair, Nat.add_zero] using hc
end

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    {j : Fin 8} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
include hpre hX hs he hst

/-- Exactly one more exchange barrier has fired before the corresponding peer read. -/
theorem peerOrdinal (hsite : d.site = .peerRead j) :
    ((X.tr g).take k).countP (Execution.isBarId (10 + warpOf L g % 2)) = d.block + 1 := by
  have hc := count_at hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hst
  change _ = ordinal d at hc
  simpa only [ordinal, hsite, completedPair] using hc

/-- No pair barrier for the current block has fired before its exchange store. -/
theorem exchangeOrdinal (hsite : d.site = .exchStore j) :
    ((X.tr g).take k).countP (Execution.isBarId (10 + warpOf L g % 2)) = d.block := by
  have hc := count_at hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hst
  change _ = ordinal d at hc
  simpa only [ordinal, hsite, completedPair, Nat.add_zero] using hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeerTrace
