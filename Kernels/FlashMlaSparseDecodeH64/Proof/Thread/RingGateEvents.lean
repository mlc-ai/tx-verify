-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The only source of the prologue's CTA barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingGateEvents

open PTX PTX.Proof PTX.Flow

local macro "decide_site" : tactic =>
  `(tactic| first
    | (intro _; exact ⟨false, rfl⟩)
    | (intro _; exact ⟨true, rfl⟩)
    | (intro _; rename_i b; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, rfl⟩))))))
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

set_option maxRecDepth 100000 in
private theorem bar_sites : OpPcsFast kernel.code barOp Flow.bar.toList = true := by
  decide +kernel

variable {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}

private theorem bar_pc_of_fired {id : Nat} {count : Option Nat} {mode : BarMode}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .bar id count mode) :
    (Machine.code P L g).pc d ∈ Flow.bar.toList := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    exact OpPcsFast.mem bar_sites hc (fires_bar_op hf hk)

/-- The event from a composed state fires the instruction at that state's site. -/
theorem fired_at_code {ins : Instr} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ t, (Machine.code P L g).AtD d t ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Machine.code P L g).AtD d t at hat
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hat.1, hc] at hf
  exact ⟨t, hat, hf⟩

private theorem named_id_nonzero {L : Launch} {g pc ra rc value : Nat} {aligned : Bool}
    {t : TState} {e : Event} {o : Option TState} {count : Option Nat} {mode : BarMode}
    (hr : t.regs ra = some (b32 value)) (hv : 0 < value) (hbound : value < 16)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.barSyncN (.reg ra) (.reg rc) aligned)) e o) (hk : e.kind = .bar 0 count mode) :
    False := by
  have hread := readBits_b32 (L := L) (g := g) hr (by omega)
  have hval : (BitVec.ofNat 64 value).toNat = value := by simp; omega
  simp only [eventTmpl, barTmpl, hread, hval, show ¬ 16 ≤ value by omega, ↓reduceIte] at hf
  cases hc : readBits L g t 32 (.reg rc) with
  | error f =>
    rw [hc] at hf
    rw [congrArg Event.kind hf.1] at hk
    cases hk
  | ok v =>
    rw [hc] at hf
    dsimp only at hf
    split at hf
    · have h := (Kind.bar.inj (hk.symm.trans (congrArg Event.kind hf.1))).1
      omega
    · rw [congrArg Event.kind hf.1] at hk
      cases hk

/-- The states that can issue a named CTA barrier. -/
def BarSite : Machine.ThreadD → Prop
  | .prologue q => q = .barrier
  | .wg0 q =>
    q.site = .wg0Sync ∨ q.site = .pairBar ∨ q.site = .wg0Sync2 ∨
    q.site = .lseBar ∨ q.site = .lseBar2 ∨ q.site = .everyone ∨ (∃ j, q.site = .epiBar j)
  | .mma q => q.site = .outBar
  | .tma q => q.site = .barrier
  | .index q => q.site = .barrier
  | .idle q => q = .sync
  | .wg2 q => q.site = .barrier
  | _ => False

/-- A fired named CTA barrier comes from one of the audited barrier states. -/
theorem bar_site {id : Nat} {count : Option Nat} {mode : BarMode}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .bar id count mode) :
    BarSite d := by
  have hm := bar_pc_of_fired hf hk
  clear * - d hm
  cases d
  case prologue q =>
    change q.pc ∈ _ at hm
    simp only [BarSite]
    cases q <;> revert hm <;> decide_site
  case wg0 q =>
    change q.site.pc ∈ _ at hm
    simp only [BarSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case mma q =>
    change q.site.pc ∈ _ at hm
    simp only [BarSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case tma q =>
    change q.site.pc ∈ _ at hm
    simp only [BarSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case index q =>
    change q.site.pc ∈ _ at hm
    simp only [BarSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case idle q =>
    change q.pc ∈ _ at hm
    simp only [BarSite]
    cases q <;> revert hm <;> decide
  case wg2 q =>
    change q.site.pc ∈ _ at hm
    simp only [BarSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case head =>
    change 1843 ∈ _ at hm
    exact (by decide : 1843 ∉ Flow.bar.toList) hm
  case done =>
    change 3611 ∈ _ at hm
    exact (by decide : 3611 ∉ Flow.bar.toList) hm

/-- Barrier zero is issued at the prologue gate and uses its full-CTA sync operands. -/
theorem gate_source {count : Option Nat} {mode : BarMode}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .bar 0 count mode) :
    d = .prologue .barrier ∧ count = none ∧ mode = .sync := by
  have hs := bar_site hf hk
  cases d
  case prologue q =>
    change q = .barrier at hs
    subst q
    obtain ⟨_, _, hfire⟩ := fired_at_code hf Flow.code_bar_0
    obtain ⟨_, hc, hm⟩ := Kind.bar.inj (hk.symm.trans (congrArg Event.kind hfire.1))
    exact ⟨rfl, hc, hm⟩
  case wg0 q =>
    rcases hs with hs | hs | hs | hs | hs | hs | ⟨j, hs⟩
    · have hpc : q.site.pc = 256 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_1)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 972 = some (b32 9) :=
        Wg0.reg_value hat (r := 972) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · have hpc : q.site.pc = 475 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_2)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 996 = some (b32 (10 + (warpOf L g) % 2)) :=
        Wg0.reg_value hat (r := 996) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · have hpc : q.site.pc = 569 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_3)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 998 = some (b32 9) :=
        Wg0.reg_value hat (r := 998) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · have hpc : q.site.pc = 1154 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_4)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 1725 = some (b32 9) :=
        Wg0.reg_value hat (r := 1725) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · have hpc : q.site.pc = 1156 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_5)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 1725 = some (b32 9) :=
        Wg0.reg_value hat (r := 1725) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · have hpc : q.site.pc = 1835 := by rw [hs]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_bar_10)
      change (Wg0.code P L g).AtD q t at hat
      have hr : t.regs 2425 = some (b32 12) :=
        Wg0.reg_value hat (r := 2425) (by rw [hpc]; decide +kernel)
      exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
    · fin_cases j
      · have hpc : q.site.pc = 1342 := by rw [hs]; rfl
        obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
          change kernel.code[q.site.pc]? = some _
          simpa only [hpc] using Flow.code_bar_6)
        change (Wg0.code P L g).AtD q t at hat
        have hr : t.regs 1906 = some (b32 9) :=
          Wg0.reg_value hat (r := 1906) (by rw [hpc]; decide +kernel)
        exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
      · have hpc : q.site.pc = 1502 := by rw [hs]; rfl
        obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
          change kernel.code[q.site.pc]? = some _
          simpa only [hpc] using Flow.code_bar_7)
        change (Wg0.code P L g).AtD q t at hat
        have hr : t.regs 2077 = some (b32 9) :=
          Wg0.reg_value hat (r := 2077) (by rw [hpc]; decide +kernel)
        exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
      · have hpc : q.site.pc = 1659 := by rw [hs]; rfl
        obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
          change kernel.code[q.site.pc]? = some _
          simpa only [hpc] using Flow.code_bar_8)
        change (Wg0.code P L g).AtD q t at hat
        have hr : t.regs 2247 = some (b32 9) :=
          Wg0.reg_value hat (r := 2247) (by rw [hpc]; decide +kernel)
        exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
      · have hpc : q.site.pc = 1817 := by rw [hs]; rfl
        obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
          change kernel.code[q.site.pc]? = some _
          simpa only [hpc] using Flow.code_bar_9)
        change (Wg0.code P L g).AtD q t at hat
        have hr : t.regs 2416 = some (b32 9) :=
          Wg0.reg_value hat (r := 2416) (by rw [hpc]; decide +kernel)
        exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  case mma q =>
    have hpc : q.site.pc = 2160 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_11)
    change (Wg1Mma.code P L g).AtD q t at hat
    have hr : t.regs 918 = some (b32 12) :=
      Wg1Mma.atD_reg hat (r := 918) hpc (by decide +kernel)
    exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  case tma q =>
    have hpc : q.site.pc = 2330 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_12)
    change (Wg1Tma.code P L g).AtD q t at hat
    have hr : t.regs 790 = some (b32 12) :=
      Wg1Tma.atD_regAt hat hpc (by decide +kernel)
    exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  case index q =>
    have hpc : q.site.pc = 2585 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_13)
    change (Wg1Index.code P L g).AtD q t at hat
    have hr : t.regs 659 = some (b32 12) :=
      Wg1Index.AtD.reg hat (r := 659) (by rw [hpc]; decide +kernel)
    exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  case idle q =>
    have hpc : q.pc = 2604 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
      change kernel.code[q.pc]? = some _
      simpa only [hpc] using Flow.code_bar_14)
    change (Thread.code L g).AtD q t at hat
    have hm : Holds t.regs (Thread.facts L g q) := hat.2.2.2.2
    change q = .sync at hs
    rw [hs] at hm
    have hr : t.regs 923 = some (b32 12) :=
      holds_mem hm (mem_factsFrom (val := Thread.valueOf L g) (by decide +kernel))
    exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  case wg2 q =>
    have hpc : q.site.pc = 3610 := by rw [hs]; rfl
    obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
      change kernel.code[q.site.pc]? = some _
      simpa only [hpc] using Flow.code_bar_15)
    change (Wg2.code P L g).AtD q t at hat
    have hr : t.regs 2878 = some (b32 12) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    exact (named_id_nonzero hr (by omega) (by omega) hfire hk).elim
  all_goals exact hs.elim

private def exitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem exit_sites : OpPcsFast kernel.code exitOp Flow.exit.toList = true := by
  decide +kernel

/-- The frozen kernel has no exit inside the prologue. -/
theorem exit_after_prologue (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .exit)
    : ∀ s, d ≠ .prologue s := by
  rintro s rfl
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[s.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[s.pc]? with
  | none =>
    rw [hc] at hf
    rw [congrArg Event.kind hf.1] at hk
    cases hk
  | some ins =>
    rw [hc] at hf
    have hop : exitOp ins.op = true := by
      rcases fires_exit_op hf hk with h | h <;> rw [h] <;> rfl
    have hm := OpPcsFast.mem exit_sites hc hop
    clear * - s hm
    cases s <;> revert hm <;> decide_site

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingGateEvents
