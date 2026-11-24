-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Barrier events fired by the composed thread machine -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingEvents

open PTX PTX.Proof PTX.Flow

/-- The event at a tracked abstract state fired from that state in a consistent execution. -/
theorem fired_of_trace {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g k : Nat} {d : Machine.ThreadD} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g k = some (some d)) :
    ∃ o, (Machine.machine P L g).Fired (some d) e o :=
  (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired_at he hd

private theorem fired_at_code {P : Params} {L : Launch} {g : Nat}
    {d : Machine.ThreadD} {e : Event} {o : Option TState} {ins : Instr}
    (h : (Machine.machine P L g).Fired (some d) e o)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ t, (Machine.code P L g).AtD d t ∧ (Machine.code P L g).inv d ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, hg, hf⟩ := h
  change (Machine.code P L g).AtD d t ∧ (Machine.code P L g).inv d at hg
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hc, hg.1.1] at hf
  exact ⟨t, hg.1, hg.2, hf⟩

private theorem unit_arrive_template {L : Launch} {g base : Nat} {off : Int}
    {t : TState} {m : Loc} (hm : mbarLoc L g t base off = .ok m) :
    eventTmpl Assumptions.all L g t
      (.mbarArrive base off (.imm 0) (.imm 1) false true .cta none) =
      .arrive m 0 (PTX.next t) 1 true .cta := by
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte,
    tmaTmpl, hm, readBits, pure, Except.pure, bind, Except.bind, ofExec, mbarStateDest]
  rfl

/-- The actual unit arrival returns to its CTA barrier. -/
theorem fired_unit_arrive {L : Launch} {g base pc : Nat} {off : Int}
    {t : TState} {m : Loc} {e : Event} {o : Option TState}
    (hm : mbarLoc L g t base off = .ok m)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarArrive base off (.imm 0) (.imm 1) false true .cta none)) e o) :
    e.kind = .arrive m 0 1 true .cta := by
  rw [unit_arrive_template hm] at hf
  exact congrArg Event.kind hf.1

private theorem fired_acquire_wait {L : Launch} {g dst base pc q : Nat} {off : Int}
    {par : Opnd} {t : TState} {m : Loc} {e : Event} {o : Option TState}
    (hm : mbarLoc L g t base off = .ok m)
    (hq : readBits L g t 32 par = .ok (BitVec.ofNat 64 q)) (hlt : q < 2)
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mbarWait dst base off par true .cta)) e o) :
    ∃ ok, e.kind = .wait m q ok true .cta := by
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte,
    tmaTmpl, hm, hq, pure, Except.pure, bind, Except.bind, ofExec, Fires] at hf
  obtain ⟨ok, he, _⟩ := hf
  have hq' : (BitVec.ofNat 64 q).toNat % 2 = q := by
    simp [Nat.mod_eq_of_lt hlt]
  exact ⟨ok, by simpa only [hq'] using congrArg Event.kind he⟩

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- A dequantizer polls its block's raw-ready buffer with acquire semantics. -/
theorem rawReady_wait {d : Wg2.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .rawReady) (h : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg2.rawReadyOff (d.block % 2)⟩
      (d.block / 2 % 2) ok true .cta := by
  have hpc : d.site.pc = 2677 := by rw [hd]; rfl
  obtain ⟨t, hat, hinv, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarWait_14)
  change (Wg2.code P L g).AtD d t at hat
  change Wg2.Inv P L g d at hinv
  have hbase : t.regs 2458 = some (sb L (Wg2.rawReadyOff d.buf)) :=
    Wg2.AtD.regAt hat hpc (by decide +kernel)
  have hpar : t.regs 2459 = some (b32 d.par) :=
    Wg2.AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg2.rawReadyOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    have h2 := hinv.bufLt
    unfold Wg2.rawReadyOff
    omega
  have hm : mbarLoc L g t 2458 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + Wg2.rawReadyOff d.buf⟩ :=
    mbarLoc_b32 hbase hb (Wg2.sharedAddr_align hpre (by unfold Wg2.rawReadyOff; omega))
  have hq : readBits L g t 32 (.reg 2459) = .ok (BitVec.ofNat 64 d.par) :=
    readBits_b32 hpar (by have := hinv.parLt; omega)
  rw [← hinv.bufBlock, ← hinv.parBlock]
  exact fired_acquire_wait hm hq hinv.parLt hf

/-- The actual CTA arrival template at the producer's free site. -/
theorem rawFree_template {d : Wg2.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .free) (hat : (Wg2.code P L g).AtD d t) (hinv : Wg2.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, g / L.block, L.sharedBase + Wg2.rawFreeOff (d.block % 2)⟩
        0 (PTX.next t) 1 true .cta := by
  have hpc : d.site.pc = 3599 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
  have hbase : t.regs 2784 = some (sb L (Wg2.rawFreeOff d.buf)) :=
    Wg2.AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg2.rawFreeOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    have h2 := hinv.bufLt
    unfold Wg2.rawFreeOff
    omega
  have hm : mbarLoc L g t 2784 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + Wg2.rawFreeOff d.buf⟩ :=
    mbarLoc_b32 hbase hb (Wg2.sharedAddr_align hpre (by unfold Wg2.rawFreeOff; omega))
  rw [← hinv.bufBlock]
  exact unit_arrive_template hm

/-- A dequantizer returns its block's raw buffer with a unit release arrival. -/
theorem rawFree_arrive {d : Wg2.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .free) (h : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg2.rawFreeOff (d.block % 2)⟩
      0 1 true .cta := by
  have hpc : d.site.pc = 3599 := by rw [hd]; rfl
  have hc : kernel.code[d.site.pc]? = some _ := hpc ▸ Flow.code_mbarArrive_9
  obtain ⟨_, hat, hi, hf⟩ := fired_at_code h hc
  rw [rawFree_template hpre hd hat hi hc] at hf
  exact congrArg Event.kind hf.1

/-- The exact CTA release template for an index lane's valid-ready arrival. -/
theorem validReady_template {d : Wg1Index.D} {extra : Bool} {ins : Instr} {t : TState}
    (hpre : Pre P L mem0) (hd : d.site = .ready extra) (hat : Wg1Index.AtD P L g d t)
    (hi : Wg1Index.Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩
        0 (PTX.next t) 1 true .cta := by
  have addr {base : Nat} {t : TState}
      (hat : Wg1Index.AtD P L g d t)
      (hi : Wg1Index.Inv P L g d)
      (hm : base ∈ (Flow.live d.site.pc).filter (fun r => Wg1Index.tracked.contains r))
      (hv : Wg1Index.valueOf P L g d base = sb L (Wg1Index.readyOff d.phase)) :
      mbarLoc L g t base 0 =
        .ok ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩ := by
    have hreg := Wg1Index.AtD.reg hat hm
    rw [hv] at hreg
    have hphase := hi.phase_block (by rw [hd]; intro h'; cases h')
    rw [← hphase]
    apply mbarLoc_b32 hreg
    · have := sharedBase_lt hpre
      have := hi.phase
      unfold Wg1Index.readyOff
      omega
    · exact Wg2.sharedAddr_align hpre (by unfold Wg1Index.readyOff; omega)
  let base := if extra then 653 else 614
  have hCode : kernel.code[d.site.pc]? = some
      ⟨none, .mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none⟩ := by
    rw [hd]
    cases extra
    · exact Flow.code_mbarArrive_6
    · exact Flow.code_mbarArrive_7
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  have hm := addr (base := base) hat hi
    (by rw [hd]; cases extra <;> decide +kernel) (by cases extra <;> rfl)
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte,
    tmaTmpl, hm, readBits, pure, Except.pure, bind, Except.bind, ofExec, mbarStateDest]
  rfl

/-- Each index lane releases its block's valid-ready slot after its coordinate and mask writes. -/
theorem validReady_arrive {d : Wg1Index.D} {extra : Bool} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .ready extra)
    (h : (Machine.machine P L g).Fired (some (.index d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩
      0 1 true .cta := by
  let base := if extra then 653 else 614
  have hc : kernel.code[d.site.pc]? = some
      ⟨none, .mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none⟩ := by
    rw [hd]
    cases extra
    · exact Flow.code_mbarArrive_6
    · exact Flow.code_mbarArrive_7
  obtain ⟨t, hat, hi, hf⟩ := fired_at_code h hc
  rw [validReady_template hpre hd hat hi hc] at hf
  exact congrArg Event.kind hf.1

/-- The actual CTA arrival template at the producer's rawReady site. -/
theorem rawReady_template {d : Wg1Tma.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .rawReady) (hat : (Wg1Tma.code P L g).AtD d t) (hi : Wg1Tma.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩
        36864 (PTX.next t) 1 true .cta := by
  have hpc : d.site.pc = 2305 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_4)
  have hbase : t.regs 696 = some (sb L (Wg1Tma.rawReadyOff d.buf)) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hbytes : t.regs 772 = some (b32 36864) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg1Tma.rawReadyOff d.buf < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hi.buf_lt
    unfold Wg1Tma.rawReadyOff
    omega
  have hslot := hi.buf_eq (by rw [hd]; decide) (by rw [hd]; decide)
  have hm : mbarLoc L g t 696 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩ := by
    rw [← hslot]
    exact mbarLoc_b32 hbase hb (Wg1Tma.sharedAddr_align hpre (by unfold Wg1Tma.rawReadyOff; omega))
  have hq := readBits_b32 (L := L) (g := g) hbytes (by decide)
  have hn : readBits L g t 32 (.imm 1) = .ok (BitVec.ofNat 64 1) := rfl
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte,
    tmaTmpl, hm, hq, hn, pure, Except.pure, bind, Except.bind, ofExec, mbarStateDest]
  rfl

/-- The TMA producer adds one arrival and 36,864 expected bytes to its block's raw-ready slot. -/
theorem rawReady_expectTx {d : Wg1Tma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .rawReady) (h : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩
      36864 1 true .cta := by
  have hpc : d.site.pc = 2305 := by rw [hd]; rfl
  have hc : kernel.code[d.site.pc]? = some _ := hpc ▸ Flow.code_mbarArrive_4
  obtain ⟨_, hat, hi, hf⟩ := fired_at_code h hc
  rw [rawReady_template hpre hd hat hi hc] at hf
  exact congrArg Event.kind hf.1

/-- The actual CTA arrival template at the producer's coordFree site. -/
theorem validFree_template {d : Wg1Tma.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .coordFree) (hat : (Wg1Tma.code P L g).AtD d t) (hi : Wg1Tma.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.coordFreeOff (d.block % 4)⟩
        0 (PTX.next t) 1 true .cta := by
  have hpc : d.site.pc = 2308 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_5)
  have hbase : t.regs 773 = some (sb L (Wg1Tma.coordFreeOff d.phase)) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg1Tma.coordFreeOff d.phase < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hi.phase_lt
    unfold Wg1Tma.coordFreeOff
    omega
  have hslot := hi.phase_eq (by rw [hd]; decide) (by rw [hd]; decide)
  rw [← hslot]
  exact unit_arrive_template
    (mbarLoc_b32 hbase hb (Wg1Tma.sharedAddr_align hpre (by unfold Wg1Tma.coordFreeOff; omega)))

/-- The TMA producer returns its block's index slot with a unit release arrival. -/
theorem validFree_arrive {d : Wg1Tma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .coordFree) (h : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.coordFreeOff (d.block % 4)⟩
      0 1 true .cta := by
  have hpc : d.site.pc = 2308 := by rw [hd]; rfl
  have hc : kernel.code[d.site.pc]? = some _ := hpc ▸ Flow.code_mbarArrive_5
  obtain ⟨_, hat, hi, hf⟩ := fired_at_code h hc
  rw [validFree_template hpre hd hat hi hc] at hf
  exact congrArg Event.kind hf.1

/-- The TMA producer polls its block's valid-ready slot with acquire semantics. -/
theorem validReady_wait {d : Wg1Tma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .waitCoord) (h : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.readyOff (d.block % 4)⟩
      (d.block / 4 % 2) ok true .cta := by
  have hpc : d.site.pc = 2234 := by rw [hd]; rfl
  obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarWait_9)
  change (Wg1Tma.code P L g).AtD d t at hat
  change Wg1Tma.Inv P L g d at hi
  have hbase : t.regs 685 = some (sb L (Wg1Tma.readyOff d.phase)) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hpar : t.regs 686 = some (b32 d.par) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg1Tma.readyOff d.phase < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hi.phase_lt
    unfold Wg1Tma.readyOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) hbase hb
    (Wg1Tma.sharedAddr_align hpre (by unfold Wg1Tma.readyOff; omega))
  have hq := readBits_b32 (L := L) (g := g) hpar (by have := hi.par_lt; omega)
  have hslot := hi.phase_eq (by rw [hd]; decide) (by rw [hd]; decide)
  have hphase := hi.par_eq (by rw [hd]; decide) (by rw [hd]; decide)
  rw [← hslot, ← hphase]
  exact fired_acquire_wait hm hq hi.par_lt hf

/-- The TMA producer polls for reuse of its raw buffer with the opposite parity. -/
theorem rawFree_wait {d : Wg1Tma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .waitFree) (h : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawFreeOff (d.block % 2)⟩
      (1 - d.block / 2 % 2) ok true .cta := by
  have hpc : d.site.pc = 2245 := by rw [hd]; rfl
  obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarWait_10)
  change (Wg1Tma.code P L g).AtD d t at hat
  change Wg1Tma.Inv P L g d at hi
  have hbase : t.regs 688 = some (sb L (Wg1Tma.rawFreeOff d.buf)) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hpar : t.regs 689 = some (b32 (1 - d.rpar)) :=
    Wg1Tma.atD_regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg1Tma.rawFreeOff d.buf < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hi.buf_lt
    unfold Wg1Tma.rawFreeOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) hbase hb
    (Wg1Tma.sharedAddr_align hpre (by unfold Wg1Tma.rawFreeOff; omega))
  have hq := readBits_b32 (L := L) (g := g) hpar (by omega)
  have hslot := hi.buf_eq (by rw [hd]; decide) (by rw [hd]; decide)
  have hphase := hi.rpar_eq (by rw [hd]; decide) (by rw [hd]; decide)
  rw [← hslot, ← hphase]
  exact fired_acquire_wait hm hq (by omega) hf

/-- The softmax role's mask-ready poll acquires the same slot as the TMA ready poll. -/
theorem maskReady_wait {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .maskReady) (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg0.validReadyOff (d.block % 4)⟩
      (d.block / 4 % 2) ok true .cta := by
  have hpc : d.site.pc = 264 := by rw [hd]; rfl
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarWait_0)
  change (Wg0.code P L g).AtD d t at hat
  have hm := mbarLoc_b32 (L := L) (g := g) (Wg0.reg974 hat hd)
    (Wg0.maskAddr_lt hpre (Wg0.vslotOf_lt d)) (Wg0.maskAddr_mod8 hpre (d.block % 4))
  have hq := readBits_b32 (L := L) (g := g) (Wg0.reg975 hat hd) (by omega)
  exact fired_acquire_wait hm hq (by omega) hf

/-- Each softmax lane releases its use of the index slot with a unit release arrival. -/
theorem maskFree_arrive {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .validFree) (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg0.validFreeOff (d.block % 4)⟩
      0 1 true .cta := by
  have hpc : d.site.pc = 571 := by rw [hd]; rfl
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarArrive_1)
  change (Wg0.code P L g).AtD d t at hat
  have hm := mbarLoc_b32 (L := L) (g := g) (Wg0.reg1000 hat hd)
    (Wg0.ringAddr_lt hpre (buf := d.block % 4) (by omega))
    (Wg0.ringAddr_mod8 hpre (off := 222872) (by decide))
  exact fired_unit_arrive hm hf

/-- Each index lane polls for reuse of its slot with the opposite parity. -/
theorem validFree_wait {d : Wg1Index.D} {extra : Bool} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .waitFree extra)
    (h : (Machine.machine P L g).Fired (some (.index d)) e o) :
    ∃ ok, e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
      (1 - d.block / 4 % 2) ok true .cta := by
  have of_regs {base par dst pc : Nat} {t : TState}
      (hat : Wg1Index.AtD P L g d t) (hi : Wg1Index.Inv P L g d)
      (hm : base ∈ (Flow.live d.site.pc).filter (fun r => Wg1Index.tracked.contains r))
      (hp : par ∈ (Flow.live d.site.pc).filter (fun r => Wg1Index.tracked.contains r))
      (hbase : Wg1Index.valueOf P L g d base = sb L (Wg1Index.freeOff d.phase))
      (hpar : Wg1Index.valueOf P L g d par = b32 (1 - d.par))
      (hf : Fires pc (eventTmpl Assumptions.all L g t
        (.mbarWait dst base 0 (.reg par) true .cta)) e o) :
      ∃ ok, e.kind = .wait
        ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
        (1 - d.block / 4 % 2) ok true .cta := by
    have hreg := Wg1Index.AtD.reg hat hm
    have hregp := Wg1Index.AtD.reg hat hp
    rw [hbase] at hreg
    rw [hpar] at hregp
    have hb : L.sharedBase + Wg1Index.freeOff d.phase < 2 ^ 32 := by
      have := sharedBase_lt hpre
      have := hi.phase
      unfold Wg1Index.freeOff
      omega
    have hm := mbarLoc_b32 (L := L) (g := g) hreg hb
      (Wg2.sharedAddr_align hpre (by unfold Wg1Index.freeOff; omega))
    have hq := readBits_b32 (L := L) (g := g) hregp (by omega)
    have hne : d.site ≠ .barrier := by rw [hd]; intro he; cases he
    rw [← hi.phase_block hne, ← hi.par_block hne]
    exact fired_acquire_wait hm hq (by omega) hf
  cases extra
  · obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hd, Wg1Index.Site.pc] using Flow.code_mbarWait_11)
    exact of_regs hat hi (by rw [hd]; decide +kernel) (by rw [hd]; decide +kernel) rfl rfl hf
  · obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hd, Wg1Index.Site.pc] using Flow.code_mbarWait_12)
    exact of_regs hat hi (by rw [hd]; decide +kernel) (by rw [hd]; decide +kernel) rfl rfl hf


/-- The TMA role's two entry polls use the query and output objects respectively. -/
theorem tmaEntry_wait {d : Wg1Tma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .waitQ ∨ d.site = .waitLast)
    (h : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ off ok, (off = Wg1Tma.qUtccpOff ∨ off = Wg1Tma.lastStoreOff) ∧
      e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ 0 ok true .cta := by
  have from_regs {base dst off pc : Nat} {t : TState}
      (hm : t.regs base = some (sb L off)) (hp : t.regs 670 = some (b32 0))
      (hoff : off = Wg1Tma.qUtccpOff ∨ off = Wg1Tma.lastStoreOff)
      (hf : Fires pc (eventTmpl Assumptions.all L g t
        (.mbarWait dst base 0 (.reg 670) true .cta)) e o) :
      ∃ off ok, (off = Wg1Tma.qUtccpOff ∨ off = Wg1Tma.lastStoreOff) ∧
        e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ 0 ok true .cta := by
    have hb : L.sharedBase + off < 2 ^ 32 := by
      have hle : off ≤ 222952 := by rcases hoff with rfl | rfl <;> decide
      have := sharedBase_lt hpre
      omega
    have hmod : off % 8 = 0 := by rcases hoff with rfl | rfl <;> decide
    have ha := mbarLoc_b32 (L := L) (g := g) hm hb (Wg1Tma.sharedAddr_align hpre hmod)
    have hq := readBits_b32 (L := L) (g := g) hp (by decide)
    obtain ⟨ok, hk⟩ := fired_acquire_wait ha hq (by decide) hf
    exact ⟨off, ok, hoff, hk⟩
  rcases hd with hQ | hLast
  · have hpc : d.site.pc = 2205 := by rw [hQ]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_7)
    change (Wg1Tma.code P L g).AtD d t at hat
    exact from_regs (Wg1Tma.atD_regAt hat hpc (r := 669) (by decide +kernel))
      (Wg1Tma.atD_regAt hat hpc (by decide +kernel)) (Or.inl rfl) hf
  · have hpc : d.site.pc = 2209 := by rw [hLast]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_8)
    change (Wg1Tma.code P L g).AtD d t at hat
    exact from_regs (Wg1Tma.atD_regAt hat hpc (r := 672) (by decide +kernel))
      (Wg1Tma.atD_regAt hat hpc (by decide +kernel)) (Or.inr rfl) hf

/-- The two GEMM waits of the softmax role poll their own completion objects. -/
theorem gemmDone_wait_exact {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qkDone ∨ d.site = .svDone)
    (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    let off := if d.site = .qkDone then Wg0.qkDoneOff (d.block % 2)
      else Wg0.svDoneOff (d.block % 2)
    ∃ ok scope, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩
      (d.block / 2 % 2) ok true scope := by
  rcases hd with hQ | hS
  · have hpc : d.site.pc = 272 := by rw [hQ]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_1)
    change (Wg0.code P L g).AtD d t at hat
    obtain ⟨scope, ht⟩ := Wg0.event_qkDone hpre hat hQ
    change Fires ((Machine.code P L g).pc (.wg0 d)) (eventTmpl Assumptions.all L g t _) e o at hf
    rw [ht] at hf
    obtain ⟨ok, he, _⟩ := hf
    have hpar : (BitVec.ofNat 64 (d.block / 2 % 2)).toNat % 2 = d.block / 2 % 2 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    exact ⟨ok, scope, by simpa [hQ, Wg0.qkDoneOff, hpar] using congrArg Event.kind he⟩
  · have hpc : d.site.pc = 1184 := by rw [hS]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_1184)
    change (Wg0.code P L g).AtD d t at hat
    obtain ⟨scope, ht⟩ := Wg0.event_svDone hpre hat hS
    change Fires ((Machine.code P L g).pc (.wg0 d)) (eventTmpl Assumptions.all L g t _) e o at hf
    rw [ht] at hf
    obtain ⟨ok, he, _⟩ := hf
    have hpar : (BitVec.ofNat 64 (d.block / 2 % 2)).toNat % 2 = d.block / 2 % 2 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    exact ⟨ok, scope, by simpa [hS, Wg0.svDoneOff, hpar] using congrArg Event.kind he⟩

/-- The two GEMM waits of the softmax role poll their own completion objects. -/
theorem gemmDone_wait {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qkDone ∨ d.site = .svDone)
    (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    ∃ off parity ok scope, (off = Wg0.qkDoneOff (d.block % 2) ∨ off = Wg0.svDoneOff (d.block % 2)) ∧
      e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true scope := by
  obtain ⟨ok, scope, he⟩ := gemmDone_wait_exact hpre hd h
  rcases hd with hd | hd
  · exact ⟨_, _, ok, scope, .inl rfl, by simpa [hd] using he⟩
  · exact ⟨_, _, ok, scope, .inr rfl, by simpa [hd] using he⟩

/-- The softmax role publishes completion of the previous row on the output store object. -/
theorem lastStore_arrive {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .lastStore) (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg0.lastStoreOff⟩ 0 1 true .cta := by
  have hpc : d.site.pc = 200 := by rw [hd]; rfl
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarArrive_0)
  change (Wg0.code P L g).AtD d t at hat
  have hbase : t.regs 938 = some (sb L Wg0.lastStoreOff) := by
    have hr := Wg0.reg_value hat (r := 938) (by rw [hd]; decide +kernel)
    simpa [Wg0.valueOf, Wg0.table, Wg0.lastStoreOff, PTX.Flow.lookupLit, Option.getD_some] using hr
  have hb : L.sharedBase + Wg0.lastStoreOff < 2 ^ 32 := by
    have := sharedBase_lt hpre
    unfold Wg0.lastStoreOff
    omega
  have halign := Wg0.ringAddr_mod8 hpre (off := Wg0.lastStoreOff) (buf := 0) (by decide)
  exact fired_unit_arrive (mbarLoc_b32 hbase hb halign) hf

/-- The softmax lane arrives on the score/probability object for its current raw buffer. -/
theorem scores_arrive {d : Wg0.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .soReady) (h : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    e.kind = .arrive
      ⟨.shared, g / L.block, L.sharedBase + Wg0.soReadyOff (d.block % 2)⟩ 0 1 true .cta := by
  have hpc : d.site.pc = 1122 := by rw [hd]; rfl
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarArrive_2)
  change (Wg0.code P L g).AtD d t at hat
  have hbase : t.regs 1717 = some (sb L (Wg0.soReadyOff (d.block % 2))) :=
    Wg0.reg_value hat (by rw [hd]; decide +kernel)
  have hm := mbarLoc_b32 (L := L) (g := g) hbase
    (Wg0.ringAddr_lt hpre (off := 222920) (buf := d.block % 2) (by omega))
    (Wg0.ringAddr_mod8 hpre (off := 222920) (by decide))
  exact fired_unit_arrive hm hf

set_option maxRecDepth 100000 in
private theorem init_code (j : Fin 23) :
    kernel.code[(Site.init j).pc]? =
      some { op := .mbarInit (initAddrReg j) 0 (.reg (initCountReg j)) } := by
  fin_cases j <;> first
    | exact Flow.code_mbarInit_0
    | exact Flow.code_mbarInit_1
    | exact Flow.code_mbarInit_2
    | exact Flow.code_mbarInit_3
    | exact Flow.code_mbarInit_4
    | exact Flow.code_mbarInit_5
    | exact Flow.code_mbarInit_6
    | exact Flow.code_mbarInit_7
    | exact Flow.code_mbarInit_8
    | exact Flow.code_mbarInit_9
    | exact Flow.code_mbarInit_10
    | exact Flow.code_mbarInit_11
    | exact Flow.code_mbarInit_12
    | exact Flow.code_mbarInit_13
    | exact Flow.code_mbarInit_14
    | exact Flow.code_mbarInit_15
    | exact Flow.code_mbarInit_16
    | exact Flow.code_mbarInit_17
    | exact Flow.code_mbarInit_18
    | exact Flow.code_mbarInit_19
    | exact Flow.code_mbarInit_20
    | exact Flow.code_mbarInit_21
    | exact Flow.code_mbarInit_22

set_option maxRecDepth 100000 in
private theorem init_regs {P : Params} {L : Launch} {g : Nat} {j : Fin 23} {t : TState}
    (h : (Machine.code P L g).AtD (.prologue (.init j)) t) :
    t.regs (initAddrReg j) = some (sb L (initOff j)) ∧
      t.regs (initCountReg j) = some (b32 (initCount j)) := by
  have ht : Holds t.regs (facts L g (.init j)) := h.2.2.2.2
  have ha : initAddrReg j ∈ liveAll (Site.init j).pc := by fin_cases j <;> decide +kernel
  have hc : initCountReg j ∈ liveAll (Site.init j).pc := by fin_cases j <;> decide +kernel
  have hr1 := holds_mem ht (mem_factsFrom (val := valueOf L g) ha)
  have hr2 := holds_mem ht (mem_factsFrom (val := valueOf L g) hc)
  fin_cases j <;> exact ⟨hr1, hr2⟩

/-- The initialization template names the shared object and the count of its table entry. -/
theorem init_template {j : Fin 23} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (Machine.code P L g).AtD (.prologue (.init j)) t)
    (hCode : kernel.code[(Site.init j).pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .mbInit ⟨.shared, g / L.block, L.sharedBase + initOff j⟩ (initCount j)
        (PTX.next t) := by
  obtain rfl := Option.some.inj (hCode.symm.trans (init_code j))
  obtain ⟨hr, hc⟩ := init_regs hat
  have hOff : initOff j ≤ 222952 := by fin_cases j <;> decide
  have hAlign : initOff j % 8 = 0 := by fin_cases j <;> decide
  have hBound : L.sharedBase + initOff j < 2 ^ 32 := by
    have := sharedBase_lt hpre
    omega
  have hLoc := mbarLoc_b32 (L := L) (g := g) hr hBound
    (Wg1Tma.sharedAddr_align hpre hAlign)
  have hCount : 0 < initCount j ∧ initCount j < 2 ^ 20 := by fin_cases j <;> decide
  have hbits := readBits_b32 (L := L) (g := g) hc (by omega)
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  have hnat : (BitVec.ofNat 64 (initCount j)).toNat = initCount j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte, tmaTmpl,
    hLoc, hbits, pure, Except.pure, bind, Except.bind, ofExec, hnat, ite_eq_left hCount]

/-- A prologue initialization names the shared object and the count of its table entry. -/
theorem barrier_init {j : Fin 23} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (h : (Machine.machine P L g).Fired (some (.prologue (.init j))) e o) :
    e.kind = .mbInit ⟨.shared, g / L.block, L.sharedBase + initOff j⟩ (initCount j) := by
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (init_code j)
  rw [init_template hpre hat (init_code j)] at hf
  exact congrArg Event.kind hf.1

/-- The MMA producer expects the eight query transfers on the fixed query object. -/
theorem query_expectTx {d : Wg1Mma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qArrive) (h : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + 222776⟩ 65536 1 true .cta := by
  have hpc : d.site.pc = 1929 := by rw [hd]; rfl
  obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
    change kernel.code[d.site.pc]? = some _
    simpa only [hpc] using Flow.code_mbarArrive_3)
  change (Wg1Mma.code P L g).AtD d t at hat
  have h811 : t.regs 811 = some (b32 (Wg1Mma.qTmaAddr L)) := by
    have hm := Wg1Mma.atD_reg hat (r := 811) hpc (by decide +kernel)
    simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h827 : t.regs 827 = some (b32 65536) := by
    have hm := Wg1Mma.atD_reg hat (r := 827) hpc (by decide +kernel)
    simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
  rw [Wg1Mma.qTmaAddr_eq] at h811
  have haddr : L.sharedBase + 222776 < 2 ^ 32 := by have := sharedBase_lt hpre; omega
  have hm := mbarLoc_b32 (L := L) (g := g) h811 haddr
    (Wg2.sharedAddr_align hpre (by decide : 222776 % 8 = 0))
  have hb := readBits_b32 (L := L) (g := g) h827 (by decide)
  have hn : readBits L g t 32 (.imm 1) = .ok (BitVec.ofNat 64 1) := rfl
  have hscope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp only [eventTmpl, widenMbarScope, hscope, Bool.false_eq_true, ↓reduceIte,
    tmaTmpl, hm, hb, hn, pure, Except.pure, bind, Except.bind, ofExec, Fires] at hf
  exact congrArg Event.kind hf.1

/-- The actual CTA arrival template at the producer's ready site. -/
theorem dequantReady_template {d : Wg2.D} {t : TState} {ins : Instr} (hpre : Pre P L mem0)
    (hd : d.site = .ready) (hat : (Wg2.code P L g).AtD d t) (hi : Wg2.Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .arrive ⟨.shared, g / L.block, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩
        0 (PTX.next t) 1 true .cta := by
  have hpc : d.site.pc = 3597 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
  have hbase : t.regs 2783 = some (sb L (Wg2.dequantReadyOff d.buf)) :=
    Wg2.AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + Wg2.dequantReadyOff d.buf < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hi.bufLt
    unfold Wg2.dequantReadyOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) hbase hb
    (Wg2.sharedAddr_align hpre (by unfold Wg2.dequantReadyOff; omega))
  rw [← hi.bufBlock]
  exact unit_arrive_template hm

/-- The dequantized-KV producer publishes on its block's dequant-ready object. -/
theorem dequantReady_arrive {d : Wg2.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .ready) (h : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    e.kind = .arrive ⟨.shared, g / L.block, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩
      0 1 true .cta := by
  have hpc : d.site.pc = 3597 := by rw [hd]; rfl
  have hc : kernel.code[d.site.pc]? = some _ := hpc ▸ Flow.code_mbarArrive_8
  obtain ⟨_, hat, hi, hf⟩ := fired_at_code h hc
  rw [dequantReady_template hpre hd hat hi hc] at hf
  exact congrArg Event.kind hf.1



private theorem wait_from_regs {P : Params} {L : Launch} {mem0 : Mem0}
    {g base dst pc par off q : Nat}
    {t : TState} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hm : t.regs base = some (sb L off)) (hp : t.regs par = some (b32 q))
    (hoff : off ≤ 222952) (halign : off % 8 = 0) (hlt : q < 2)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarWait dst base 0 (.reg par) true .cta)) e o) :
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ q ok true .cta := by
  have hb : L.sharedBase + off < 2 ^ 32 := by have := sharedBase_lt hpre; omega
  have ha := mbarLoc_b32 (L := L) (g := g) hm hb (Wg2.sharedAddr_align hpre halign)
  have hq := readBits_b32 (L := L) (g := g) hp (by omega)
  exact fired_acquire_wait ha hq hlt hf

/-- The MMA role waits on the query, dequantized KV, and probability objects. -/
theorem mma_wait_exact {d : Wg1Mma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qWait ∨ d.site = .qCopyWait ∨ d.site = .kvWait ∨ d.site = .soWait)
    (h : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    let off := if d.site = .qWait then 222776 else if d.site = .qCopyWait then 222784
      else if d.site = .kvWait then 222792 + 8 * (d.i % 2) else 222920 + 8 * (d.i % 2)
    let parity := if d.site = .qWait ∨ d.site = .qCopyWait then 0 else Wg1Mma.parOf d.i
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true .cta := by
  rcases hd with hd | hd | hd | hd
  · have hpc : d.site.pc = 1931 := by rw [hd]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_3)
    change (Wg1Mma.code P L g).AtD d t at hat
    have hb : t.regs 811 = some (sb L 222776) := by
      have hm := Wg1Mma.atD_reg hat (r := 811) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.qTmaAddr_eq, Nat.add_assoc, sb] using hm
    have hp : t.regs 812 = some (b32 0) := by
      have hm := Wg1Mma.atD_reg hat (r := 812) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp (by omega) (by omega)
      (by decide) hf
    exact ⟨ok, by simpa [hd] using hk⟩
  · have hpc : d.site.pc = 1983 := by rw [hd]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_4)
    change (Wg1Mma.code P L g).AtD d t at hat
    have hb : t.regs 843 = some (sb L 222784) := by
      have hm := Wg1Mma.atD_reg hat (r := 843) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.qUtccpAddr_eq, Nat.add_assoc, sb] using hm
    have hp : t.regs 812 = some (b32 0) := by
      have hm := Wg1Mma.atD_reg hat (r := 812) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp (by omega) (by omega)
      (by decide) hf
    exact ⟨ok, by simpa [hd] using hk⟩
  · have hpc : d.site.pc = 2012 := by rw [hd]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_5)
    change (Wg1Mma.code P L g).AtD d t at hat
    have hb : t.regs 855 = some (sb L (222792 + 8 * (d.i % 2))) := by
      have hm := Wg1Mma.atD_reg hat (r := 855) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.dequantAddr_eq, Nat.add_assoc, sb] using hm
    have hp : t.regs 879 = some (b32 (Wg1Mma.parOf d.i)) := by
      have hm := Wg1Mma.atD_reg hat (r := 879) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp (by omega) (by omega)
      (by unfold Wg1Mma.parOf; omega) hf
    exact ⟨ok, by simpa [hd] using hk⟩
  · have hpc : d.site.pc = 2107 := by rw [hd]; rfl
    obtain ⟨t, hat, _, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_6)
    change (Wg1Mma.code P L g).AtD d t at hat
    have hb : t.regs 878 = some (sb L (222920 + 8 * (d.i % 2))) := by
      have hm := Wg1Mma.atD_reg hat (r := 878) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some,
        Wg1Mma.soReadyAddr_eq, Nat.add_assoc, sb] using hm
    have hp : t.regs 879 = some (b32 (Wg1Mma.parOf d.i)) := by
      have hm := Wg1Mma.atD_reg hat (r := 879) hpc (by decide +kernel)
      simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using hm
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp (by omega) (by omega)
      (by unfold Wg1Mma.parOf; omega) hf
    exact ⟨ok, by simpa [hd] using hk⟩


/-- The MMA role waits on the query, dequantized KV, and probability objects. -/
theorem mma_wait_object {d : Wg1Mma.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qWait ∨ d.site = .qCopyWait ∨ d.site = .kvWait ∨ d.site = .soWait)
    (h : (Machine.machine P L g).Fired (some (.mma d)) e o) :
    ∃ off parity ok,
      (off = 222776 ∨ off = 222784 ∨ off = 222792 + 8 * (d.i % 2) ∨
        off = 222920 + 8 * (d.i % 2)) ∧
        e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true .cta := by
  obtain ⟨ok, he⟩ := mma_wait_exact hpre hd h
  rcases hd with hd | hd | hd | hd
  · exact ⟨_, _, ok, .inl rfl, by simpa [hd] using he⟩
  · exact ⟨_, _, ok, .inr (.inl rfl), by simpa [hd] using he⟩
  · exact ⟨_, _, ok, .inr (.inr (.inl rfl)), by simpa [hd] using he⟩
  · exact ⟨_, _, ok, .inr (.inr (.inr rfl)), by simpa [hd] using he⟩


/-- The dequantizer waits on query or PV completion. -/
theorem dequant_wait_exact {d : Wg2.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qUtccp ∨ d.site = .svDone)
    (h : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    let off := if d.site = .qUtccp then Wg2.qUtccpOff else Wg2.svDoneOff (d.block % 2)
    let parity := if d.site = .qUtccp then d.block / 2 % 2 else 1 - d.block / 2 % 2
    ∃ ok, e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true .cta := by
  rcases hd with hd | hd
  · have hpc : d.site.pc = 2644 := by rw [hd]; rfl
    obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_13)
    change (Wg2.code P L g).AtD d t at hat
    change Wg2.Inv P L g d at hi
    have hb : t.regs 2434 = some (sb L Wg2.qUtccpOff) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    have hp : t.regs 2435 = some (b32 d.par) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp
      (by have := hi.bufLt; unfold Wg2.qUtccpOff; omega)
      (by unfold Wg2.qUtccpOff; omega)
      (by have := hi.parLt; omega) hf
    exact ⟨ok, by simpa only [hd, ↓reduceIte, hi.parBlock] using hk⟩
  · have hpc : d.site.pc = 2684 := by rw [hd]; rfl
    obtain ⟨t, hat, hi, hf⟩ := fired_at_code h (by
      change kernel.code[d.site.pc]? = some _
      simpa only [hpc] using Flow.code_mbarWait_15)
    change (Wg2.code P L g).AtD d t at hat
    change Wg2.Inv P L g d at hi
    have hb : t.regs 2461 = some (sb L (Wg2.svDoneOff d.buf)) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    have hp : t.regs 2462 = some (b32 (1 - d.par)) :=
      Wg2.AtD.regAt hat hpc (by decide +kernel)
    obtain ⟨ok, hk⟩ := wait_from_regs hpre hb hp
      (by have := hi.bufLt; unfold Wg2.svDoneOff; omega)
      (by unfold Wg2.svDoneOff; omega)
      (by have := hi.parLt; omega) hf
    exact ⟨ok, by simpa [hd, hi.bufBlock, hi.parBlock] using hk⟩

/-- The dequantizer waits on query or PV completion. -/
theorem dequant_wait_object {d : Wg2.D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .qUtccp ∨ d.site = .svDone)
    (h : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    ∃ off parity ok,
      (off = Wg2.qUtccpOff ∨ off = Wg2.svDoneOff (d.block % 2)) ∧
      e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true .cta := by
  obtain ⟨ok, he⟩ := dequant_wait_exact hpre hd h
  rcases hd with hd | hd
  · exact ⟨_, _, ok, .inl rfl, by simpa [hd] using he⟩
  · exact ⟨_, _, ok, .inr rfl, by simpa [hd] using he⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingEvents
