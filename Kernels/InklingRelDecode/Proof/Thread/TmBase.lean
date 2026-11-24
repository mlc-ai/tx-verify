-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerAll
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.TmplOkMore
public import Lemmas.Flow.TmplOkOff
public import Lemmas.Flow.TmplOkSync
public import Lemmas.Cluster.Unit
public import Lemmas.Flow.Events

@[expose] public section

/-! # Undefined-behaviour templates: the instruction forms of the kernel

The statement that no site's event template is undefined behaviour (`Code.TmplOk`) is a fact
about one state and its instruction. This file proves it for the instruction forms the kernel
uses whose operands the machines' facts pin by one generic argument:

* a named barrier with immediate operands (`barSync_imm_ok`);
* a weak load or store of a global or shared register address that evaluates, to an address
  aligned to its size (`loadDirect_ok`, `storeDirect_ok`).

The per-state statements are in the role files (`TmWorker.lean`, …). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- A `bar.sync` with an immediate barrier below 16 and no count is not undefined behaviour. -/
theorem barSync_imm_ok {id : Nat} {al : Bool} (hid : id < 16) (f : Fault) :
    eventTmpl A L g t (.barSync (.imm id) al) ≠ .ub f := by
  have hid' : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp [truncBits]; omega
  simp only [eventTmpl, barTmpl, readBits, pure, Except.pure, hid', show ¬ 16 ≤ id by omega,
    ↓reduceIte]
  simp

/-- A weak load of a register address that `effAddr` locates, aligned to its element size, is
not undefined behaviour, when the access is located directly (`MemAccess.locSpace?`). -/
theorem loadDirect_ok {a : MemAccess} {sp : Space} {base w : Nat}
    (hr : a.rule = some .threadAccess) (hl : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hs : a.sem = .weak)
    (hnc : a.nc = false) (hpos : 0 < a.elem.width / 8)
    (he : ∃ loc, effAddr L g t sp base a.addr.off = .ok loc ∧
      loc.addr % (a.elem.width / 8 * a.regs.length) = 0)
    (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨loc, he, hal⟩ := he
  rw [eventTmpl, memTmpl_direct_weakLoad hr hl hb hk hs]
  simp only [loadTmpl, he, hnc, bind, Except.bind]
  rw [elemAcc_ok hpos hal]
  simp

/-- A weak store of a register address that `effAddr` locates, aligned to its element size, of a
register whose value has the store's size, is not undefined behaviour, when the access is
located directly. -/
theorem storeDirect_ok {a : MemAccess} {sp : Space} {base w : Nat} {o : Opnd}
    (hr : a.rule = some .threadAccess) (hl : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hs : a.sem = .weak)
    (hpos : 0 < a.elem.width / 8)
    (he : ∃ loc, effAddr L g t sp base a.addr.off = .ok loc ∧
      loc.addr % (a.elem.width / 8 * a.srcs.length) = 0)
    (hsrc : a.srcs[t.sub]? = some o)
    (hv : ∃ v, readValue L g t a.elem.width o = .ok v ∧ v.bytes = a.elem.width / 8)
    (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨loc, he, hal⟩ := he
  obtain ⟨v, hv, hbytes⟩ := hv
  rw [eventTmpl, memTmpl_direct_weakStore hr hl hb hk hs]
  simp only [storeTmpl, he, bind, Except.bind]
  rw [elemAcc_ok hpos hal]
  simp [hsrc, hv, storeValue_of_bytes hbytes]

/-- A weak load of an element located by `accessLoc`, aligned to its element size, is not
undefined behaviour. -/
theorem loadAccess_ok {a : MemAccess}
    (hr : a.rule = some .threadAccess) (hl : a.locSpace? = none) (hk : a.kind = .load)
    (hs : a.sem = .weak) (hnc : a.nc = false) (hgo : a.hints.globalOnly = false)
    (hv8 : a.vec ≠ 8) (hv4 : a.vec = 4 → a.elem.width ≠ 64) (hpos : 0 < a.elem.width / 8)
    (he : ∃ loc, accessLoc L g t a = .ok loc ∧ loc.addr % (a.elem.width / 8 * a.vec) = 0)
    (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨loc, he, hal⟩ := he
  have hv4' : ¬ (a.vec == 4 && a.elem.width == 64) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]; exact hv4
  simp only [eventTmpl, memTmpl, hr, hl, accessTmpl, hk, accessAcc, he, hnc, hgo, hs,
    MemAccess.strongLocOk, bind, Except.bind, Bool.false_or, ne_eq, Bool.or_false, hv4',
    Bool.or_self, ↓reduceIte]
  rw [elemAcc_ok hpos hal]
  simp [hv8, MemAccess.semAcc, hs]

/-- A weak store of an element located by `accessLoc`, aligned to its element size, of a register
whose value has the store's size, is not undefined behaviour. -/
theorem storeAccess_ok {a : MemAccess} {o : Opnd}
    (hr : a.rule = some .threadAccess) (hl : a.locSpace? = none) (hk : a.kind = .store)
    (hs : a.sem = .weak) (hnc : a.nc = false) (hgo : a.hints.globalOnly = false)
    (hv8 : a.vec ≠ 8) (hv4 : a.vec = 4 → a.elem.width ≠ 64) (hpos : 0 < a.elem.width / 8)
    (he : ∃ loc, accessLoc L g t a = .ok loc ∧ loc.addr % (a.elem.width / 8 * a.vec) = 0)
    (hsrc : a.srcs[t.sub]? = some o)
    (hv : ∃ v, readValue L g t a.elem.width o = .ok v ∧ v.bytes = a.elem.width / 8)
    (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨loc, he, hal⟩ := he
  obtain ⟨v, hv, hbytes⟩ := hv
  have hv4' : ¬ (a.vec == 4 && a.elem.width == 64) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]; exact hv4
  simp only [eventTmpl, memTmpl, hr, hl, accessTmpl, hk, accessAcc, he, hnc, hgo, hs,
    MemAccess.strongLocOk, bind, Except.bind, Bool.false_or, ne_eq, Bool.or_false, hv4',
    Bool.or_self, ↓reduceIte]
  rw [elemAcc_ok hpos hal]
  simp [hv8, MemAccess.semAcc, hs, hsrc, hv, storeValue_of_bytes hbytes]

/-- A `.shared` symbol's location: the thread's CTA, at the shared base plus the offsets, when
they stay below `2 ^ 32` (the decoder's layout, EXT-SHARED). -/
theorem accessLoc_sharedSym {a : MemAccess} {win : SharedWindow} {o : Nat} {off : Nat}
    (hs : a.space = some (.shared win)) (hb : a.addr.base = .sharedSym o)
    (hoff : a.addr.off = (off : Int)) (hlt : L.sharedBase + o + off < 2 ^ 32) :
    accessLoc L g t a = .ok ⟨.shared, g / L.block, L.sharedBase + o + off⟩ := by
  simp only [accessLoc, hs, hb, hoff, wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  congr
  omega

/-- A `.shared::cta` address in a 32-bit register holding a number: the thread's CTA, at the
register plus the offset modulo `2 ^ 32`. -/
theorem accessLoc_sharedReg {a : MemAccess} {r : Nat} {x : BitVec 64}
    (hs : a.space = some (.shared .cta)) (hb : a.addr.base = .reg r 32)
    (hr : t.regs r = some (.bits 32 x)) :
    accessLoc L g t a = .ok ⟨.shared, g / L.block, wrapAddr 32 (truncBits 32 x) a.addr.off⟩ := by
  have hlt : (truncBits 32 x).toNat < 4294967296 := by
    unfold truncBits; rw [BitVec.toNat_ofNat]; omega
  simp [accessLoc, hs, hb, readReg, hr, readBits, hlt, bind, Except.bind, pure, Except.pure]

/-- An immediate reads as its low bits. -/
theorem readBits_imm {w : Nat} {v : Int} :
    readBits L g t w (.imm v) = .ok (truncBits w (BitVec.ofInt 64 v)) := rfl

/-- A register read as a value: a register holding a value of the access's size. -/
theorem readValue_reg {w r : Nat} {v : Value} (hr : t.regs r = some v) :
    readValue L g t w (.reg r) = .ok v := by
  simp [readValue, readReg, hr, pure, Except.pure]

/-- An immediate read for a store of width `w` is a `w`-bit value. -/
theorem readValue_imm {w : Nat} {n : Int} :
    ∃ v, readValue L g t w (.imm n) = .ok v ∧ v.bytes = w / 8 := by
  refine ⟨.bits w (truncBits w (BitVec.ofInt 64 n)), ?_, by simp [Value.bytes]⟩
  simp [readValue, readBits_imm, bind, Except.bind, pure, Except.pure]

/-- A register holding a bit pattern reads as its low bits. -/
theorem readBits_bits {r w w' : Nat} {x : BitVec 64} (hr : t.regs r = some (.bits w' x)) :
    readBits L g t w (.reg r) = .ok (truncBits w x) := by
  simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]

/-- An mbarrier at an aligned shared address held in a 32-bit register. -/
theorem mbarLoc_bits {base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (h8 : wrapAddr 32 (truncBits 32 x) off % 8 = 0) :
    mbarLoc L g t base off = .ok ⟨.shared, g / L.block, wrapAddr 32 (truncBits 32 x) off⟩ := by
  simp [mbarLoc, effAddr, sharedEffAddr, readReg, hr, readBits, wrapAddr] at h8 ⊢
  simp [h8, pure, Except.pure]

/-- A cluster-addressed mbarrier at an aligned shared address held in a 32-bit register. -/
theorem mbarClusterLoc_bits {base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (h8 : wrapAddr 32 (truncBits 32 x) off % 8 = 0) :
    mbarClusterLoc L g t base off =
      .ok ⟨.shared, g / L.block, wrapAddr 32 (truncBits 32 x) off⟩ := by
  simp [mbarClusterLoc, sharedEffAddr, readReg, hr, readBits, wrapAddr] at h8 ⊢
  simp [h8, pure, Except.pure]

/-- An `mbarrier.try_wait` on an aligned barrier address in a 32-bit register, with a parity
operand that reads, is not undefined behaviour. -/
theorem mbarWait_bits_ok {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    {x : BitVec 64} (hr : t.regs base = some (.bits 32 x))
    (h8 : wrapAddr 32 (truncBits 32 x) off % 8 = 0) (hq : ∃ q, readBits L g t 32 par = .ok q)
    (f : Fault) : eventTmpl A L g t (.mbarWait p base off par acq sc) ≠ .ub f := by
  obtain ⟨q, hq⟩ := hq
  exact wait_loc_ok (mbarLoc_bits hr h8) hq f

/-- An `mbarrier.arrive` (not cluster addressed) on an aligned barrier address in a 32-bit
register, with immediate byte count and arrival count, is not undefined behaviour. -/
theorem mbarArrive_imm_ok {base : Nat} {off : Int} {tx count : Int} {rel : Bool} {sc : MbarScope}
    {x : BitVec 64} (hr : t.regs base = some (.bits 32 x))
    (h8 : wrapAddr 32 (truncBits 32 x) off % 8 = 0) (f : Fault) :
    eventTmpl A L g t (.mbarArrive base off (.imm tx) (.imm count) false rel sc none) ≠ .ub f :=
  arrive_loc_ok (by simpa using mbarLoc_bits hr h8) rfl rfl f

/-- The launch facts a `tcgen05.commit` needs: valid cluster placement, one CTA per cluster. -/
theorem tcCommit_ok {group : CtaGroup} {base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (h8 : wrapAddr 32 (truncBits 32 x) off % 8 = 0)
    (hv : L.clusterGridValid) (hg : g < L.threads)
    (hunit : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) (hnc : L.nclusters = L.grid)
    (f : Fault) : eventTmpl A L g t (.tcCommit group base off none) ≠ .ub f := by
  have hblock : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · simp [Launch.threads, h] at hg
    · exact h
  have hgt : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hcn : g / L.block < L.nclusters := by rw [hnc]; exact hgt
  have hrank := Launch.rankOfCta_unit hunit hcn
  have hsz := Launch.clusterSizeOf_unit hunit (g / L.block)
  have hcl := Launch.clusterOfCta_unit hunit hcn
  have hres : TcCommit.resolve L group (g / L.block)
      ⟨.shared, g / L.block, wrapAddr 32 (truncBits 32 x) off⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) ≠ none := by
    unfold TcCommit.resolve
    split
    · simp
    · rename_i hn
      exact absurd ⟨hv, hgt, rfl, hgt, rfl, by rw [hrank, hsz]; simp⟩ hn
  simp only [eventTmpl, tcCommitTmpl, ofExec, mbarClusterLoc_bits hr h8, bind, Except.bind, pure,
    Except.pure, show g < L.threads from hg, ↓reduceIte]
  intro h
  cases hres' : TcCommit.resolve L group (g / L.block)
      ⟨.shared, g / L.block, wrapAddr 32 (truncBits 32 x) off⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) with
  | none => exact hres hres'
  | some s => simp [hres'] at h

/-- The address of a number plus a natural offset, below `2 ^ 32`, in a 32-bit shared window. -/
theorem wrapAddr_ofNat {n off : Nat} (h : n + off < 2 ^ 32) :
    wrapAddr 32 (truncBits 32 (BitVec.ofNat 64 n)) (off : Int) = n + off := by
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- A register of a fact list `factsFrom live vf` that is live holds its value. -/
theorem holds_reg {R : Nat → Option Value} {live : List Nat} {vf : Nat → Value} {r : Nat}
    {v : Value} (hH : Holds R (Flow.factsFrom live vf)) (hl : r ∈ live) (hv : vf r = v) :
    R r = some v :=
  holds_mem hH (hv ▸ Flow.mem_factsFrom hl)

/-- The shared base word, as the code's `mov.b32` makes it, when the window is in range. -/
theorem baseW_eq {sb : Nat} (h : sb < 2 ^ 32) :
    truncBits 32 (BitVec.ofNat 64 (sb + 0)) = BitVec.ofNat 64 sb := by
  simpa using truncBits_ofNat (w := 32) (n := sb) h (by omega)

/-- A Tensor Memory allocation of 512 columns (an immediate count), storing its address to a
4-aligned shared word held in a 32-bit register, is not undefined behaviour at its request
(`sub = 0`) or its address store. -/
theorem tcAlloc_imm_ok {grp : CtaGroup} {base a : Nat} (hb : L.block % 32 = 0)
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h4 : a % 4 = 0) (f : Fault) :
    eventTmpl A L g t (.tcAlloc grp base 0 (.imm 512)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, readBits_imm, hb, bind, Except.bind, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 512)).toNat = 512 by decide]
  by_cases hs : t.sub = 0 <;> simp [Tmem.validColumns, h4, hs, ofExec]

/-- A Tensor Memory deallocation of 512 columns (an immediate count) at an address register
whose value has a bit pattern is not undefined behaviour. -/
theorem tcDealloc_imm_ok {grp : CtaGroup} {ra : Nat} {v : Value} {x : BitVec 64}
    (hb : L.block % 32 = 0) (hra : t.regs ra = some v) (hv : v.regBits = some x) (f : Fault) :
    eventTmpl A L g t (.tcDealloc grp (.reg ra) (.imm 512)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, readBits_regBits hra hv, readBits_imm, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 512)).toNat = 512 by decide]
  simp [Tmem.validColumns, ofExec]

/-- A `bar.sync` with an immediate barrier in `0 .. 15` and no count. -/
theorem barSync_int_ok {id : Int} (h0 : 0 ≤ id) (h16 : id < 16) {al : Bool} (f : Fault) :
    eventTmpl A L g t (.barSync (.imm id) al) ≠ .ub f := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  exact barSync_imm_ok (by omega) f

/-- A `bar.sync` or `bar.arrive` with immediate operands: a barrier in `0 .. 15` and a nonzero
count that is a multiple of 32. -/
theorem barN_int_ok {id n : Int} (h0 : 0 ≤ id) (h16 : id < 16) (hn0 : 0 < n)
    (hn : n < 2 ^ 31) (hn32 : n % 32 = 0) {al : Bool} (f : Fault) :
    eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al) ≠ .ub f := by
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn0.le
  exact (bar_ok (by omega) (by omega) (by omega) (by omega) f).1

/-- An `mbarrier.init` of an aligned barrier address in a 32-bit register, with the immediate
arrival count 1. -/
theorem mbarInit_one_ok {base a : Nat} (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (h8 : a % 8 = 0) (f : Fault) :
    eventTmpl A L g t (.mbarInit base 0 (.imm 1)) ≠ .ub f := by
  have h1 : (truncBits 32 (BitVec.ofNat 64 1)).toNat = 1 := by decide
  simp [eventTmpl, tmaTmpl, mbarLoc_b32 hr ha h8, readBits_imm, h1, ofExec, widenMbarScope, bind,
    Except.bind, pure, Except.pure]

/-- The warp collectives with immediate operands only: the full-mask election and warp
barrier. -/
def staticWarp : WarpInstr → Bool
  | ⟨.elect, _, [_, some _], [], some (.imm (-1))⟩ => true
  | ⟨.barWarp, _, [], [], some (.imm (-1))⟩ => true
  | _ => false

theorem staticWarp_ok {w : WarpInstr} (h : staticWarp w = true) (f : Fault) :
    eventTmpl A L g t (.warp w) ≠ .ub f := by
  unfold staticWarp at h
  split at h
  · exact elect_imm_ok f
  · exact warpBar_ok f
  · simp at h

/-- The instructions whose event does not depend on any register: the plain ones, the named
barriers and the full-mask election and warp barrier with immediate operands. -/
def staticOk : Op → Bool
  | .barSync (.imm id) _ => decide (0 ≤ id ∧ id < 16)
  | .barSyncN (.imm id) (.imm n) _ =>
    decide (0 ≤ id ∧ id < 16 ∧ 0 < n ∧ n < 2 ^ 31 ∧ n % 32 = 0)
  | .warp w => staticWarp w
  | op => plainOk op

/-- The instruction at `pc` is static. -/
def staticAt (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ins => staticOk ins.op
  | none => false

set_option linter.unnecessarySimpa false in
/-- **A static instruction's event template is not undefined behaviour.** -/
theorem static_tmpl {pc : Nat} {ins : Instr} (hb : L.block % 32 = 0) (h : staticAt pc = true)
    (hc : kernel.code[pc]? = some ins) (f : Fault) :
    eventTmpl A L g t ins.op ≠ .ub f := by
  simp only [staticAt, hc] at h
  obtain ⟨gd, op⟩ := ins
  simp only at h ⊢
  cases op
  case barSync a al =>
    cases a <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    case imm id =>
      simp only [staticOk, decide_eq_true_eq] at h
      exact barSync_int_ok h.1 h.2 f
  case barSyncN a b al =>
    cases a <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    cases b <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    rename_i id n
    simp only [staticOk, decide_eq_true_eq] at h
    exact barN_int_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 f
  case warp w => exact staticWarp_ok (by simpa [staticOk] using h) f
  all_goals first
    | (simp [staticOk, plainOk] at h; done)
    | exact plainOk_tmpl hb (by simpa [staticOk, plainOk] using h) f

end
end PTX.Kernels.InklingRelDecode.Proof.Tm
