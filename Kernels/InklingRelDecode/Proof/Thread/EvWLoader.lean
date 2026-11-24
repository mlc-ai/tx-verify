-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWBase
public import Kernels.InklingRelDecode.Proof.Thread.LoaderRing
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.UbStop

@[expose] public section

/-!
# The event shapes of the loader warp

For each state `d` of the loader (`Loader.D`) the event its next instruction performs, as a
function of the state. `LdShape Q L g d e` says what `e` is when it fires at `d`:

* the poll of the ring slot's `kv_empty` barrier: the barrier `kvEmpty (d.i % 3)`, the parity
  `1 - (d.i / 3) % 2`, acquire at CTA scope; either outcome;
* the arrival on `kv_ready (d.i % 3)` of lane 0, `expect_tx 65536`, count 1, release at CTA scope;
* the block-table loads (`ldb0`, `ldb1`): four bytes of global memory at the address register of
  the slab, which the state's counters determine (`ldBtAddr`);
* the `(num_pre, num_iters)` shared load: the two four-byte elements at `global_smem + 212992`;
* the eight tensor copies of the iteration, `cp0a … cp3b`: the copy `ldCopy` (box K low and high
  half and V low and high half of slab 0, then of slab 1): the `kv_rows` map at `Q.kvMap`, the
  origin `(col, row)` read as signed 32-bit integers, the destination in the ring slot
  `d.i % 3`, the barrier `kvReady (d.i % 3)`, non-cluster addressing, one CTA group;
* the barrier events (`bar.sync 1`, `bar.warp.sync`, the elections, the register adjustments).

The origin of a copy is a function of the loop's words: the column
`w70 · ctaid.y + 128 [V] + 64 hh` and the row `p_slab · w68 + w69 · ctaid.y`, modulo `2 ^ 32`,
where `w68 … w71` are the parameter words the role inherited (`Loader.Pro`), `p_slab` the
block-table word of the slab (`d.p0`, `d.p1`, the words the loads returned) and `ctaid.y` the KV
head. `ldCopy_origin` states that, with `Q`'s fields in place of the inherited words, they are the
quantities of `Spec` (`kvh · head_cols + 128 [V] + 64 hh`, `page · page_rows + kvh · head_rows`)
whenever those stay below `2 ^ 31`.

The statements name sites by the constructors of `Loader.Site` and read the state's fields; the
program counter of the event is `Loader.Site.pc` of the state's site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {d : Loader.D} {t u : TState}
  {e : Event} {ins : Instr}

/-! ### The inherited words the loader reads -/

/-- `stride_bt`, `page_rows`, `head_rows`, `head_cols` and `num_splits`, as the 32-bit words the
loader inherited. -/
def ldStrideBt (d : Loader.D) : Nat := Loader.natOf (d.pro 528)
def ldPageRows (d : Loader.D) : Nat := Loader.natOf (d.pro 529)
def ldHeadRows (d : Loader.D) : Nat := Loader.natOf (d.pro 530)
def ldHeadCols (d : Loader.D) : Nat := Loader.natOf (d.pro 531)
def ldSplits (d : Loader.D) : Nat := Loader.natOf (d.pro 532)

/-- The base pointer of the block table, as the inherited 64-bit word. -/
def ldBtBase (d : Loader.D) : Nat := Loader.natOf64 (d.pro 2020)

/-- The pointer the K/V copies read as their tensor-map operand. -/
def ldMapPtr (d : Loader.D) : Value := d.pro 1949

/-! ### The quantities of a state -/

/-- The box a copy site moves: whether it is a V box, its 64-key slab and its column half. -/
def ldBox : Loader.Site → Option (Bool × Nat × Nat)
  | .cp0a => some (false, 0, 0) | .cp0b => some (false, 0, 1)
  | .cp1a => some (true, 0, 0) | .cp1b => some (true, 0, 1)
  | .cp2a => some (false, 1, 0) | .cp2b => some (false, 1, 1)
  | .cp3a => some (true, 1, 0) | .cp3b => some (true, 1, 1)
  | _ => none

/-- The origin column of a box: `w70 · ctaid.y + 128 [V] + 64 hh` (32-bit). -/
def ldCol (L : Launch) (g : Nat) (d : Loader.D) (isV : Bool) (hh : Nat) : Nat :=
  (ldHeadCols d * Loader.ctaY L g + (if isV then 128 else 0) + 64 * hh) % 2 ^ 32

/-- The origin row of a slab: `p_slab · w68 + w69 · ctaid.y` (32-bit), `p_slab` the slab's
block-table word. -/
def ldRow (L : Launch) (g : Nat) (d : Loader.D) (slab : Nat) : Nat :=
  ((if slab = 0 then d.p0 else d.p1) * ldPageRows d +
    ldHeadRows d * Loader.ctaY L g) % 2 ^ 32

/-- The shared destination of a box in the ring slot of the iteration. -/
def ldDst (L : Launch) (d : Loader.D) (isV : Bool) (slab hh : Nat) : Nat :=
  L.sharedBase + 32768 * (d.i % 3) + (if isV then 98304 else 0) + 8192 * slab + 16384 * hh

/-- The copy a loader state issues for box `(isV, slab, hh)`. -/
def ldCopy (Q : Params) (L : Launch) (g : Nat) (d : Loader.D) (b : Bool × Nat × Nat) :
    TensorCopy.Spec :=
  kvCopySpec Q (g / L.block) (ldCol L g d b.1 b.2.2) (ldRow L g d b.2.1) (ldDst L d b.1 b.2.1 b.2.2)
    (kvReady L (g / L.block) (d.i % 3))

/-- The 64-bit address register of slab 0's block-table word, as the code computes it from the
loop's words: `bt + 4 · (sext(w67 · ctaid.z)) + 4 · (sext(128 · (w71 i + ctaid.x)) >> 6)`. -/
def ldBtAddr0 (L : Launch) (g : Nat) (d : Loader.D) : BitVec 64 :=
  let w67 := ldStrideBt d
  let w71 := ldSplits d
  let bt := ldBtBase d
  let r1441 := 128 * ((w71 * d.i + Loader.ctaX L g) % 2 ^ 32) % 2 ^ 32
  let rd2 := (bt + 4 * Loader.sx32 (w67 * Loader.ctaZ L g)) % 2 ^ 64
  Loader.madWideW (Loader.sarW (BitVec.ofNat 64 r1441) (BitVec.ofInt 64 6)) (BitVec.ofInt 64 4)
    (BitVec.ofNat 64 rd2)

/-- The address of the block-table word of slab `slab`: slab 1's is four bytes above slab 0's. -/
def ldBtAddr (L : Launch) (g : Nat) (d : Loader.D) (slab : Nat) : Nat :=
  (if slab = 0 then ldBtAddr0 L g d else Loader.add64W (ldBtAddr0 L g d) (BitVec.ofInt 64 4)).toNat

/-! ### The shape of the event at a state -/

/-- **What the event fired at loader state `d` is.** -/
def LdShape (Q : Params) (L : Launch) (g : Nat) (d : Loader.D) (e : Event) : Prop :=
  match d.site with
  | .setMaxDec => ∃ inst, e = ⟨d.site.pc, .setMaxReg false 24 inst⟩
  | .ld0 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212992⟩ ∧ ac.size = 4 ∧ ac.elem = 0
  | .ld1 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4⟩ ∧ ac.size = 4 ∧ ac.elem = 1
  | .bar0 | .bar1 => e = ⟨d.site.pc, .bar 1 none .sync⟩
  | .wait => ∃ ok, e = ⟨d.site.pc, .wait (kvEmpty L (g / L.block) (d.i % 3))
      (1 - d.i / 3 % 2) ok true .cta⟩
  | .wb0 | .wb1 | .wb2 | .wb3 | .wb4 => ∃ inst, e = ⟨d.site.pc, .warpBar 4294967295 inst⟩
  | .arrive => e = ⟨d.site.pc, .arrive (kvReady L (g / L.block) (d.i % 3)) 65536 1 true .cta⟩
  | .ldb0 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.global, 0, ldBtAddr L g d 0⟩ ∧ ac.size = 4
  | .ldb1 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.global, 0, ldBtAddr L g d 1⟩ ∧ ac.size = 4
  | .el0 | .el1 | .el2 | .el3 => ∃ inst ld, e = ⟨d.site.pc, .elect 4294967295 inst ld⟩
  | .cp0a | .cp0b | .cp1a | .cp1b | .cp2a | .cp2b | .cp3a | .cp3b =>
      ∃ b, ldBox d.site = some b ∧ e = ⟨d.site.pc, .tensorIssue Q.kvMap (ldCopy Q L g d b)⟩
  | .setMaxInc => ∃ inst, e = ⟨d.site.pc, .setMaxReg true 256 inst⟩

/-! ### The shape for every counter

The poll, the arrival and the copies address the ring through the slot offsets the code computes
from the counter (`Loader.bOff`, `Loader.kOff`, `Loader.parW`). For a counter below `2 ^ 31` they
are the slot `i % 3` and the parity `1 - (i / 3) % 2` (`LdShapeW.shape`); for a larger word the
slot remainder is `-2 … 0`, so the barriers are 8 or 16 bytes below the slot-0 ones or slot 0's,
and a copy lands at most `65536` bytes below the rings or wraps to the top of the 32-bit space
(`ldDstW_range`). `LdShapeW` is `LdShape` with these addresses. -/

/-- The `kv_empty` barrier the poll of counter `i` names. -/
def ldEmptyW (L : Launch) (cta i : Nat) : Loc :=
  ⟨.shared, cta, (L.sharedBase + Loader.bOff i + 213248) % 2 ^ 32⟩

/-- The `kv_ready` barrier the arrival and the copies of counter `i` name. -/
def ldReadyW (L : Launch) (cta i : Nat) : Loc :=
  ⟨.shared, cta, (L.sharedBase + Loader.bOff i + 213216) % 2 ^ 32⟩

/-- The shared destination of a box at counter `d.i`, as the code computes it. -/
def ldDstW (L : Launch) (d : Loader.D) (isV : Bool) (slab hh : Nat) : Nat :=
  (L.sharedBase + Loader.kOff d.i + (if isV then 98304 else 0) + 8192 * slab + 16384 * hh) %
    2 ^ 32

/-- The copy a loader state issues for box `(isV, slab, hh)`, for every counter. -/
def ldCopyW (Q : Params) (L : Launch) (g : Nat) (d : Loader.D) (b : Bool × Nat × Nat) :
    TensorCopy.Spec :=
  kvCopySpec Q (g / L.block) (ldCol L g d b.1 b.2.2) (ldRow L g d b.2.1)
    (ldDstW L d b.1 b.2.1 b.2.2) (ldReadyW L (g / L.block) d.i)

/-- **What the event fired at loader state `d` is, for every counter.** -/
def LdShapeW (Q : Params) (L : Launch) (g : Nat) (d : Loader.D) (e : Event) : Prop :=
  match d.site with
  | .setMaxDec => ∃ inst, e = ⟨d.site.pc, .setMaxReg false 24 inst⟩
  | .ld0 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212992⟩ ∧ ac.size = 4 ∧ ac.elem = 0
  | .ld1 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4⟩ ∧ ac.size = 4 ∧ ac.elem = 1
  | .bar0 | .bar1 => e = ⟨d.site.pc, .bar 1 none .sync⟩
  | .wait => ∃ ok, e = ⟨d.site.pc, .wait (ldEmptyW L (g / L.block) d.i) (Loader.parW d.i) ok
      true .cta⟩
  | .wb0 | .wb1 | .wb2 | .wb3 | .wb4 => ∃ inst, e = ⟨d.site.pc, .warpBar 4294967295 inst⟩
  | .arrive => e = ⟨d.site.pc, .arrive (ldReadyW L (g / L.block) d.i) 65536 1 true .cta⟩
  | .ldb0 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.global, 0, ldBtAddr L g d 0⟩ ∧ ac.size = 4
  | .ldb1 => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.global, 0, ldBtAddr L g d 1⟩ ∧ ac.size = 4
  | .el0 | .el1 | .el2 | .el3 => ∃ inst ld, e = ⟨d.site.pc, .elect 4294967295 inst ld⟩
  | .cp0a | .cp0b | .cp1a | .cp1b | .cp2a | .cp2b | .cp3a | .cp3b =>
      ∃ b, ldBox d.site = some b ∧ e = ⟨d.site.pc, .tensorIssue Q.kvMap (ldCopyW Q L g d b)⟩
  | .setMaxInc => ∃ inst, e = ⟨d.site.pc, .setMaxReg true 256 inst⟩

/-! ### The sites -/

/-- A live register of the state's site holds the state's value. -/
theorem reg_of {r : Nat} (h : Loader.AtS L g d t) (hl : r ∈ Flow.live d.site.pc) :
    t.regs r = some (Loader.valueOf L g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The shared base leaves room for every offset the loader's barriers and tiles use. -/
def SbOk (L : Launch) : Prop := L.sharedBase + 2 ^ 18 < 2 ^ 32

theorem sbOk_of_pre (hpre : Pre Q L mem0) : SbOk L := by
  have := hpre.sharedRange
  unfold sharedBytes at this
  unfold SbOk
  omega

/-- The `(num_pre, num_iters)` load: the two elements of the vector at `global_smem + 212992`. -/
theorem shapeAt_ldv (hb : SbOk L) {P : Loader.Pro} (d : Loader.D)
    (hs : d.site = .ld0 ∨ d.site = .ld1) :
    (Loader.code L g P).ShapeAt (OrUb (LdShapeW Q L g)) d := by
  intro t ins e o h _ hc hf
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ : ∃ a : MemAccess,
      kernel.code[2345]? = some ⟨none, .mem a⟩ ∧ a.rule = some .threadAccess ∧
      a.addr.base = .sharedSym 0 ∧ a.addr.off = ((212992 : Nat) : Int) ∧ a.kind = .load ∧
      a.nc = false ∧ a.space = some (.shared .cta) ∧ a.sem = .weak ∧
      (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && a.elem.width == 64)) = false ∧
      a.elem.width = 32 :=
    ⟨_, Flow.code_2345, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hs
  have hc' : kernel.code[2345]? = some ins := by rcases hs with rfl | rfl <;> exact hc
  obtain rfl := Option.some.inj (hc'.symm.trans ha1)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  obtain ⟨ac, bs, he, hl, hsz, hel⟩ := fires_ldv_sharedSym ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10
    (by unfold SbOk at hb; omega) hf
  have hsub := h.2.1
  rcases hs with rfl | rfl <;> simp only [Loader.sub] at hsub <;> rw [hsub] at hl hel <;>
    exact ⟨ac, bs, he, by simpa using hl, hsz, hel⟩

theorem shape_cp_core (hpre : Pre Q L mem0)
    (hmap : ldMapPtr d = .ptr 64 true (.param (param "1")) 0) (h : Loader.AtS L g d t)
    {b : Bool × Nat × Nat} {dstR cR rR : Nat}
    (hl : dstR ∈ Flow.live d.site.pc ∧ cR ∈ Flow.live d.site.pc ∧ rR ∈ Flow.live d.site.pc ∧
      580 ∈ Flow.live d.site.pc ∧ 1949 ∈ Flow.live d.site.pc)
    (hdst : Loader.valueOf L g d dstR = b32 (ldDstW L d b.1 b.2.1 b.2.2))
    (hcol : Loader.valueOf L g d cR = b32 (ldCol L g d b.1 b.2.2))
    (hrow : Loader.valueOf L g d rR = b32 (ldRow L g d b.2.1))
    (hf : Fires d.site.pc (eventTmpl Loader.asms L g t (.cpTensor false false dstR 0 (.reg 1949)
      [.reg cR, .reg rR] 580 0 none .tile)) e (some u)) :
    e = ⟨d.site.pc, .tensorIssue Q.kvMap (ldCopyW Q L g d b)⟩ := by
  unfold ldMapPtr at hmap
  have r580 := reg_of (r := 580) h hl.2.2.2.1
  have rmap := reg_of (r := 1949) h hl.2.2.2.2
  have rd := reg_of (r := dstR) h hl.1
  have rc := reg_of (r := cR) h hl.2.1
  have rr := reg_of (r := rR) h hl.2.2.1
  rw [hdst] at rd
  rw [hcol] at rc
  rw [hrow] at rr
  simp only [Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none] at r580 rmap
  have hw := Loader.barc_word L d.i 213216
  simp only [Nat.cast_ofNat] at hw
  rw [hw] at r580
  rw [hmap] at rmap
  obtain ⟨he, -⟩ := fires_kvCopy hpre rmap rd r580 rc rr (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hf
  rw [he]
  rfl

/-- The table's values of the two coordinate registers of a copy. -/
macro "ev_col" : tactic => `(tactic| (
  simp only [Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_some, ldCol,
    ldHeadCols]
  simp))

macro "ev_row" : tactic => `(tactic| (
  simp only [Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_some, ldRow,
    ldPageRows, ldHeadRows]
  simp))

theorem kvc_word_lit (L : Launch) (i c : Nat) :
    Loader.addW (Loader.kvW L i) (BitVec.ofInt 64 (OfNat.ofNat c)) =
      BitVec.ofNat 64 ((L.sharedBase + Loader.kOff i + c) % 2 ^ 32) :=
  Loader.kvc_word L i c

/-- The table's value of a shared-destination register of the loop. -/
macro "ev_dst" : tactic => `(tactic| (
  simp only [Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_some, ldDstW]
  first
  | (rw [kvc_word_lit L]; simp [b32])
  | (rw [Loader.kv_word L]; simp [b32])))

/-- **The copy of box `b` at `pc`**, with the destination in `dstR` and the coordinates in `cR`
and `rR` (`shape_cp_core`). -/
theorem shapeAt_cp (hpre : Pre Q L mem0) {P : Loader.Pro}
    (hmap : ldMapPtr d = .ptr 64 true (.param (param "1")) 0)
    {s : Loader.Site} {b : Bool × Nat × Nat} {pc dstR cR rR : Nat} {gd : Option (Nat × Bool)}
    (hcode : kernel.code[pc]? = some ⟨gd, .cpTensor false false dstR 0 (.reg 1949)
      [.reg cR, .reg rR] 580 0 none .tile none⟩)
    (hs : d.site = s) (hpc : s.pc = pc := by rfl) (hb : ldBox s = some b := by rfl)
    (hl : dstR ∈ Flow.live pc ∧ cR ∈ Flow.live pc ∧ rR ∈ Flow.live pc ∧ 580 ∈ Flow.live pc ∧
      1949 ∈ Flow.live pc := by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> table_decide)
    (hdst : ∀ d, Loader.valueOf L g d dstR = b32 (ldDstW L d b.1 b.2.1 b.2.2) := by
      intro; ev_dst)
    (hcol : ∀ d, Loader.valueOf L g d cR = b32 (ldCol L g d b.1 b.2.2) := by intro; ev_col)
    (hrow : ∀ d, Loader.valueOf L g d rR = b32 (ldRow L g d b.2.1) := by intro; ev_row) :
    (Loader.code L g P).ShapeAt (OrUb (LdShapeW Q L g)) d := by
  intro t ins e o h _ hc hf
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hs
  subst hs hpc
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  have hw : LdShapeW Q L g ⟨site, pro, i, n, p0, p1, ln⟩ e ↔ ∃ b, ldBox site = some b ∧
      e = ⟨site.pc, .tensorIssue Q.kvMap (ldCopyW Q L g ⟨site, pro, i, n, p0, p1, ln⟩ b)⟩ := by
    cases site <;> simp_all [LdShapeW, ldBox]
  exact hw.2 ⟨b, hb, shape_cp_core hpre hmap h hl (hdst _) (hcol _) (hrow _) hf⟩

theorem barc_word_lit (L : Launch) (i c : Nat) :
    Loader.addW (Loader.barW L i) (BitVec.ofInt 64 (OfNat.ofNat c)) =
      BitVec.ofNat 64 ((L.sharedBase + Loader.bOff i + c) % 2 ^ 32) :=
  Loader.barc_word L i c

/-- The parity the poll reads from its 32-bit register. -/
theorem par_read (i : Nat) :
    (truncBits 32 (Loader.andW (Loader.notW (Loader.quotW i)) (BitVec.ofInt 64 1))).toNat % 2 =
      Loader.parW i := by
  have h := Loader.parW_lt i
  unfold Loader.parW at h ⊢
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- The address of a global load whose register holds a 64-bit word, offset 0. -/
theorem toNat_trunc64_add0 (x : BitVec 64) :
    (truncBits 64 x + BitVec.ofInt 64 0).toNat = x.toNat := by
  simp [truncBits, Nat.mod_eq_of_lt x.isLt]

set_option hygiene false in
/-- The loader's side conditions: the block, the aligned mbarrier addresses of the poll and the
arrival. -/
macro "ld_addr" : tactic => `(tactic| first
  | rw [hpre.block]
  | (apply mbarLoc_b32_ok
     case hr =>
       exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by
         simp only [Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_some]
         rw [barc_word_lit]; rfl)
     case ha => exact Nat.mod_lt _ (by norm_num)
     case hal =>
       have := hpre.sharedAlignment
       rcases Loader.bOff_cases i with h | h | h | h | h <;> rw [h] <;> simp only <;> omega))

/-- **The loader's shape table, for every counter**, at the states whose inherited map register
is the pointer to the kernel's tensor-map parameter. -/
theorem ldShapeAt (hpre : Pre Q L mem0) (P : Loader.Pro) (d : Loader.D)
    (hmap : ldMapPtr d = .ptr 64 true (.param (param "1")) 0) :
    (Loader.code L g P).ShapeAt (OrUb (LdShapeW Q L g)) d := by
  have hb := sbOk_of_pre hpre
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  site_shape s
    except [.ld0 => fun {_ _ _ _} => shapeAt_ldv hb ⟨_, pro, i, n, p0, p1, ln⟩ (.inl rfl),
      .ld1 => fun {_ _ _ _} => shapeAt_ldv hb ⟨_, pro, i, n, p0, p1, ln⟩ (.inr rfl),
      .cp0a => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_12 rfl,
      .cp0b => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_13 rfl,
      .cp1a => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_14 rfl,
      .cp1b => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_15 rfl,
      .cp2a => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_16 rfl,
      .cp2b => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_17 rfl,
      .cp3a => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_18 rfl,
      .cp3b => fun {_ _ _ _} => shapeAt_cp hpre hmap Flow.code_tensorCopy_19 rfl]
    unfolding [OrUb, LdShapeW, ldEmptyW, ldReadyW, par_read, toNat_trunc64_add0, Loc.at,
      Nat.mul_zero, Nat.add_zero, ldBtAddr, ldBtAddr0, ldStrideBt, ldSplits,
      ldBtBase, Loader.add64W]
    reg_vals [Loader.valueOf, Loader.table, lookupLit]
    addr_by (ld_addr)

/-- **The event fired at a loader state is its shape, for every counter.** -/
theorem ld_shapeW (hpre : Pre Q L mem0) {P : Loader.Pro}
    (hmap : ldMapPtr d = .ptr 64 true (.param (param "1")) 0)
    (h : Loader.AtS L g d t) (hi : Loader.Inv L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Loader.asms L g t ins.op) e (some u)) :
    LdShapeW Q L g d e :=
  OrUb.of_some (ldShapeAt hpre P d hmap h hi hc hf) hf

/-! ### Below `2 ^ 31` -/

theorem ldEmptyW_eq (hb : SbOk L) (cta : Nat) {i : Nat} (hi : i < 2 ^ 31) :
    ldEmptyW L cta i = kvEmpty L cta (i % 3) := by
  unfold SbOk at hb
  have h3 := Nat.mod_lt i (show 3 > 0 by omega)
  have hm : (L.sharedBase + 8 * (i % 3) + 213248) % 2 ^ 32 =
      L.sharedBase + (213248 + 8 * (i % 3)) := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [ldEmptyW, kvEmpty, barLoc, kvEmptyOff, Loader.bOff_eq hi, hm]

theorem ldReadyW_eq (hb : SbOk L) (cta : Nat) {i : Nat} (hi : i < 2 ^ 31) :
    ldReadyW L cta i = kvReady L cta (i % 3) := by
  unfold SbOk at hb
  have h3 := Nat.mod_lt i (show 3 > 0 by omega)
  have hm : (L.sharedBase + 8 * (i % 3) + 213216) % 2 ^ 32 =
      L.sharedBase + (213216 + 8 * (i % 3)) := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [ldReadyW, kvReady, barLoc, kvReadyOff, Loader.bOff_eq hi, hm]

theorem ldDstW_eq (hb : SbOk L) (hi : d.i < 2 ^ 31) {isV : Bool} {slab hh : Nat}
    (hs : slab ≤ 1) (hh1 : hh ≤ 1) : ldDstW L d isV slab hh = ldDst L d isV slab hh := by
  unfold SbOk at hb
  have h3 := Nat.mod_lt d.i (show 3 > 0 by omega)
  unfold ldDstW ldDst
  rw [Loader.kOff_eq hi]
  split_ifs <;> omega

theorem ldBox_le {s : Loader.Site} {b : Bool × Nat × Nat} (hbx : ldBox s = some b) :
    b.2.1 ≤ 1 ∧ b.2.2 ≤ 1 := by
  revert hbx
  cases s <;> simp [ldBox] <;> intro h <;> subst h <;> simp

theorem ldCopyW_eq (hb : SbOk L) (hi : d.i < 2 ^ 31) {b : Bool × Nat × Nat}
    (hbx : ldBox d.site = some b) : ldCopyW Q L g d b = ldCopy Q L g d b := by
  have hb' := ldBox_le hbx
  unfold ldCopyW ldCopy
  rw [ldDstW_eq hb hi hb'.1 hb'.2, ldReadyW_eq hb _ hi]

/-- **The shape below `2 ^ 31`.** At a state whose counter is below `2 ^ 31` where the
iteration's sites use it, `LdShapeW` is `LdShape`. -/
theorem LdShapeW.shape (hb : SbOk L) (hrg : d.site.iBounded = true → d.i < 2 ^ 31)
    (h : LdShapeW Q L g d e) : LdShape Q L g d e := by
  unfold LdShapeW at h
  unfold LdShape
  cases hsite : d.site <;> rw [hsite] at h
  case wait =>
    have hi := hrg (by rw [hsite]; rfl)
    obtain ⟨ok, he⟩ := h
    exact ⟨ok, by rw [he, ldEmptyW_eq hb _ hi, Loader.parW_eq hi]⟩
  case arrive =>
    have hi := hrg (by rw [hsite]; rfl)
    rw [h, ldReadyW_eq hb _ hi]
  case cp0a | cp0b | cp1a | cp1b | cp2a | cp2b | cp3a | cp3b =>
    have hi := hrg (by rw [hsite]; rfl)
    obtain ⟨b, hbx, he⟩ := h
    refine ⟨b, hbx, ?_⟩
    rw [he, ldCopyW_eq hb hi (by rw [hsite]; exact hbx)]
  all_goals exact h

/-- **The destination of a copy, for every counter**: within `65536` bytes below the rings and
not above them, or wrapped to the top `65536` bytes of the 32-bit space. -/
theorem ldDstW_range (hsr : L.sharedBase + 213340 ≤ 2 ^ 18) {b : Bool × Nat × Nat}
    (hb : ldBox d.site = some b) :
    (L.sharedBase ≤ ldDstW L d b.1 b.2.1 b.2.2 + 65536 ∧
      ldDstW L d b.1 b.2.1 b.2.2 + 8192 ≤ L.sharedBase + 196608) ∨
    2 ^ 32 - 65536 ≤ ldDstW L d b.1 b.2.1 b.2.2 := by
  have hb' := ldBox_le hb
  have hk := Loader.kOff_cases d.i
  unfold ldDstW
  rcases (by omega : b.2.1 = 0 ∨ b.2.1 = 1) with h2 | h2 <;>
    rcases (by omega : b.2.2 = 0 ∨ b.2.2 = 1) with h3 | h3 <;> rw [h2, h3] <;> split_ifs <;>
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
