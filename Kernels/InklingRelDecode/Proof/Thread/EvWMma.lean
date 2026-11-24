-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWTc
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.UbStop

@[expose] public section

/-!
# The event shapes of the MMA warp

For each state `d` of the MMA warp (`Mma.D`: the site, the iteration `i`, `num_iters` `n`, the
Tensor Memory base `tm`) the event its next instruction performs, as a function of the state.
`MmShape L g d e` says what `e` is when it fires at `d`, with `cta = g / L.block`:

* the QK half of iteration `i`: the poll of `kv_ready (i % 3)` for parity `(i / 3) % 2`; the eight
  MMAs `qk j`: destination column `tm + 128 (i % 2)`, accumulate off for `j = 0` and on after, A
  the Q tile (shared descriptor start `qLo + 2 (j % 4) + 512 (j / 4)`), B the K tile of ring slot
  `i % 3` (start `kLo (i % 3) + 2 (j % 4) + 1024 (j / 4)`), the decoding of the QK instruction
  descriptor; then the commit to `s_ready (i % 2)`;
* the PV half, for the block `i - 1`: the poll of `p_ready ((i - 1) % 2)` for parity
  `((i - 1) / 2) % 2`; the eight MMAs `pv j`: destination column `tm + 256`, accumulate on except
  for `j = 0` of block 0, A the P tile in Tensor Memory at `tm + 128 ((i - 1) % 2) + 8 j`, B the V
  tile of slot `(i - 1) % 3` (start `vLo ((i - 1) % 3) + 128 j`, bit 26 set), the decoding of the PV
  instruction descriptor; then the commits to `kv_empty ((i - 1) % 3)` and `o_done`;
* after the loop the commit to `o_final`;
* the shared load of `num_iters`, the broadcasts of the warp index (the value 7, lane 0, the full
  warp), the warp barriers, the elections, `bar.sync 1` and the register adjustments.

An MMA event is `.tc (.mma c spec acc [0, 0, 0, 0])` with `spec = ⟨dsc, a, b, cta, cta, aTmem,
{}⟩`: `dsc` is the decoding of the instruction descriptor, `a` and `b` the decodings of the shared
descriptors (`TcShared.decode`), `aTmem` the A address in Tensor Memory or none. A commit is
`.tc (.commit (commitSpec cta m))`, `cta_group::1`, mask 1, cluster base `cta`, cluster size 1.

The facts about the launch these use are `Pre`'s: the grid has one-CTA clusters (`UnitCta`), the
shared base is 1024-aligned and `L.sharedBase + 213340 ≤ 2 ^ 18`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0} {d : Mma.D} {t u : TState}
  {e : Event} {ins : Instr}

/-! ### The quantities of a state -/

/-- The low word of the shared descriptor of the A operand (the Q tile) of QK MMA `j`. -/
def mmQkALo (L : Launch) (j : Nat) : Nat := Mma.qLo L + 2 * (j % 4) + 512 * (j / 4)

/-- The low word of the shared descriptor of the B operand (the K tile of slot `s`) of QK
MMA `j`. -/
def mmQkBLo (L : Launch) (s j : Nat) : Nat := Mma.kLo L s + 2 * (j % 4) + 1024 * (j / 4)

/-- The low word of the shared descriptor of the B operand (the V tile of slot `s`) of PV MMA
`j`, without bit 26. -/
def mmPvBLo (L : Launch) (s j : Nat) : Nat := Mma.vLo L s + 128 * j

/-- QK MMA `j` of iteration `i`, with Tensor Memory base `tm`, issued by a thread of CTA `cta`
at program counter `pc`. -/
def QkIssue (L : Launch) (cta tm i j pc : Nat) (e : Event) : Prop :=
  ∃ da db dsc, TcMma.decode .one false .f16 Mma.qkIdesc = some dsc ∧
    TcShared.decode (mmQkALo L j + Mma.descHi * 2 ^ 32) = some da ∧
    TcShared.decode (mmQkBLo L (i % 3) j + Mma.descHi * 2 ^ 32) = some db ∧
    e = ⟨pc, .tc (.mma (tm + 128 * (i % 2)) ⟨dsc, da, db, cta, cta, none, {}⟩ (decide (j ≠ 0))
      [0, 0, 0, 0])⟩

/-- PV MMA `j` of the block `i - 1`, with Tensor Memory base `tm`. -/
def PvIssue (L : Launch) (cta tm i j pc : Nat) (e : Event) : Prop :=
  ∃ db dsc, TcMma.decode .one false .f16 Mma.pvIdesc = some dsc ∧
    TcShared.decode (mmPvBLo L ((i - 1) % 3) j + 2 ^ 26 + Mma.descHi * 2 ^ 32) = some db ∧
    e = ⟨pc, .tc (.mma (tm + 256) ⟨dsc, db, db, cta, cta,
      some (tm + 128 * ((i - 1) % 2) + 8 * j), {}⟩ (decide (j ≠ 0 ∨ i ≠ 1)) [0, 0, 0, 0])⟩

/-! ### The shape of the event at a state -/

/-- **What the event fired at MMA state `d` is.** -/
def MmShape (L : Launch) (g : Nat) (d : Mma.D) (e : Event) : Prop :=
  match d.site with
  | .setMaxReg => ∃ inst, e = ⟨d.site.pc, .setMaxReg false 24 inst⟩
  | .ldNum => ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212996⟩ ∧ ac.size = 4
  | .bar0 | .bar1 => e = ⟨d.site.pc, .bar 1 none .sync⟩
  | .qkBar | .qkBar2 | .pvBar | .pvBar2 | .finBar | .qkSkip | .pvSkip =>
      ∃ inst, e = ⟨d.site.pc, .warpBar 4294967295 inst⟩
  | .kvWait => ∃ ok, e = ⟨d.site.pc, .wait (kvReady L (g / L.block) (d.i % 3))
      (d.i / 3 % 2) ok true .cta⟩
  | .pWait => ∃ ok, e = ⟨d.site.pc, .wait (pReady L (g / L.block) ((d.i - 1) % 2))
      ((d.i - 1) / 2 % 2) ok true .cta⟩
  | .qkShfl | .pvShfl =>
      ∃ recv ok, e = ⟨d.site.pc, .shfl .idx (b32 (Worker.warpOf L g)) 0 31 recv ok⟩
  | .qkElect | .pvElect | .finElect => ∃ inst ld, e = ⟨d.site.pc, .elect 4294967295 inst ld⟩
  | .qk j => QkIssue L (g / L.block) d.tm d.i j d.site.pc e
  | .qkCommit => e = ⟨d.site.pc, .tc (.commit (commitSpec (g / L.block)
      (sReady L (g / L.block) (d.i % 2))))⟩
  | .pv j => PvIssue L (g / L.block) d.tm d.i j d.site.pc e
  | .pvCommit1 => e = ⟨d.site.pc, .tc (.commit (commitSpec (g / L.block)
      (kvEmpty L (g / L.block) ((d.i - 1) % 3))))⟩
  | .pvCommit2 => e = ⟨d.site.pc, .tc (.commit (commitSpec (g / L.block)
      (oDone L (g / L.block))))⟩
  | .finCommit => e = ⟨d.site.pc, .tc (.commit (commitSpec (g / L.block)
      (oFinal L (g / L.block))))⟩
  | .setMaxRegInc => ∃ inst, e = ⟨d.site.pc, .setMaxReg true 256 inst⟩

/-! ### The sites -/

/-- A live register of the state's site holds the state's value. -/
theorem mm_reg {r : Nat} (h : At t d.site.pc (Mma.facts L d)) (hl : r ∈ Flow.live d.site.pc) :
    t.regs r = some (Mma.valueOf L d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- What the MMA warp's shapes read of the launch. -/
structure MmEnv (L : Launch) : Prop where
  sb : L.sharedBase + 213340 ≤ 2 ^ 18
  align : L.sharedBase % 1024 = 0

theorem mmEnv_of_pre (hpre : Pre Q L mem0) : MmEnv L := by
  have := hpre.sharedRange
  unfold sharedBytes at this
  exact ⟨by omega, hpre.sharedAlignment⟩

/-- The table's value of a register of the MMA warp's state. -/
macro "mm_val " h:ident : tactic => `(tactic| simp only [Mma.valueOf, Mma.values,
  PTX.Flow.lookupLit, Option.getD_some, Option.getD_none] at $h:ident)

/-- **QK MMA `j`**, at `pc`, with the A and B descriptors in `rA` and `rB` and the enable flag
in `rE`. -/
theorem mm_qk {j : Fin 8} {pc rA rB rE : Nat} {gd : Option (Nat × Bool)}
    (hcode : kernel.code[pc]? = some ⟨gd, .tcMma (.dense .one false .f16 547 (.smem (.reg rA))
      (.reg rB) (.reg 548) Mma.masks0 (.reg rE))⟩)
    (hE : MmEnv L) (hu : UnitCta L g) (hg : g < L.threads) {tm0 : Nat} {pro0 : Nat → Value}
    (hs : d.site = .qk j) (hpc : (Mma.Site.qk j).pc = pc := by rfl)
    (hl : ∀ r ∈ [547, rA, rB, 548, rE], r ∈ Flow.live pc := by table_decide)
    (hA : ∀ d : Mma.D, Mma.valueOf L d rA = Mma.desc (mmQkALo L j) := by intro; rfl)
    (hB : ∀ d : Mma.D, Mma.valueOf L d rB = Mma.desc (mmQkBLo L (d.i % 3) j) := by intro; rfl)
    (hen : ∀ d : Mma.D, Mma.valueOf L d rE = .pred (decide (j ≠ 0)) := by intro; rfl) :
    (Mma.code Loader.asms L g tm0 pro0).ShapeAt (OrUb (MmShape L g)) d := by
  intro t ins e o h hi hc hf
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only at hs
  subst hs
  change At t (⟨.qk j, i, n, tm, pro⟩ : Mma.D).site.pc (Mma.facts L ⟨.qk j, i, n, tm, pro⟩) at h
  subst hpc
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  have hb := hE.sb
  have hj := j.isLt
  have htm : tm + 512 < 2 ^ 32 := hi.tm
  have r547 := mm_reg (r := 547) h (hl 547 (by simp))
  have rA := mm_reg (r := rA) h (hl rA (by simp))
  have rB := mm_reg (r := rB) h (hl rB (by simp))
  have r548 := mm_reg (r := 548) h (hl 548 (by simp))
  have hrE := mm_reg (r := rE) h (hl rE (by simp))
  mm_val r547
  mm_val r548
  rw [hA] at rA
  rw [hB] at rB
  dsimp only at rB
  rw [hen] at hrE
  have hen' : mmaEnable t (.reg rE) = .ok (decide (j ≠ 0)) := by
    unfold mmaEnable
    simp only [readReg, hrE]
    rfl
  have hla : mmQkALo L j < 2 ^ 15 := by unfold mmQkALo Mma.qLo; omega
  have hlb : mmQkBLo L (i % 3) j < 2 ^ 15 := by unfold mmQkBLo Mma.kLo; omega
  obtain ⟨da, db, dsc, h1, h2, h3, he⟩ := fires_qk_event (peer_self hu) hg
    (c := tm + 128 * (i % 2)) r547 (by omega) rA (by omega) (by rw [Nat.div_eq_of_lt hla]) rB
    (by omega) (by rw [Nat.div_eq_of_lt hlb]) r548 hen' hf
  exact ⟨da, db, dsc, h1, h2, h3, he⟩

/-- **PV MMA `j`**, at `pc`, with the B descriptor in `rB`, the A columns at offset `aoff` and the
enable flag in `rE`. -/
theorem mm_pv {j : Fin 8} {pc rB rE : Nat} {aoff : Int} {gd : Option (Nat × Bool)}
    (hcode : kernel.code[pc]? = some ⟨gd, .tcMma (.dense .one false .f16 564 (.tmem 565 aoff)
      (.reg rB) (.reg 566) Mma.masks0 (.reg rE))⟩)
    (hE : MmEnv L) (hu : UnitCta L g) (hg : g < L.threads) {tm0 : Nat} {pro0 : Nat → Value}
    (hs : d.site = .pv j) (hpc : (Mma.Site.pv j).pc = pc := by rfl)
    (haoff : 0 ≤ aoff ∧ aoff.toNat = 8 * j := by decide)
    (hl : ∀ r ∈ [564, 565, rB, 566, rE], r ∈ Flow.live pc := by table_decide)
    (hB : ∀ d : Mma.D, Mma.valueOf L d rB = Mma.vdesc (mmPvBLo L ((d.i - 1) % 3) j) := by
      intro; rfl)
    (hen : ∀ d : Mma.D, Mma.valueOf L d rE = .pred (decide (j ≠ 0 ∨ d.i ≠ 1)) := by
      intro; simp [Mma.valueOf, Mma.values, PTX.Flow.lookupLit]) :
    (Mma.code Loader.asms L g tm0 pro0).ShapeAt (OrUb (MmShape L g)) d := by
  intro t ins e o h hi hc hf
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only at hs
  subst hs
  change At t (⟨.pv j, i, n, tm, pro⟩ : Mma.D).site.pc (Mma.facts L ⟨.pv j, i, n, tm, pro⟩) at h
  subst hpc
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  have hb := hE.sb
  have htm : tm + 512 < 2 ^ 32 := hi.tm
  have r564 := mm_reg (r := 564) h (hl 564 (by simp))
  have r565 := mm_reg (r := 565) h (hl 565 (by simp))
  have rB := mm_reg (r := rB) h (hl rB (by simp))
  have r566 := mm_reg (r := 566) h (hl 566 (by simp))
  have hrE := mm_reg (r := rE) h (hl rE (by simp))
  mm_val r564
  mm_val r565
  mm_val r566
  rw [hB] at rB
  rw [hen] at hrE
  dsimp only at rB hrE
  have hen' : mmaEnable t (.reg rE) = .ok (decide (j ≠ 0 ∨ i ≠ 1)) := by
    unfold mmaEnable
    simp only [readReg, hrE]
    rfl
  have hj := j.isLt
  obtain ⟨db, dsc, h1, h2, he⟩ := fires_pv_event (peer_self hu) hg (c := tm + 256)
    (a := tm + 128 * ((i - 1) % 2)) haoff.1 r564 (by omega) r565 (by omega) rB
    (by unfold mmPvBLo Mma.vLo; omega) r566 hen' hf
  rw [haoff.2] at he
  exact ⟨db, dsc, h1, h2, he⟩

theorem mm_ldNum (hE : MmEnv L) {tm0 : Nat} {pro0 : Nat → Value} (hs : d.site = .ldNum) :
    (Mma.code Loader.asms L g tm0 pro0).ShapeAt (OrUb (MmShape L g)) d := by
  intro t ins e o h hi hc hf
  have hpc : d.site.pc = 2423 := by rw [hs]; rfl
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ : ∃ a : MemAccess,
      kernel.code[2423]? = some ⟨none, .mem a⟩ ∧ a.rule = some .threadAccess ∧
      a.addr.base = .sharedSym 0 ∧ a.addr.off = ((212996 : Nat) : Int) ∧ a.kind = .load ∧
      a.nc = false ∧ a.space = some (.shared .cta) ∧ a.sem = .weak ∧
      (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && a.elem.width == 64)) = false ∧
      a.elem.width = 32 :=
    ⟨_, Flow.code_2423, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u hf => .inl ?_) fun f => .inr ⟨f, rfl⟩
  have hb := hE.sb
  obtain ⟨ac, bs, he, hl, hsz, -⟩ := fires_ldv_sharedSym ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10
    (by omega) hf
  have hsub : t.sub = 0 := h.2.1
  rw [hsub] at hl
  simp only [MmShape, hs]
  refine ⟨ac, bs, he.trans ?_, hl, hsz⟩
  show (⟨d.site.pc, _⟩ : Event) = _
  rw [hs]

/-- The parity a poll reads from a 32-bit register. -/
theorem trunc32_mod2 (x : Nat) : (truncBits 32 (BitVec.ofNat 64 x)).toNat % 2 = x % 2 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- The commits: the one-CTA group without a mask, to the mbarrier at the site's register. -/
theorem mm_commit (hu : UnitCta L g) (hg : g < L.threads) {tm0 : Nat} {pro0 : Nat → Value}
    {pc r a : Nat} {gd : Option (Nat × Bool)}
    (hcode : kernel.code[pc]? = some ⟨gd, .tcCommit .one r 0 none⟩) (hpc : d.site.pc = pc)
    (hl : r ∈ Flow.live pc) (hv : Mma.valueOf L d r = b32 a) (ha : a < 2 ^ 32) (hal : a % 8 = 0)
    (hs : MmShape L g d ⟨pc, .tc (.commit (commitSpec (g / L.block) ⟨.shared, g / L.block, a⟩))⟩) :
    (Mma.code Loader.asms L g tm0 pro0).ShapeAt (OrUb (MmShape L g)) d := by
  intro t ins e o h _ hc hf
  change kernel.code[d.site.pc]? = some ins at hc
  change Fires d.site.pc _ e o at hf
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hr : t.regs r = some (b32 a) := by
    rw [← hv]; exact holds_mem h.2.2.2.2 (Flow.mem_factsFrom (hpc ▸ hl))
  have ht := tc_commit (L := L) (g := g) (t := t) (group := .one) hr ha hal hg (resolve_unit hu _)
  simp only [eventTmpl] at hf
  rw [ht] at hf
  rw [hf.1]
  exact .inl hs

set_option hygiene false in
/-- A commit site by `mm_commit`. -/
macro "mm_commit_at " st:term:max ppSpace c:ident : tactic => `(tactic|
  exact fun {_ _ _ _} => mm_commit (d := ⟨$st, i, n, tm, pro⟩) hu hg $c rfl (by table_decide) rfl
    (by have := hE.sb; omega)
    (by have := hE.sb; have := hE.align; omega)
    (by simp only [MmShape, kvEmpty, sReady, oDone, oFinal, barLoc, kvEmptyOff, sReadyOff,
      oDoneOff, oFinalOff, Nat.add_assoc] <;> rfl))

set_option hygiene false in
/-- The MMA warp's side conditions: the launch, the aligned mbarrier addresses, the warp index. -/
macro "mm_addr" : tactic => `(tactic| first
  | rw [hpre.block]
  | (rw [hw]; rfl)
  | (have := hE.sb; omega)
  | (have := hE.sb; have := hE.align; omega)
  | (apply mbarLoc_b32_ok <;> first
      | (have := hE.sb; omega)
      | (have := hE.sb; have := hE.align; omega)
      | (exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by
          simp only [Mma.valueOf, Mma.values, PTX.Flow.lookupLit, Option.getD_some,
            Option.getD_none]
          try rfl))))

set_option maxHeartbeats 400000 in
/-- **The MMA warp's shape table**, at the states of a thread of a launch that satisfies `Pre`
whose inherited warp-index register holds the warp index. -/
theorem mmShapeAt (hpre : Pre Q L mem0) (hg : g < L.threads) (tm0 : Nat) (pro0 : Nat → Value)
    (d : Mma.D) (hw : d.pro 464 = b32 (Worker.warpOf L g)) :
    (Mma.code Loader.asms L g tm0 pro0).ShapeAt (OrUb (MmShape L g)) d := by
  have hE := mmEnv_of_pre hpre
  have hu := unitCta_of_pre hpre hg
  obtain ⟨s, i, n, tm, pro⟩ := d
  dsimp only at hw
  site_shape s
    except [.ldNum => fun {_ _ _ _} => mm_ldNum hE (d := ⟨_, i, n, tm, pro⟩) rfl,
      .qk 0 => fun {_ _ _ _} => mm_qk Flow.code_mma_0 hE hu hg rfl,
      .qk 1 => fun {_ _ _ _} => mm_qk Flow.code_mma_1 hE hu hg rfl,
      .qk 2 => fun {_ _ _ _} => mm_qk Flow.code_mma_2 hE hu hg rfl,
      .qk 3 => fun {_ _ _ _} => mm_qk Flow.code_mma_3 hE hu hg rfl,
      .qk 4 => fun {_ _ _ _} => mm_qk Flow.code_mma_4 hE hu hg rfl,
      .qk 5 => fun {_ _ _ _} => mm_qk Flow.code_mma_5 hE hu hg rfl,
      .qk 6 => fun {_ _ _ _} => mm_qk Flow.code_mma_6 hE hu hg rfl,
      .qk 7 => fun {_ _ _ _} => mm_qk Flow.code_mma_7 hE hu hg rfl,
      .pv 0 => fun {_ _ _ _} => mm_pv Flow.code_mma_8 hE hu hg rfl,
      .pv 1 => fun {_ _ _ _} => mm_pv Flow.code_mma_9 hE hu hg rfl,
      .pv 2 => fun {_ _ _ _} => mm_pv Flow.code_mma_10 hE hu hg rfl,
      .pv 3 => fun {_ _ _ _} => mm_pv Flow.code_mma_11 hE hu hg rfl,
      .pv 4 => fun {_ _ _ _} => mm_pv Flow.code_mma_12 hE hu hg rfl,
      .pv 5 => fun {_ _ _ _} => mm_pv Flow.code_mma_13 hE hu hg rfl,
      .pv 6 => fun {_ _ _ _} => mm_pv Flow.code_mma_14 hE hu hg rfl,
      .pv 7 => fun {_ _ _ _} => mm_pv Flow.code_mma_15 hE hu hg rfl,
      .qkCommit => by mm_commit_at .qkCommit Flow.code_tcCommit_0,
      .pvCommit1 => by mm_commit_at .pvCommit1 Flow.code_tcCommit_1,
      .pvCommit2 => by mm_commit_at .pvCommit2 Flow.code_tcCommit_2,
      .finCommit => by mm_commit_at .finCommit Flow.code_tcCommit_3]
    unfolding [OrUb, MmShape, kvReady, pReady, sReady, kvEmpty, oDone, oFinal, barLoc, kvReadyOff,
      pReadyOff, sReadyOff, kvEmptyOff, oDoneOff, oFinalOff, Nat.add_assoc, trunc32_mod2, hw,
      Nat.mod_mod]
    reg_vals [Mma.valueOf, Mma.values, lookupLit]
    addr_by (mm_addr)

/-- **The event fired at an MMA state is its shape.** For a thread of a launch that satisfies
`Pre`. -/
theorem mm_shape (hpre : Pre Q L mem0) (hg : g < L.threads) (hi : Mma.Inv d)
    (hw : d.pro 464 = b32 (Worker.warpOf L g)) (h : At t d.site.pc (Mma.facts L d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Loader.asms L g t ins.op) e (some u)) :
    MmShape L g d e :=
  OrUb.of_some (mmShapeAt hpre hg 0 d.pro d hw h hi hc hf) hf

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
