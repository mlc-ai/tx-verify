-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith
public import Kernels.FlashKdaFwd.Proof.Ref.TensorLoad
public import Kernels.FlashKdaFwd.Proof.Ref.ParamBridge
public import Kernels.FlashKdaFwd.Flow.Code
public import Lemmas.Flow.TcTmpl
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # The events of the startup phase, in closed form

`Ev P L g pos e` says which event a thread fires at a position of the startup phase: its kind
and its object, address, size and count as closed forms of the launch and the thread index. No
alternative of `Ev` is an undefined-behaviour event. `ev_at` proves it for every position but
the 21 loads of the offsets array (`Pos.soft`; their address is placed by the scan's invariant,
so `Trace.lean: ev_load` proves them and `ev_full` is the statement for all positions), from the
reference invariant at the position (`RefAt`), the concrete state (`Code.AtD`: the registers
hold the values of the file) and the firing fact of the site's instruction.

How each class is obtained (one library inversion lemma per class of instruction, with the
operand registers read from the state's facts by `reg_w` and rewritten with the invariant's
closed forms):

| position | instruction | lemma | what the invariant gives |
|---|---|---|---|
| `elect j` | `elect.sync` | `electTmpl` with `Sched.full_member` | the mask register holds `-1` |
| `shfl j` | `shfl.sync.idx` | `fires_shflTmpl` | the operand register holds the warp index |
| `init j` | `mbarrier.init` | `shape_mbInitR` | address `S + off`, count |
| `fence j` | `fence.mbarrier_init` | unfolding the template | nothing |
| `bar j` | `bar.sync 0` | `shape_barSync` | nothing |
| `load j` | `ld.global.b64` | (`Trace.lean`: `offsets_rd`) | the pointer and its range |
| `arrive` | `mbarrier.arrive.expect_tx` | `shape_arrive` | address, byte count 65536 |
| `copy j` | `cp.async.bulk.tensor` | `Ref/TensorLoad.lean: tensorLoad_event` | all operands |
| `wait` | `mbarrier.try_wait.parity` | `shape_wait` | address, parity 0 |

The 16 tensor loads of the initial state: the tensor map is register `%rd45` (2291), whose
static kind is the generic address of parameter object 8 (`RegKind.gparamPtr 8`; `Ref.reg_g`
reads it, and `Ref/ParamBridge.lean: paramName_8` says that this object is the specification's
`param "8"`); the coordinate and destination registers are in the invariant (`AtPos` at `copy j`:
`8 j`, `0`, `H * seq + head`, `shared_mem + 32768 + 4096 j`). The event is exactly the issue of
`stateSpec P L g j`: a load through the map of the initial state (`Pre.map8`) of 8 columns of
the 128 rows of plane `H * seq + head`, 4096 bytes, to the `j`-th 4096-byte block of the state
buffer, completing on the state barrier. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The offset in the block's shared memory of the mbarrier initialized at `init j`: the load
pipeline's full and empty barriers of the stages 0, 1, 2 (`98304 + 8 s`, `98328 + 8 s`), the
store pipeline's full barriers (`98352`, `98360`) and empty barriers (`98368`, `98376`), the
state barrier (`98384`). -/
def initOff (j : Nat) : Nat :=
  [98304, 98328, 98312, 98336, 98320, 98344, 98352, 98368, 98360, 98376, 98384].getD j 0

/-- The arrival count of the mbarrier initialized at `init j`. -/
def initCnt (j : Nat) : Nat := [1, 128, 1, 128, 1, 128, 128, 1, 128, 1, 1].getD j 0

/-- **The copy of the `j`-th load of the initial state** by a thread `g`: through the map of
parameter object 8 at the coordinates `(8 j, 0, H * seq + head)` (column, row, plane), to byte
`32768 + 4096 j` of the shared window of the thread's block, completing on the state barrier
(byte 98384 of the window). -/
def stateSpec (P : Params) (L : Launch) (g j : Nat) : TensorCopy.Spec :=
  loadSpec P (g / L.block) 8 [8 * j, 0, P.heads * seqOf P g + headOf P g]
    (P.sharedBase + (32768 + 4096 * j)) (P.sharedBase + 98384)

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (L : Launch) (g : Nat) : Pos → Event → Prop
  | .elect j, e => ∃ inst ld, e = ⟨(Site.elect j).pc, .elect 4294967295 inst ld⟩
  | .shfl j, e => ∃ v ok, e = ⟨(Site.shfl j).pc, .shfl .idx (.bits 32 (W (warp g))) 0 31 v ok⟩
  | .init j, e => e = ⟨(Site.mbarInit j).pc,
      .mbInit ⟨.shared, g / L.block, P.sharedBase + initOff j.val⟩ (initCnt j.val)⟩
  | .fence j, e => e = ⟨(Site.fenceMbarInit j).pc, .fenceMbarInit⟩
  | .bar j, e => e = ⟨(Pos.bar j).site.pc, .bar 0 none .sync⟩
  | .load j, e => ∃ i ≤ P.sequences, ∃ bs, bs.length = 8 ∧
      e = ⟨(Pos.load j).site.pc, .rd { loc := P.offsetLoc i, size := 8 } bs⟩
  | .arrive, e =>
    e = ⟨327, .arrive ⟨.shared, g / L.block, P.sharedBase + 98384⟩ 65536 1 true .cta⟩
  | .copy j, e =>
    e = ⟨(Pos.copy j).site.pc, .tensorIssue (P.objectBase 8) (stateSpec P L g j.val)⟩
  | .wait, e =>
    ∃ ok, e = ⟨384, .wait ⟨.shared, g / L.block, P.sharedBase + 98384⟩ 0 ok true .cta⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {site : Site}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- No assumption of the kernel widens the scope of an mbarrier instruction. -/
theorem noWiden (pc : Nat) : Assumptions.all.any (·.clusterScopeMbar pc) = false := rfl

theorem full_mask : i32 (-1) = W 4294967295 := by decide

/-- **Positions whose event `ev_at` does not derive**: the loads of the offsets array (their
address is placed by the invariant of the scan; `Trace.lean: ev_load`). -/
def Pos.soft : Pos → Prop
  | .load _ => True
  | _ => False

/-- An election whose mask register holds `-1`: the full mask has every lane as a member, so
the election is not undefined behaviour. -/
theorem ev_elect {pc r : Nat} {dst : Option Nat} {pr : Nat} {ty : Option DType}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.reg r)⟩)) e o)
    (hr : t.regs r = some (.bits 32 (i32 (-1)))) :
    ∃ inst ld, e = ⟨pc, .elect 4294967295 inst ld⟩ := by
  rw [full_mask] at hr
  have hm := readBits_b32 (L := L) (g := g) hr (by decide)
  have hmem : electMember (BitVec.ofNat 64 4294967295).toNat (laneOf L g) :=
    Sched.full_member (Nat.mod_lt _ (by decide))
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm, hmem, ↓reduceIte, Fires] at hf
  obtain ⟨inst, ld, rfl, -⟩ := hf
  exact ⟨inst, ld, rfl⟩

/-- A full-mask shuffle, from lane 0, of a 32-bit word register: never undefined behaviour in
a block of whole warps. -/
theorem ev_shfl {pc d pr ar : Nat} {y : BitVec 64} (hblk : L.block % 32 = 0)
    (hr : t.regs ar = some (.bits 32 y))
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.shfl .idx, some (.int .b 32), [some d, some pr], [.reg ar, .imm 0, .imm 31],
        some (.imm (-1))⟩)) e o) :
    ∃ v ok, e = ⟨pc, .shfl .idx (.bits 32 y) 0 31 v ok⟩ := by
  change Fires _ (shflTmpl L g t .idx d (some pr) (.reg ar) (.imm 0) (.imm 31) (.imm (-1))) e o
    at hf
  obtain ⟨recv, ok, he⟩ := fires_shflTmpl (m := truncBits 32 (BitVec.ofInt 64 (-1)))
    (av := .bits 32 y) (bv := truncBits 32 (BitVec.ofInt 64 0))
    (cv := truncBits 32 (BitVec.ofInt 64 31)) rfl
    (by simp [readValue, readReg, hr, pure, Except.pure]) rfl rfl (by decide) hblk rfl hf
  exact ⟨recv, ok, he⟩

/-- An `mbarrier.init` whose address register holds `S + off` and whose count register holds
`n`. -/
theorem ev_init (hpre : Pre P L mem0) {pc r c off n : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mbarInit r 0 (.reg c))) e o)
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + off))))
    (hc : t.regs c = some (.bits 32 (W n))) (ho : off ≤ 98384) (h8 : off % 8 = 0)
    (hn : 0 < n) (hn' : n < 2 ^ 20) :
    e = ⟨pc, .mbInit ⟨.shared, g / L.block, P.sharedBase + off⟩ n⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  exact shape_mbInitR (P := fun e => e = _) hf hr (by omega) hc hn hn' (by omega) rfl

/-- The address register of the state barrier names the barrier. -/
theorem stateLoc (hpre : Pre P L mem0) {r : Nat}
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 98384)))) :
    mbarLoc L g t r 0 = .ok ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  exact mbarLoc_b32 hr (by omega) (by omega)

/-- **A load of the initial state**: with the operand registers of the invariant, the event
is the issue of `stateSpec`. It is not undefined behaviour: the map is the launch's map of the
initial state, the destination is a multiple of 128, the first coordinate a multiple of 4
elements, and the copy and its mbarrier are in the issuer's own block. -/
theorem ev_copy (hpre : Pre P L mem0) (hg : g < L.threads) {pc dst rc j : Nat} (hj : j < 16)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg 2291) [.reg rc, .reg 499, .reg 500] 496 0 none .tile
        (some (.reg 2290)))) e o)
    (hat : (code L g).AtD ⟨site, w, p, x⟩ t) (h2291 : 2291 ∈ Flow.live site.pc)
    (h2290 : 2290 ∈ Flow.live site.pc)
    (hdst : t.regs dst = some (.bits 32 (W (P.sharedBase + (32768 + 4096 * j)))))
    (hmb : t.regs 496 = some (.bits 32 (W (P.sharedBase + 98384))))
    (hc0 : t.regs rc = some (.bits 32 (W (8 * j))))
    (hc1 : t.regs 499 = some (.bits 32 (W 0)))
    (hc2 : t.regs 500 = some (.bits 32 (W (P.heads * seqOf P g + headOf P g)))) :
    e = ⟨pc, .tensorIssue (P.objectBase 8) (stateSpec P L g j)⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have hp := plane_lt hpre hg
  have hr := hpre.planesRange
  have hrm := reg_g hat (r := 2291) h2291 (i := 8) rfl
  have hpol := reg_w hat (r := 2290) h2290 (n := 64) rfl
  exact (tensorLoad_event hpre hg (i := 8) paramName_8 (rs := [rc, 499, 500])
    (vs := [8 * j, 0, P.heads * seqOf P g + headOf P g]) hf hrm hdst (by omega) (by omega)
    hmb (by omega) (by omega) hpol
    (.cons ⟨hc0, by omega⟩ (.cons ⟨hc1, by omega⟩ (.cons ⟨hc2, by omega⟩ .nil))) rfl
    (show 8 * j * 4 % 16 = 0 by omega)).1

/-- `copy_ev dst rc`: the event of the tensor load of the current case, whose destination
register is `dst` and whose first coordinate register is `rc`. -/
syntax "copy_ev " num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| copy_ev $dst $rc) => `(tactic| (
      have r1 := reg_w hat (r := $dst) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 496) (by lit_mem) (n := 32) rfl
      have r3 := reg_w hat (r := $rc) (by lit_mem) (n := 32) rfl
      have r4 := reg_w hat (r := 499) (by lit_mem) (n := 32) rfl
      have r5 := reg_w hat (r := 500) (by lit_mem) (n := 32) rfl
      dsimp only at r1 r2 r3 r4 r5 hdst hco h496 h499 h500
      rw [hdst] at r1
      rw [h496] at r2
      rw [hco] at r3
      rw [h499] at r4
      rw [h500] at r5
      exact ev_copy hpre hg (by decide) hf hat (by lit_mem) (by lit_mem) r1 r2 r3 r4 r5))

/-- **The event at a position** other than a load of the offsets array. -/
theorem ev_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩)
    (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t) (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hns : ¬ pos.soft) : Ev P L g pos e := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain ⟨-, hbase, h⟩ := h
  cases pos with
  | elect j =>
    fin_cases j <;> simp only [AtPos, Fin.isValue] at h <;>
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    · have r1 := reg_w hat (r := 331) (by lit_mem) (n := 32) rfl
      simp only [h] at r1
      exact ev_elect hf r1
    · have r1 := reg_w hat (r := 334) (by lit_mem) (n := 32) rfl
      simp only [h] at r1
      exact ev_elect hf r1
    · have r1 := reg_w hat (r := 339) (by lit_mem) (n := 32) rfl
      simp only [h] at r1
      exact ev_elect hf r1
    · have r1 := reg_w hat (r := 356) (by lit_mem) (n := 32) rfl
      simp only [h] at r1
      exact ev_elect hf r1
    · have r1 := reg_w hat (r := 487) (by lit_mem) (n := 32) rfl
      simp only [h] at r1
      exact ev_elect hf r1
  | shfl j =>
    have hw := hbase.warp
    dsimp only at hw
    have hblk : L.block % 32 = 0 := by rw [hpre.block]
    fin_cases j <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      (have r1 := reg_w hat (r := 308) (by lit_mem) (n := 32) rfl
       dsimp only at r1
       rw [hw] at r1
       exact ev_shfl hblk r1 hf)
  | init j =>
    fin_cases j <;> simp only [AtPos, Fin.isValue] at h <;>
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    · have r1 := reg_w hat (r := 341) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 340) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 343) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 342) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 344) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 340) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 345) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 342) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 346) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 340) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 347) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 342) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 358) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 357) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 360) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 359) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 361) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 357) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 362) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 359) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
    · have r1 := reg_w hat (r := 496) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := 495) (by lit_mem) (n := 32) rfl
      simp only [h] at r1 r2
      exact ev_init hpre hf r1 r2 (by decide) (by decide) (by decide) (by decide)
  | fence j =>
    fin_cases j <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      (simp only [eventTmpl, tmaTmpl, widenMbarScope, noWiden, Bool.false_eq_true, ↓reduceIte,
         Fires] at hf
       exact hf.1)
  | bar j =>
    fin_cases j <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      exact shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  | load j => exact (hns trivial).elim
  | arrive =>
    simp only [AtPos] at h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 496) (by lit_mem) (n := 32) rfl
    have r2 := reg_w hat (r := 497) (by lit_mem) (n := 32) rfl
    simp only [h] at r1 r2
    exact shape_arrive (P := fun e => e = _) hf (noWiden _)
      (readBits_b32 r2 (by decide)) rfl (stateLoc hpre r1) rfl
  | copy j =>
    simp only [AtPos] at h
    obtain ⟨-, -, -, -, -, -, h496, h499, h500, hdst, hco⟩ := h
    fin_cases j <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      simp only [finVal, copyDst, copyCoord, getLit] at hdst hco
    · copy_ev 498 499
    · copy_ev 501 502
    · copy_ev 503 504
    · copy_ev 505 506
    · copy_ev 507 508
    · copy_ev 509 510
    · copy_ev 511 512
    · copy_ev 513 514
    · copy_ev 515 516
    · copy_ev 517 518
    · copy_ev 519 520
    · copy_ev 521 522
    · copy_ev 523 524
    · copy_ev 525 526
    · copy_ev 527 528
    · copy_ev 529 530
  | wait =>
    simp only [AtPos] at h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 532) (by lit_mem) (n := 32) rfl
    have r2 := reg_w hat (r := 533) (by lit_mem) (n := 32) rfl
    simp only [h] at r1 r2
    exact shape_wait (P := fun e' => ∃ ok, e' =
        ⟨384, .wait ⟨.shared, g / L.block, P.sharedBase + 98384⟩ 0 ok true .cta⟩) hf (noWiden _)
      (readBits_b32 r2 (by decide)) (stateLoc hpre r1) (fun ok => ⟨ok, rfl⟩)

/-- **No closed-form event of the phase is undefined behaviour.** -/
theorem Ev.noUb {pos : Pos} (h : Ev P L g pos e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  cases pos <;>
    simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
      false_and] at h

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
