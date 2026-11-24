-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProASiteTac
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec
public import Kernels.InklingRelDecode.Proof.Thread.EvDProBase
public import Lemmas.Flow.SharedSym

@[expose] public section

/-! # The startup's register table and the ABI prefix

Every thread runs the same code from its first instruction: the loads of the parameter words the
roles use (pc 0 to 7), `%tid.x` and `%p3 = tid < 32`, the shared base (pc 8 to 10). Here are the
values of the registers the startup and the prologue inherit (`table`, `preValueOf`,
`preFactsAt`), the inherited registers of the prologue (`inh`, `argsOk_inh`), and the run of
the ABI prefix to the first event (`start0`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

/-- The warp index of a thread of the CTA. -/
abbrev warpOf (L : Launch) (g : Nat) : Nat := g % L.block / 32

/-- The shared base as `mov.b32` gives it. -/
def baseW (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))

/-- The inherited registers the prologue reads, as the launch gives them: the parameter words
(`Pre.param*`), `%p3` and `%rd1` (the registers the common code carries), the Tensor Memory base
word `tm`. -/
def inh (L : Launch) (g : Nat) (Q : Params) (tm : Nat) : Proof.ProA.Inh where
  rest := fun r =>
    if r = 3 then .pred (decide (g % L.block < 32))
    else if r = 1949 then .ptr 64 true (.param (param "1")) 0 else b32 0
  tm := tm
  w67 := Q.strideBt % 2 ^ 32
  w68 := Q.pageRows % 2 ^ 32
  w69 := Q.headRows % 2 ^ 32
  w70 := Q.headCols % 2 ^ 32
  w71 := Q.splits % 2 ^ 32
  btB := Q.btBase
  x15 := (L.params (param "15")).getD 0
  x16 := BitVec.ofNat 64 Q.strideQ
  x17 := BitVec.ofNat 64 Q.strideRel
  x0 := BitVec.ofNat 64 Q.qBase
  x6 := BitVec.ofNat 64 Q.relBase
  x8 := BitVec.ofNat 64 Q.seqBase
  x9 := BitVec.ofNat 64 Q.cuBase
  x25 := BitVec.ofNat 64 Q.nTok
  x10 := BitVec.ofNat 64 Q.oBase
  x11 := BitVec.ofNat 64 Q.lseBase

/-- The registers the common code defines or inherits at pc 11 to 17 and their values: `%p3`
(`tid < 32`), `%r1` (`%tid.x`), `%r2` (the Tensor Memory base word), `%r3` and `%r4` (the warp
index), `%r67 … %r71` (the parameter words), `%r73` (the shared base) and `%rd1`, `%rd72`. -/
def table (L : Launch) (g : Nat) (Q : Params) (w : Value) : List (Nat × Value) :=
  [(3, .pred (decide (g % L.block < 32))), (462, b32 (g % L.block)), (463, w),
   (464, b32 (warpOf L g)), (465, b32 (warpOf L g)), (528, b32 (Q.strideBt % 2 ^ 32)),
   (529, b32 (Q.pageRows % 2 ^ 32)), (530, b32 (Q.headRows % 2 ^ 32)),
   (531, b32 (Q.headCols % 2 ^ 32)), (532, b32 (Q.splits % 2 ^ 32)),
   (534, .bits 32 (baseW L)), (1949, .ptr 64 true (.param (param "1")) 0),
   (2020, b64 Q.btBase)]

/-- The value of register `r`: the table's, else the prologue's (`ProA.valueOf` of its first
state), which values the registers the seven `ld.param` of pc 20 to 26 write. -/
def preValueOf (L : Launch) (g : Nat) (Q : Params) (w : Value) (r : Nat) : Value :=
  ((table L g Q w).lookup r).getD
    (Proof.ProA.valueOf L g (Proof.ProA.Dat.start (inh L g Q (Proof.ProA.shW w)) w) r)

/-- The registers live at `pc` with their values. -/
def preFactsAt (L : Launch) (g : Nat) (Q : Params) (w : Value) (pc : Nat) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (preValueOf L g Q w)

/-- A table fact at a checkpoint where the register is live. -/
theorem tbl_mem {L : Launch} {g : Nat} {Q : Params} {pc : Nat} {tm : Value} {r : Nat}
    {v : Value} (hl : r ∈ Flow.live pc) (hv : preValueOf L g Q tm r = v) :
    (r, v) ∈ preFactsAt L g Q tm pc :=
  hv ▸ Flow.mem_factsFrom hl

theorem live27 : Flow.live 27 = [3, 462, 463, 464, 525, 526, 527, 528, 529, 530, 531, 532, 1949,
    2018, 2019, 2020, 2021, 2022] := by
  decide +kernel

/-- The shared base as the register `%r73` (`mov.b32 %r73, global_smem`) holds it. -/
theorem sb_toNat {L : Launch} (hS : Proof.ProA.SharedOk L) :
    (BitVec.ofNat 64 (L.sharedBase + 0)).toNat % 2 ^ 32 = L.sharedBase := by
  have := hS.2
  simp only [BitVec.toNat_ofNat]
  omega

/-- The kernel parameters the code up to pc 12 reads, with their values. -/
def startParams (Q : Params) : List (String × Nat) :=
  [(param "18", Q.strideBt), (param "21", Q.pageRows), (param "22", Q.headRows),
   (param "23", Q.headCols), (param "24", Q.splits), (param "7", Q.btBase)]

theorem trunc32 (x : Nat) : truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  have h : (2 : Nat) ^ 32 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  rw [Nat.mod_mod_of_dvd _ h]

theorem trunc64 (x : Nat) : truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, BitVec.toNat_ofNat]

/-- In a launch whose CTA is `(block, 1, 1)`, `%tid.x` is the thread's index in the CTA. -/
theorem tidOf_x {L : Launch} (hn : L.ntid = ⟨L.block, 1, 1⟩) (g : Nat) :
    ((L.tidOf g).get .x) = g % L.block := by
  simp only [Launch.tidOf, Dim3.coord, hn, Nat.mod_mod, Nat.mod_one, Nat.mul_one]
  rcases Nat.eq_zero_or_pos L.block with h0 | hpos
  · simp [h0, Dim3.get]
  · simp [Dim3.get]

/-- **The ABI prefix** (pc 0 to 10): the parameter words, `%tid.x`, `%p3` and the shared base.
The launch is `explicitParams L (startParams Q)`, which `Common/Sound.lean` identifies with
`L`. -/
theorem start0 (Q : Params) (L : Launch) (g : Nat) (hn : L.ntid = ⟨L.block, 1, 1⟩)
    (hb : L.block < 2 ^ 32) (hpos : 0 < L.block) :
    ∃ t, run kernel Assumptions.all (explicitParams L (startParams Q)) g 11 {} = some t ∧
      At t 11 (preFactsAt L g Q (b32 0) 11) := by
  have htid : ∀ ps, ((explicitParams L ps).tidOf g).get .x = g % L.block :=
    fun _ => tidOf_x hn g
  have hlt : g % L.block < 2 ^ 32 := lt_trans (Nat.mod_lt g hpos) hb
  seg_fp at_init using
    try simp only [preValueOf, table, startParams, PTX.Flow.lookupLit, Option.getD_some]
    all_goals first
      | (simp only [MemExt.extendBits_same, b32, b64, trunc32, trunc64]; done)
      | (simp only [b32, trunc32]; done)
      | rfl
      | (rw [htid, trunc32, Nat.mod_eq_of_lt hlt]; rfl)
      | (rw [htid, trunc32, Nat.mod_eq_of_lt hlt]
         simp only [Value.pred.injEq]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq]
         omega)

/-- **`Pre` gives `ProA.ArgsOk`** for the inherited registers of a thread of warps 0 to 3. -/
theorem argsOk_inh {Q : Params} {L : Launch} {m : Mem0} {g : Nat} (hpre : Pre Q L m)
    (hg : g < L.threads) (hw : g % L.block < 128) (tm : Nat) :
    Proof.ProA.ArgsOk L g (inh L g Q tm) :=
  Proof.ProA.argsOk_of_pre hpre hg (inh := inh L g Q tm) hw
    (Nat.mod_eq_of_lt (by have := hpre.splitsRange; omega)) rfl rfl rfl rfl rfl rfl
    (fun w hw => by simp [inh, hw]) rfl rfl rfl

/-- No assumption of the kernel selects a segment at a program counter outside the software
`exp2` instances. -/
theorem asms_segFreePc {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc Assumptions.all pc := by
  intro a ha L g t htpc
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then _ else none) = none
    rw [htpc, h]
    simp
  all_goals rfl

end
end PTX.Kernels.InklingRelDecode.Proof2.Startup
