-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerHandoff

@[expose] public section

/-! # The worker's start

From the launch state, a thread of warp 4 or above runs the code every thread runs: the loads of
the parameter words the roles use (pc 0 to 7: `strideBt`, `pageRows`, `headRows`, `headCols`,
`splits` and the block-table base, and the address of the tensor map `param_1`), `%tid.x`, the
test `%p3 = (tid < 32)` and the shared base (pc 8 to 10). The `tcgen05.alloc` at pc 11 is guarded
by `%p3`, false for these threads, so it is skipped, and the thread reaches the first barrier
(pc 12), the worker machine's first site, with the registers `startPro Q`.

`startPro Q` is the inherited-register record at that point: the parameter words (mod `2 ^ 32`),
the block-table base and the pointer `%rd1 = cvta.param(param_1)` (the other registers of `rest`
are dead there). The facts used are the launch's (`Pre`): the CTA has 256 threads in `x`, and
the six parameters hold the values `Spec.Params` gives. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)

noncomputable section
set_option maxRecDepth 100000

/-- The inherited registers of a worker at its first barrier. -/
def startPro (Q : Params) : Pro :=
  { rest := fun r => if r = 1949 then .ptr 64 true (.param (param "1")) 0 else b32 0,
    w67 := Q.strideBt % 2 ^ 32, w68 := Q.pageRows % 2 ^ 32, w69 := Q.headRows % 2 ^ 32,
    w70 := Q.headCols % 2 ^ 32, w71 := Q.splits % 2 ^ 32, bt := Q.btBase }

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

/-- The code from the start to the `tcgen05.alloc` (pc 0 to 10): the parameter words, `%tid.x`,
`%p3` and the shared base. The launch is `explicitParams L (startParams Q)`, which `start`
identifies with `L`. -/
theorem start0 (Q : Params) (L : Launch) (g : Nat) (hn : L.ntid = ⟨L.block, 1, 1⟩)
    (hb : L.block < 2 ^ 32) (hpos : 0 < L.block) :
    ∃ t, run kernel asms (explicitParams L (startParams Q)) g 11 {} = some t ∧
      At t 11 (factsAt L g 11 ⟨.bar0, startPro Q⟩) := by
  have htid : ∀ ps, ((explicitParams L ps).tidOf g).get .x = g % L.block :=
    fun _ => tidOf_x hn g
  have hlt : g % L.block < 2 ^ 32 := lt_trans (Nat.mod_lt g hpos) hb
  seg_fp at_init using
    try simp only [valueOf, own, Pro.val, Pro.table, startPro, startParams, PTX.Flow.lookupLit,
      Option.getD_some, Option.getD_none, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first
      | (simp only [MemExt.extendBits_same, b32, b64, trunc32, trunc64]; done)
      | (simp only [b32, trunc32]; done)
      | rfl
      | (rw [htid, trunc32, Nat.mod_eq_of_lt hlt]; rfl)
      | (rw [htid, trunc32, Nat.mod_eq_of_lt hlt]
         simp only [Value.pred.injEq]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq]
         omega)

variable {L : Launch} {g : Nat}

/-- **The worker's start**: a thread of warp 4 or above, in a launch that satisfies `Pre`, reaches
its first barrier with the worker machine's first state for `startPro Q`, which satisfies the
machine's invariant. -/
theorem start {Q : Params} {mem0 : Mem0} (hpre : Pre Q L mem0) (hw : 4 ≤ warpOf L g) :
    ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      At t Site.bar0.pc (facts L g (D.start (startPro Q))) ∧ Inv L g (D.start (startPro Q)) := by
  have hblk := hpre.block
  have hn : L.ntid = ⟨L.block, 1, 1⟩ := by rw [hpre.ntid, hblk]
  obtain ⟨t, hr, ht⟩ := start0 Q L g hn (by rw [hblk]; decide) (by rw [hblk]; decide)
  have hps : explicitParams L (startParams Q) = L := by
    apply explicitParams_eq
    intro p v hm
    simp only [startParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpre.paramStrideBt
    · exact hpre.paramPageRows
    · exact hpre.paramHeadRows
    · exact hpre.paramHeadCols
    · exact hpre.paramSplits
    · exact hpre.paramBt
  rw [hps] at hr
  have hp3 : (3, Value.pred false) ∈ factsAt L g 11 ⟨.bar0, startPro Q⟩ :=
    tbl_mem (by live_dec) (by wk_values; rw [p3_false hw])
  obtain ⟨t', hr', ht'⟩ := Seg.skip (K := kernel) (A := asms) (L := L) (g := g) Flow.code_11 hp3
    rfl t ht
  refine ⟨t', (run_rtg hr).trans (run_rtg hr'), ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1,
    holds_relive ht'.2.2.2.2 rfl (by live_dec)⟩,
    ⟨hw, ?_, ⟨hpre.btAlign, by simp [D.start, startPro], by
      have := hpre.headColsAlign
      show Q.headCols % 2 ^ 32 % 8 = 0
      omega⟩⟩⟩
  have := Nat.mod_lt g (show 0 < L.block by rw [hblk]; decide)
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
