-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartSound

@[expose] public section

/-! # The common start from the launch state

From the launch state a thread of warps 0 to 3 runs the loads of the parameter words (pc 0 to 7:
`strideBt`, `pageRows`, `headRows`, `headCols`, `splits`, the block-table base and the address of
the tensor map `param_1`), `%tid.x`, the test `%p3 = (tid < 32)` and the shared base (pc 8 to
10), and reaches the `tcgen05.alloc` (pc 11). A thread of warp 0 is then at the machine's first
site `alloc`. The other threads skip the allocation (`%p3` is false) and are at the first barrier
(`bar0`, pc 12).

`start` states the machine's `Code.Sound.start`, from `Pre` and the thread's being in the default
partition (`tid < 128`), and `inv_start` shows that the first state's invariant holds: `Pre`
gives `ProA.ArgsOk` for the inherited registers `inh L g Q 0` (`ProA.argsOk_of_pre`) with the
parameter words the launch gives. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The code from the start to the `tcgen05.alloc` (pc 0 to 10): the parameter words, `%tid.x`,
`%p3` and the shared base. The launch is `explicitParams L (Worker.startParams Q)`, which
`start` identifies with `L`. -/
theorem start0 (Q : Params) (L : Launch) (g : Nat) (hn : L.ntid = ⟨L.block, 1, 1⟩)
    (hb : L.block < 2 ^ 32) (hpos : 0 < L.block) :
    ∃ t, run kernel asms (explicitParams L (Worker.startParams Q)) g 11 {} = some t ∧
      At t 11 (factsAt L g Q (b32 0) 11) := by
  have htid : ∀ ps, ((explicitParams L ps).tidOf g).get .x = g % L.block :=
    fun _ => Worker.tidOf_x hn g
  have hlt : g % L.block < 2 ^ 32 := lt_trans (Nat.mod_lt g hpos) hb
  seg_fp at_init using
    try simp only [valueOf, table, Worker.startParams, PTX.Flow.lookupLit, Option.getD_some]
    all_goals first
      | (simp only [MemExt.extendBits_same, b32, b64, Worker.trunc32, Worker.trunc64]; done)
      | (simp only [b32, Worker.trunc32]; done)
      | rfl
      | (rw [htid, Worker.trunc32, Nat.mod_eq_of_lt hlt]; rfl)
      | (rw [htid, Worker.trunc32, Nat.mod_eq_of_lt hlt]
         simp only [Value.pred.injEq]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq]
         omega)

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0}

/-- **`Pre` gives `ProA.ArgsOk`** for the inherited registers of a thread of the default
partition: every field (the thread index below 128, the `num_splits` word positive and below
`2 ^ 31`, `ctaid.x` below it, the parameter words) is discharged. -/
theorem argsOk_inh (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128)
    (tm : Nat) : ProA.ArgsOk L g (inh L g Q tm) :=
  ProA.argsOk_of_pre hpre hg (inh := inh L g Q tm) hw
    (Nat.mod_eq_of_lt (by have := hpre.splitsRange; omega)) rfl rfl rfl rfl rfl rfl
    (fun w hw => by simp [inh, hw]) rfl rfl rfl

/-- The first state satisfies the invariant. -/
theorem inv_start (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128) :
    Inv L g Q (D.start L g) := by
  refine ⟨argsOk_inh hpre hg hw _, ?_⟩
  · unfold D.start
    split_ifs with hl
    · exact fun _ => hl
    · intro hh
      simp at hh

/-- **The common start from the launch state**: a thread of warps 0 to 3 of a launch that
satisfies `Pre` reaches its first event, in the machine's first state, which satisfies the
invariant. -/
theorem start (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128) :
    ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧ AtS L g Q (D.start L g) t ∧
      Inv L g Q (D.start L g) := by
  have hblk := hpre.block
  have hn : L.ntid = ⟨L.block, 1, 1⟩ := by rw [hpre.ntid, hblk]
  obtain ⟨t, hr, ht⟩ := start0 Q L g hn (by rw [hblk]; decide) (by rw [hblk]; decide)
  have hps : explicitParams L (Worker.startParams Q) = L := by
    apply explicitParams_eq
    intro p v hm
    simp only [Worker.startParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpre.paramStrideBt
    · exact hpre.paramPageRows
    · exact hpre.paramHeadRows
    · exact hpre.paramHeadCols
    · exact hpre.paramSplits
    · exact hpre.paramBt
  rw [hps] at hr
  have hinv := inv_start hpre hg hw
  by_cases hl : g % L.block < 32
  · refine ⟨t, run_rtg hr, ?_, hinv⟩
    simp only [D.start, hl, ↓reduceIte]
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  · have hp3 : (3, Value.pred false) ∈ factsAt L g Q (b32 0) 11 :=
      tbl_mem (by live_dec) (by simp [valueOf, table, hl])
    obtain ⟨t', hr', ht'⟩ := Seg.skip (K := kernel) (A := asms) (L := L) (g := g) Flow.code_11
      hp3 (by simp) t ht
    refine ⟨t', (run_rtg hr).trans (run_rtg hr'), ?_, hinv⟩
    simp only [D.start, hl, ↓reduceIte]
    exact ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1,
      holds_factsFrom_mono ht'.2.2.2.2 (by live_dec)⟩

/-- **The code machine is sound** from the launch state: `Code.Sound`, and so the machine's
`Machine.Sound`. -/
theorem sound (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128) :
    (code L g Q).Sound where
  start := by
    obtain ⟨t, hr, ht, hi⟩ := start hpre hg hw
    exact ⟨t, hr, ht, hi⟩
  steps := stepAt Q

theorem machine_sound (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128) :
    (code L g Q).toMachine.Sound :=
  (sound hpre hg hw).machine

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
