-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEndsAcc
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEndsCompute
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectData
public import Kernels.FlashKdaFwd.Proof.Ref.Store.ValuesOwes
public import Kernels.FlashKdaFwd.Proof.Values.Ends.NoUb

@[expose] public section

/-!
# The values at the ends of the tile loop, wired to the reference and protocol layers

`Proof/Values/Ends/` proves what the data are in the four stretches of the kernel around the
tile loop (the conversion loop, the carry loads, the final stores, the store path of a partial
last tile), from contracts of the reference layer and of the protocol layer.
`ValuesEndsRef.lean` proves the reference-layer contracts for a whole execution, and
`ValuesEndsAcc.lean` the read-back of the bfloat16 state copy (the field `acc` of
`Values.ReadBack`), both from two structures of facts that the Store and the Compute phase
owed (`StoreOwes`, `ComputeOwes`). `Ref/Store/ValuesOwes.lean` and `ValuesEndsCompute.lean`
prove the two structures. This file discharges them, instantiates the value layer's theorems
with the contracts and states the results in the shapes their consumers ask for. Importing it
gives all of these files.

**Words.** A *followed state* of thread `g` at position `k` is the state `s` of the thread's
machine before the thread's `k`-th event (`Frame.stateAt (code L) X g k = some (some s)`);
"the successor is followed" means that the machine has a state at position `k + 1`. A
*compute thread* has index `g % L.block` below 128 in its thread block; the *store leader* of
a block is its thread 160. *Undefined behaviour* is an event `⟨pc, .ub f⟩`. `O : Owners` are
the four functions of the protocol layer that name the writer of a byte of the buffer region.

## What is here

Helpers are in the namespace `Assembly.ValuesEnds`; the final theorems are in `Assembly`.

* `storeRef`, `storeCtl`: the last two of the five reference-layer contracts (`convRef`,
  `carryRef`, `finalRef` are in `ValuesEndsRef.lean`), with what the two phases owed
  discharged by `Store.storeOwes` (`Ref/Store/ValuesOwes.lean`) and `ValuesEnds.computeOwes`
  (`ValuesEndsCompute.lean`).
* `readBack_acc`: the field `acc` of `Values.ReadBack` (`ValuesEndsAcc.lean`).
* `ValuesEnds.finalSlots`: the value layer's hypothesis `FinalSlots` (which shared byte a slot
  of a final-state tensor store reads), from the epilogue's `final_slots`.
* `ValuesEnds.OutStage`, `ValuesEnds.leaderReads`: the value layer's hypothesis `LeaderReads`
  (what the store leader reads from the output buffers) from the protocol layer's read-back
  `UnionFacts.leader_read` and the field `stage` of `Protocol.OutContent`, which the value
  induction of the tile loop proves.
* `out_final'`, `out_elem'`: the fields `final` and `elem` of `Protocol.OutContent P L X O`,
  in the fields' own shapes.
* The data half of "no undefined-behaviour event", one theorem per field of
  `DataHalf` (`DirectData.lean`) that is about the ends of the tile loop, in the field's exact
  shape: `dataHalf_convLoad`, `dataHalf_convStore`, `dataHalf_carryLoad`,
  `dataHalf_elemRead`, `dataHalf_elemStore`, `dataHalf_finalStore`.

## Hypotheses that remain, and who owes them

Every theorem takes the precondition `hpre : Pre P L mem0` and consistency
`hX : Consistent L kernel Assumptions.all mem0 X`. Besides them:

* `F : Protocol.Facts P L X`, `U : UnionFacts L X (ctaTiles P) O`, `C : StoreCover L X O` (for
  any owner functions `O`): the assembly groups A, B and C1. Used by `readBack_acc`,
  `dataHalf_convLoad`, `dataHalf_convStore`, `dataHalf_carryLoad` and `leaderReads`.
* `Source.StateIssues P L X`, `Source.WriteFrame P X`: the assembly of the direct facts
  (group D). Used by the same theorems, except `leaderReads`.
* `Values.Ends.FinalCarries P L X` (the carries at the first final store hold the state after
  the last token): the value induction of the tile loop. Used by `out_final'` and
  `dataHalf_finalStore`.
* `Values.Ends.LeaderReads P L X`, which `ValuesEnds.leaderReads` gives from `F`, `U`, `C` and
  `ValuesEnds.OutStage P L X O` (the field `stage` of `OutContent`: the value induction of the
  tile loop). Used by `dataHalf_elemRead` and `dataHalf_elemStore`.

`convRef`, `carryRef`, `finalRef`, `storeRef`, `storeCtl`, `out_elem'`, `ValuesEnds.followed`
and `ValuesEnds.finalSlots` need nothing besides `hpre` and `hX`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before storeLeader Facts UnionFacts StoreCover Owners
  ctaTiles noEvents no_rmw blockOf blockOf_lt stageOf outByte outStage OutLast FinalLast Bar)
open PTX.Kernels.FlashKdaFwd.Proof.Values (Followed)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (EarlyRead FinalCarries FinalSlots LeaderReads
  finalSite carrySite elemReg chunkOut)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace ValuesEnds

/-- The window of a block starts at a multiple of 32 (of 128, in fact). -/
theorem sharedBase_mod (hpre : Pre P L mem0) : L.sharedBase % 32 = 0 := by
  have h1 := hpre.sharedBase
  have h2 := hpre.sharedAlignment
  omega

/-- **The field `stage` of `Protocol.OutContent`**, as a proposition of its own: the owning
compute thread's last write of a byte of a live row of the output buffer in tile `b` carries
the specified byte `Protocol.outStage`. The value induction of the tile loop proves it. -/
def OutStage (P : Params) (L : Launch) (X : Execution) (O : Owners) : Prop :=
  ∀ {s h : Nat}, s < P.sequences → h < P.heads → ∀ b off : Nat, off < 4096 →
    16 * b + off % 256 / 16 < P.length s →
    ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out (outByte L (blockOf P s h) (stageOf b).val off) = ga.val →
      OutLast L X (blockOf P s h) (stageOf b) ga (b / 2)
        (outByte L (blockOf P s h) (stageOf b).val off) iw aw bw →
        wbyte aw bw (outByte L (blockOf P s h) (stageOf b).val off) = outStage P s h b off

/-- The field `stage` of `OutContent` is `OutStage`. -/
theorem OutStage.of {O : Owners} (V : Protocol.OutContent P L X O) : OutStage P L X O :=
  V.stage

/-- The tensor stores are at the machine's tensor-copy sites from 226 on: the sixteen of a
full tile at instructions of the store leader's loop, the sixteen of the final state in the
epilogue after its second `bar.sync 0`. -/
theorem ts_site_pc : ∀ j : Fin 258, 226 ≤ j.val →
    (2944 < (Site.tensorCopy j).pc ∧ (Site.tensorCopy j).pc ≤ 3112) ∨
      3775 < (Site.tensorCopy j).pc := by decide +kernel

/-- The four element reads of the vector load are at one instruction of the store leader's
loop. -/
theorem read_site_pc {site : Site} {m : Nat} (h : readIdx site = some m) :
    m < 4 ∧ 2944 < site.pc ∧ site.pc ≤ 3112 := by
  have h177 := load177_pc
  cases site <;> simp only [readIdx, reduceCtorEq, Option.some.injEq] at h
  case load j =>
    split at h
    · rename_i hj
      obtain rfl : j = 177 := Fin.ext hj
      simp only [Option.some.injEq] at h
      exact ⟨by omega, h177⟩
    · cases h
  case loadEl1 j v0 =>
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ⟨by omega, h177⟩
  case loadEl2 j v0 v1 =>
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ⟨by omega, h177⟩
  case loadEl3 j v0 v1 v2 =>
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ⟨by omega, h177⟩

/-- A site of the family `ElemReadSite` (`DirectData.lean`) is an element read with an
index. -/
theorem readIdx_of_site {site : Site} (h : ElemReadSite site) : ∃ m, readIdx site = some m := by
  cases site <;> simp only [ElemReadSite] at h
  case load j => exact ⟨0, by simp only [readIdx, h, ↓reduceIte]⟩
  case loadEl1 j v0 => exact ⟨1, rfl⟩
  case loadEl2 j v0 v1 => exact ⟨2, rfl⟩
  case loadEl3 j v0 v1 v2 => exact ⟨3, rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The shared byte that a slot of a final-state store reads** (`Values.Ends.FinalSlots`):
a tensor store with a slot that writes a byte of the final state is a store of the epilogue
(a store of a full tile writes the output array: the field `ts_out` of `Store.storeOwes`),
and the epilogue's `final_slots` gives the byte. -/
theorem finalSlots : FinalSlots P L X := by
  intro s h b i pc al x y z sp l v k hs hh hb he hw hrl
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  obtain ⟨j, hsite, hj⟩ := tensorStore_site (sounds hpre) hX he hσ rfl
  rcases ts_site_pc j hj with ⟨h1, h2⟩ | h1
  · exfalso
    rw [← hsite] at h1 h2
    obtain ⟨-, j0, s0, -, -, -, hI, -⟩ := hst.of_pc_store h1 h2
    exact (Store.storeOwes hpre hX).ts_out _ i d pc al sp x y z _ hg hσ (hI hub) he hw
      ⟨s, hs, h, hh, v, k, b, hb, rfl⟩
  · rw [← hsite] at h1
    obtain ⟨j0, s0, past, hj0, -, -⟩ := hst.of_pc_epilogue (by omega) (.inr (by omega))
    have h := Epilogue.final_slots hpre hX hg ⟨s0, past.state, past.into⟩ hj0 hh hb he hw
    rw [h] at hrl
    exact (Option.some.inj hrl).symm

/-- **What the store leader reads from the output buffers** (`Values.Ends.LeaderReads`): the
protocol layer's read-back `UnionFacts.leader_read`, with the content of the compute threads'
writes of the output stage (`OutStage`, the field `stage` of `OutContent`). -/
theorem leaderReads {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (C : StoreCover L X O) (hstage : OutStage P L X O) : LeaderReads P L X := by
  intro s h hs hh j pcr ar br b off hrd hloc hsz hpolls hlive
  exact U.leader_read C F.life F.load F.store F.state F.init F.bars (noEvents hX) hX hpre.block
    (F.syncGuarded hpre hX) (fun _ _ _ _ _ => no_rmw hX) (blockOf_lt hpre hs hh) hrd (stageOf b)
    (b / 2) off (outStage P s h b) hpolls hloc hsz fun n hn ga iw aw bw =>
      hstage hs hh b (off + n) (by omega) (hlive n hn) ga iw aw bw

/-- **The thread is followed through each read of the store leader's vector load.** A state at
the `m`-th element read with an event is `m` events after a state at the first one (the
field `reads` of `Store.storeOwes`); the reads from there on return pairs of bfloat16 payloads
of outputs (its field `chunk`, with `LeaderReads`), so each rebuilds into a pair and, after
the fourth, the
four unpacks succeed (`Values/Ends/StorePath.lean: chunk_next0` to `chunk_next3`). This is the
per-read form of `Values.Ends.chunk_alive`, which needs all four reads at once. -/
theorem read_alive (hrd : LeaderReads P L X) {k m : Nat} {s : D}
    {e : Event} (hσ : At (code L) X g k s) (hm : readIdx s.site = some m)
    (he : X.get (g, k) = some e) :
    ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') := by
  have SO := Store.storeOwes hpre hX
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hm4, h1, h2⟩ := read_site_pc hm
  obtain ⟨hg, k0, hen, hj, hI, -⟩ := store_entered hpre hX (Nat.le_of_lt hlt) hσ h1 h2
  obtain ⟨hmk, ⟨d0, hσ0, hs0⟩, hrds⟩ :=
    SO.reads g k0 k s e m hg hen hj hσ (hI (noUb_of_lt hX hlt)) hm he
  -- the chunk of the vector load, from its first read
  have hpc0 := load177_pc
  rw [← hs0] at hpc0
  obtain ⟨-, k1, hen1, hj1, hI1, hW1⟩ :=
    store_entered hpre hX (show k - m ≤ (X.tr g).length by omega) hσ0 hpc0.1 hpc0.2
  obtain ⟨hlead, t', row, c', hrow, hc', hlive, hreads, -⟩ :=
    SO.chunk g k1 (k - m) d0 hg hen1 hj1 (by omega) hσ0 hW1 hI1 hs0
  obtain ⟨hsq, -, hbl⟩ := Values.Ends.block_eq (P := P) hblock hgrid hg
  have hread := Values.Ends.leaderReads_at hrd hblock hgrid hg hlead
  have hdiv : g / L.block = blockOf P (Values.seqOf P L g) (Values.headOf P L g) := hbl.symm
  -- what each of the reads returns
  have key : ∀ n ≤ m, ∀ (pcn : Nat) (an : Acc) (bn : List (Option Byte)),
      X.get (g, k - m + n) = some ⟨pcn, .rd an bn⟩ →
      rebuild 3 bn = .ok (WarpMatrix.bf16Pair
        (chunkOut P (Values.seqOf P L g) (Values.headOf P L g) (16 * t' + row) c' (2 * n))
        (chunkOut P (Values.seqOf P L g) (Values.headOf P L g) (16 * t' + row) c'
          (2 * n + 1))) := by
    intro n hn pcn an bn hen'
    obtain ⟨hsz, hloc, hpolls⟩ := hreads n (by omega) pcn an bn hen'
    have hb := hread (k - m + n) pcn an bn t' (16 * row + 256 * c' + 4 * n) hen'
      (by rw [hloc, hdiv]; rfl) (by omega)
      (by
        have hp := hpolls
        unfold Values.Ends.storeFullBar at hp
        rw [hdiv] at hp
        exact hp)
      (fun i hi => by
        have : (16 * row + 256 * c' + 4 * n + i) % 256 / 16 = row := by omega
        omega)
    rw [hsz, Values.Ends.outStage_chunk P _ _ t' hrow (by omega)] at hb
    rw [hb, Values.Ends.rebuild_pair]
  have hk : k + 1 = k - m + m + 1 := by omega
  rw [hk]
  obtain ⟨s0, w, p, x⟩ := d0
  cases hs0
  -- the first read
  obtain ⟨pc0, a0, b0, he0⟩ := hrds 0 (Nat.zero_le _)
  have hσ1 := (Values.Ends.stateAt_step he0 hσ0).trans
    (Values.Ends.chunk_next0 (key 0 (Nat.zero_le _) _ _ _ he0))
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · exact ⟨_, hσ1⟩
  -- the second read
  obtain ⟨pc1, a1, b1, he1⟩ := hrds 1 hm1
  have hσ2 := (Values.Ends.stateAt_step he1 hσ1).trans
    (Values.Ends.chunk_next1 (key 1 hm1 _ _ _ he1))
  rcases Nat.lt_or_ge 1 m with hm2 | hm2
  swap
  · obtain rfl : m = 1 := by omega
    exact ⟨_, hσ2⟩
  -- the third read
  obtain ⟨pc2, a2, b2, he2⟩ := hrds 2 hm2
  have hσ3 := (Values.Ends.stateAt_step he2 hσ2).trans
    (Values.Ends.chunk_next2 (key 2 hm2 _ _ _ he2))
  rcases Nat.lt_or_ge 2 m with hm3 | hm3
  swap
  · obtain rfl : m = 2 := by omega
    exact ⟨_, hσ3⟩
  -- the fourth read, and the four unpacks
  obtain rfl : m = 3 := by omega
  obtain ⟨pc3, a3, b3, he3⟩ := hrds 3 (Nat.le_refl _)
  obtain ⟨d4, hn, -, -⟩ := Values.Ends.chunk_next3 (L := L) (g := g) (w := w) (p := p) (x := x)
    (pc := pc3) (a := a3)
    (fun n => chunkOut P (Values.seqOf P L g) (Values.headOf P L g) (16 * t' + row) c' (2 * n))
    (fun n => chunkOut P (Values.seqOf P L g) (Values.headOf P L g) (16 * t' + row) c'
      (2 * n + 1))
    (key 3 (Nat.le_refl _) _ _ _ he3)
  exact ⟨d4, (Values.Ends.stateAt_step he3 hσ3).trans hn⟩

end

end ValuesEnds

open ValuesEnds

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### The reference-layer contracts of the store path, and the state copy -/

/-- **`StoreRef` for the whole execution**: a write to global memory is the `(4 + i)`-th event
after a state at the store leader's vector load, and the twelve events of a chunk at the
vector load are the four 4-byte reads of the chunk's 16 bytes of the output stage and the
eight 2-byte stores of its outputs. -/
theorem storeRef : Values.Ends.StoreRef P L X :=
  storeRef_of hpre hX (Store.storeOwes hpre hX) (computeOwes hpre hX)

/-- **`StoreCtl` for the whole execution**: the control half of the three families of stores
of data registers (a conversion store, a final store, an element store of a partial tile): if
the source register converts to the store's width, the event is the write of its bytes; and
where a conversion store and an element store come from. -/
theorem storeCtl : Values.Ends.StoreCtl L X :=
  storeCtl_of hpre hX (Store.storeOwes hpre hX)

/-- **The field `acc` of `Values.ReadBack`**: a 16-byte read by a compute thread of a row of
the bfloat16 state copy `state_acc` of its block returns the bytes of the thread's own last
16-byte write of that row, or, when it has made no 16-byte write of the row yet (the first
tile), the bytes the conversion loop left there: the bfloat16 payloads of the initial state.
It remains to show the protocol contracts `F`, `U`, `C` (assembly groups A, B, C1) and the
two hypotheses of the sources (group D). -/
theorem readBack_acc {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (C : StoreCover L X O) (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) :
    ∀ g k pc a bs o, g % L.block < 128 → X.get (g, k) = some ⟨pc, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, P.sharedBase + o⟩ → a.size = 16 → o + 16 ≤ 32768 →
      (∃ k' < k, ∃ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ ∧ a'.loc = a.loc ∧
          a'.size = 16 ∧ bs = bs'.map some ∧
          ∀ k'', k' < k'' → k'' < k → ∀ pc'' a'' bs'',
            X.get (g, k'') = some ⟨pc'', .wr a'' bs''⟩ → a''.size = 16 → a''.loc ≠ a.loc) ∨
        ((∀ k' < k, ∀ pc' a' bs', X.get (g, k') = some ⟨pc', .wr a' bs'⟩ → a'.size = 16 →
            a'.loc ≠ a.loc) ∧
          bs = (List.range 16).map fun i =>
            Values.accInitByte P (Values.seqOf P L g) (Values.headOf P L g) (o + i)) :=
  readBack_acc_of hpre hX F U C hSI hW (Store.storeOwes hpre hX) (computeOwes hpre hX)

/-! ### The fields `final` and `elem` of `OutContent` -/

/-- **The field `final` of `Protocol.OutContent`**: the owning compute thread's last write in
the epilogue of the shared byte that a final-state store copies to byte `b` of entry `(v, k)`
carries the byte of the binary32 payload of the state after the last token. It remains to show
that the carries hold that state at the first final store (`FinalCarries`: the value induction
of the tile loop). -/
theorem out_final' (hfin : FinalCarries P L X) {O : Owners}
    {s h b i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} {v k : Fin 128}
    (hs : s < P.sequences) (hh : h < P.heads) (hb4 : b < 4)
    (hst : X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩)
    (hwl : TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b))
    (hrl : TensorStore.readLoc sp x y z = some l) (ga : Fin 128) (iw : Nat) (aw : Acc)
    (bw : List Byte) (hown : O.final l = ga.val)
    (hlast : FinalLast L X (blockOf P s h) ga l iw aw bw) :
    wbyte aw bw l = some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b) :=
  Values.Ends.out_final (ValuesEnds.followed hpre hX) (finalRef hpre hX) hfin
    (finalSlots hpre hX) hpre.block (sharedBase_mod hpre) hs hh hb4 hst hwl hrl ga iw aw bw
    hown hlast

/-- **The field `elem` of `Protocol.OutContent`**: a write event of the store leader that
covers an output byte carries the byte of the bfloat16 payload of the specified output there,
given that the leader's earlier reads of live rows of the output buffers returned the specified
content of their tiles. -/
theorem out_elem' {s h t k i pc : Nat} {a : Acc} {bs : List Byte} {v : Fin 128}
    (hs : s < P.sequences) (hh : h < P.heads) (ht : t < P.length s) (hk : k < 2)
    (hw : X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .wr a bs⟩)
    (hc : a.Covers ((P.outLoc s h t v).at k))
    (hread : ∀ j < i, ∀ (pcr : Nat) (ar : Acc) (br : List (Option Byte)) (b off : Nat),
      X.get (storeLeader L (blockOf P s h), j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P s h) (stageOf b).val off → off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P s h))
        ((X.tr (storeLeader L (blockOf P s h))).take j) = b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length s) →
        br = (List.range ar.size).map fun n => outStage P s h b (off + n)) :
    wbyte a bs ((P.outLoc s h t v).at k) =
      some ((Value.float .bf16 (P.output s h t v)).byteAt k) :=
  Values.Ends.out_elem (ValuesEnds.followed hpre hX) (storeRef hpre hX) hpre.block hs hh ht hk
    hw hc hread

/-! ### The data half of "no undefined-behaviour event", per field of `DataHalf` -/

/-- **`DataHalf.convLoad`**: after a conversion load the successor is followed (the bytes read
are a binary32 payload of the initial state, which `cvt.rn.bf16.f32` narrows). -/
theorem dataHalf_convLoad {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) :
    ∀ g k s e (j : Fin 10), g < L.threads →
      Frame.stateAt (code L) X g k = some (some s) → s.site = .load ⟨21 + j.val, by omega⟩ →
      X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') := by
  intro g k s e j _ hσ hs he
  obtain ⟨el, -, d', hσ', -⟩ := Values.Ends.conv_alive (P := P) (convRef hpre hX)
    (earlyRead hpre hX F U hSI hW) (sharedBase_mod hpre) j hσ hs he
  exact ⟨d', hσ'⟩

/-- **`DataHalf.convStore`**: a conversion store is not undefined behaviour (its source
register holds the bfloat16 payload that the conversion load before it produced). -/
theorem dataHalf_convStore {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) :
    ∀ g k s e (j : Fin 10), g < L.threads →
      Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨j.val, by omega⟩ →
      X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  intro g k s e j _ hσ hs he
  obtain ⟨⟨k0, d0, rfl, hσ0, hs0⟩, hctl⟩ := storeCtl_conv hpre hX j hσ hs he
  obtain ⟨e0, he0⟩ := Values.Ends.get_of_lt he (Nat.lt_succ_self k0)
  obtain ⟨el, -, d', hσ', -, hx, -⟩ := Values.Ends.conv_alive (P := P) (convRef hpre hX)
    (earlyRead hpre hX F U hSI hW) (sharedBase_mod hpre) j hσ0 hs0 he0
  rw [hσ] at hσ'
  cases hσ'
  obtain ⟨a, ha⟩ := hctl _ (Values.Ends.conv_store_ok hx)
  exact Values.Ends.wr_not_ub ha

/-- **`DataHalf.carryLoad`**: the bytes that a carry load of a compute thread reads rebuild to
a 32-bit value (the binary32 payload of an entry of the initial state). -/
theorem dataHalf_carryLoad {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) :
    ∀ g k s (j : Fin 128) pc a bs, g < L.threads → g % L.block < 128 →
      Frame.stateAt (code L) X g k = some (some s) → s.site = .load ⟨31 + j.val, by omega⟩ →
      X.get (g, k) = some ⟨pc, .rd a bs⟩ → ∃ v, ldVal .same 32 bs = .ok v := by
  intro g k s j pc a bs _ hc hσ hs he
  have hs' : s.site = carrySite j.val := by
    rw [hs]
    simp only [carrySite, j.isLt, ↓reduceDIte]
  obtain ⟨a', bs', h, hok⟩ := Values.Ends.carry_load_ok (P := P) (carryRef hpre hX)
    (earlyRead hpre hX F U hSI hW) (sharedBase_mod hpre) j hc hσ hs' he
  cases h
  exact ⟨_, hok⟩

/-- **`DataHalf.finalStore`**: a final store of a compute thread is not undefined behaviour
(its carry register holds a binary32 payload). It remains to show `FinalCarries`. -/
theorem dataHalf_finalStore (hfin : FinalCarries P L X) :
    ∀ g k s e (j : Fin 128), g < L.threads → g % L.block < 128 →
      Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨18 + j.val, by omega⟩ →
      X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  intro g k s e j _ hc hσ hs he
  have hs' : s.site = finalSite j := hs
  have hk : k ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨a, ha⟩ := storeCtl_final hpre hX j hσ hs' he
    (Values.Ends.final_store_ok (ValuesEnds.followed hpre hX) (finalRef hpre hX) hfin j hc hk hσ
      hs')
  exact Values.Ends.wr_not_ub ha

/-- **`DataHalf.elemRead`**: after each of the four element reads of the store leader's vector
load the successor is followed. It remains to show `LeaderReads` (`ValuesEnds.leaderReads`). -/
theorem dataHalf_elemRead (hrd : LeaderReads P L X) :
    ∀ g k s e, g < L.threads →
      Frame.stateAt (code L) X g k = some (some s) → ElemReadSite s.site →
      X.get (g, k) = some e → ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') := by
  intro g k s e _ hσ hsite he
  obtain ⟨m, hm⟩ := readIdx_of_site hsite
  exact read_alive hpre hX hrd hσ hm he

/-- **`DataHalf.elemStore`**: an element store of a partial last tile is not undefined
behaviour (its source register holds the bfloat16 payload of an output). It remains to show
`LeaderReads` (`ValuesEnds.leaderReads`). -/
theorem dataHalf_elemStore (hrd : LeaderReads P L X) :
    ∀ g k s e (i : Fin 8), g < L.threads →
      Frame.stateAt (code L) X g k = some (some s) → s.site = .store ⟨10 + i.val, by omega⟩ →
      X.get (g, k) = some e → ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  intro g k s e i _ hσ hs he
  exact Values.Ends.elem_store_not_ub (ValuesEnds.followed hpre hX) (storeRef hpre hX)
    (storeCtl hpre hX) hrd hpre.block hpre.grid i hσ hs he

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
