-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.StorePath

@[expose] public section

/-!
# The data half of "no undefined behaviour" at the ends of the tile loop

An event of a thread is undefined behaviour (`⟨pc, .ub f⟩`) when its instruction faults; a
thread also stops being followed (`stateAt … = none`) when a local instruction after an event
faults, and its next event is then undefined behaviour. At the sites of the four stretches the
faults have two sources: the *control* (an address that is none, is misaligned or leaves the
window: the reference layer's part) and the *data* (a loaded value that does not rebuild, a
conversion or an unpack of a value of the wrong kind, a store of a value of the wrong width).
This file states the data half, per stretch, against the machine's own transitions.

* A, conversion load: `conv_load_not_ub` (the phase's claim, restated) and
  `Conversion.lean: conv_alive`: the successor is followed (the run `cvt.rn.bf16.f32` after
  the load does not fault).
* A, conversion store: `conv_store_wr`, `conv_store_not_ub`: the event is the write of the
  bfloat16 payload.
* B, carry load: `carry_not_ub` (the phase's claim) and `CarryLoad.lean: carry_load_ok`: the
  loaded bytes rebuild into the payload.
* C, final store: `final_store_wr`, `final_store_not_ub`: the event is the write of the
  binary32 payload.
* D, vector load: `chunk_alive`: when the four events are reads, the thread is followed
  through them and the four unpacks, to the first element store.
* D, element store: `elem_store_wr`, `elem_store_not_ub`: the event is the write of the
  bfloat16 payload of an output.

What is *not* here, because no data value is involved: that a load event is a read (a load
faults on its address only: `ConvRef.load` and `CarryRef.load` assert it, and `chunk_alive`
takes it as its hypothesis `hrds`), and the conditions of the pointer runs after a carry load
and after a final store (`Run.r766_cond`, …, `Run.r3133_cond`, …: the arithmetic of the next
address on the base pointer; `Proof/Thread/RunPtr.lean`). After a carry load the machine's
transition is `match ldVal .same 32 bs with | .ok v => across (pointer run condition) … |
.error _ => none`: `carry_load_ok` excludes the second branch.

The store statements combine the value half (the source register holds a payload of the
store's width) with the control half `StoreCtl` ("if the source converts, the event is the
write of its bytes").
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (storeLeader blockOf stageOf outByte outStage Bar
  storeLeader_div cta_lt)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : ℕ}

/-- A write event is not undefined behaviour. -/
theorem wr_not_ub {e : Event} {pc : ℕ} {a : Acc} {bs : List Byte} (h : e = ⟨pc, .wr a bs⟩) :
    ∀ pc' f, e ≠ ⟨pc', .ub f⟩ := by
  rintro pc' f rfl
  cases h

/-- A read event is not undefined behaviour. -/
theorem rd_not_ub {e : Event} {pc : ℕ} {a : Acc} {bs : List (Option Byte)}
    (h : e = ⟨pc, .rd a bs⟩) : ∀ pc' f, e ≠ ⟨pc', .ub f⟩ := by
  rintro pc' f rfl
  cases h

/-! ## A. The conversion loop -/

/-- A conversion load is a read (`ConvRef.load`), so no undefined behaviour. -/
theorem conv_load_not_ub (R : ConvRef L X) {k : ℕ} {d : D} {e : Event} (j : Fin 10)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = .load ⟨21 + j.val, by omega⟩)
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨el, -, a, bs, h, -⟩ := R.load g k d e j hσ hs he
  exact rd_not_ub h

/-- **A conversion store is the write of a bfloat16 payload of the initial state.** -/
theorem conv_store_wr (R : ConvRef L X) (C : StoreCtl L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {k : ℕ} {d : D} {e : Event} (j : Fin 10)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = .store ⟨j.val, by omega⟩)
    (he : X.get (g, k) = some e) :
    ∃ el < 16384, ∃ a, e = ⟨d.site.pc, .wr a
      (Value.float .bf16 (entry (initState P (g / L.block)) el)).toBytes⟩ := by
  obtain ⟨⟨k0, d0, rfl, hσ0, hs0⟩, hctl⟩ := C.conv g k d e j hσ hs he
  obtain ⟨e0, he0⟩ := get_of_lt he (Nat.lt_succ_self k0)
  obtain ⟨el, hel, d', hσ', -, hx, -⟩ := conv_alive (P := P) R hrd hb j hσ0 hs0 he0
  rw [hσ] at hσ'
  cases hσ'
  obtain ⟨a, ha⟩ := hctl _ (conv_store_ok hx)
  exact ⟨el, hel, a, ha⟩

/-- **A conversion store is not undefined behaviour.** -/
theorem conv_store_not_ub (R : ConvRef L X) (C : StoreCtl L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {k : ℕ} {d : D} {e : Event} (j : Fin 10)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = .store ⟨j.val, by omega⟩)
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨el, -, a, h⟩ := conv_store_wr (P := P) R C hrd hb j hσ hs he
  exact wr_not_ub h

/-! ## B. The carry loads -/

/-- A carry load is a read (`CarryRef.load`), so no undefined behaviour. -/
theorem carry_not_ub (R : CarryRef L X) {k : ℕ} {d : D} {e : Event} (j : Fin 128)
    (hg : g % L.block < 128) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = carrySite j.val) (he : X.get (g, k) = some e) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨a, bs, h, -⟩ := R.load g k d e j hg hσ hs he
  exact rd_not_ub h

/-! ## C. The final stores -/

/-- **A final store is the write of the binary32 payload of an entry of the final state.** -/
theorem final_store_wr (F : Followed L mem0 X) (R : FinalRef L X) (C : StoreCtl L X)
    (hfin : FinalCarries P L X) {k : ℕ} {d : D} {e : Event} (j : Fin 128)
    (hg : g % L.block < 128) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = finalSite j) (he : X.get (g, k) = some e) :
    ∃ a, e = ⟨d.site.pc, .wr a (Value.float .f32
      (entry (finalState P (g / L.block)) (carryElem j.val (g % L.block)))).toBytes⟩ :=
  C.final g k d e j hg hσ hs he _
    (final_store_ok F R hfin j hg (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1) hσ hs)

/-- **A final store is not undefined behaviour.** -/
theorem final_store_not_ub (F : Followed L mem0 X) (R : FinalRef L X) (C : StoreCtl L X)
    (hfin : FinalCarries P L X) {k : ℕ} {d : D} {e : Event} (j : Fin 128)
    (hg : g % L.block < 128) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = finalSite j) (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨a, h⟩ := final_store_wr F R C hfin j hg hσ hs he
  exact wr_not_ub h

/-! ## D. The store path of a partial tile -/

/-- The block of a launched thread, as the block of a sequence and a head. -/
theorem block_eq (hblock : L.block = 192) (hgrid : L.grid = P.sequences * P.heads)
    (hgt : g < L.threads) :
    g / L.block % P.sequences < P.sequences ∧ g / L.block / P.sequences < P.heads ∧
      blockOf P (g / L.block % P.sequences) (g / L.block / P.sequences) = g / L.block := by
  have hc : g / L.block < P.sequences * P.heads := hgrid ▸ cta_lt hblock hgt
  have hN : 0 < P.sequences := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.zero_mul] at hc
    exact Nat.not_lt_zero _ hc
  exact ⟨Nat.mod_lt _ hN, Nat.div_lt_of_lt_mul hc, Nat.div_add_mod' _ _⟩

/-- The standing read-back of the store leader, for a thread that is the leader of its
block. -/
theorem leaderReads_at (hrd : LeaderReads P L X) (hblock : L.block = 192)
    (hgrid : L.grid = P.sequences * P.heads) (hgt : g < L.threads)
    (hlead : g = storeLeader L (g / L.block)) :
    ∀ (j pcr : ℕ) (ar : Acc) (br : List (Option Byte)) (b off : ℕ),
      X.get (g, j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P (seqOf P L g) (headOf P L g)) (stageOf b).val off →
      off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P (seqOf P L g) (headOf P L g)))
        ((X.tr g).take j) = b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length (seqOf P L g)) →
        br = (List.range ar.size).map fun n =>
          outStage P (seqOf P L g) (headOf P L g) b (off + n) := by
  obtain ⟨hs, hh, hbl⟩ := block_eq (P := P) hblock hgrid hgt
  have h := hrd hs hh
  rw [hbl, ← hlead] at h
  intro j pcr ar br b off he hloc hsz hpolls hlive
  unfold seqOf headOf at hloc hpolls
  rw [hbl] at hloc hpolls
  exact h j pcr ar br b off he hloc hsz hpolls hlive

/-- **An element store is the write of the bfloat16 payload of an output.** -/
theorem elem_store_wr (F : Followed L mem0 X) (R : StoreRef P L X) (C : StoreCtl L X)
    (hrd : LeaderReads P L X) (hblock : L.block = 192) (hgrid : L.grid = P.sequences * P.heads)
    {k : ℕ} {d : D} {e : Event} (i : Fin 8) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = .store ⟨10 + i.val, by omega⟩) (he : X.get (g, k) = some e) :
    ∃ a tok c, tok < P.length (seqOf P L g) ∧ e = ⟨d.site.pc, .wr a
      (Value.float .bf16 (chunkOut P (seqOf P L g) (headOf P L g) tok c i.val)).toBytes⟩ := by
  obtain ⟨⟨k0, d0, rfl, hσ0, hs0⟩, hctl⟩ := C.elem g k d e i hσ hs he
  have hgt := lt_threads F he
  obtain ⟨hlead, -⟩ := R.chunk g k0 d0 hσ0 hs0
  obtain ⟨hsq, -, hbl⟩ := block_eq (P := P) hblock hgrid hgt
  have hread := leaderReads_at hrd hblock hgrid hgt hlead
  obtain ⟨t', row, c', hlive, -, hsrc, -⟩ := chunk_state F R hblock hsq
    (by
      have h1 := hlead.symm
      rw [← hbl] at h1
      exact h1) i.isLt hσ0 hs0 hσ he
    (fun j _ pcr ar br b off => hread j pcr ar br b off)
  obtain ⟨a, ha⟩ := hctl _ (elem_store_ok hsrc)
  exact ⟨a, _, c', hlive, ha⟩

/-- **An element store is not undefined behaviour.** -/
theorem elem_store_not_ub (F : Followed L mem0 X) (R : StoreRef P L X) (C : StoreCtl L X)
    (hrd : LeaderReads P L X) (hblock : L.block = 192) (hgrid : L.grid = P.sequences * P.heads)
    {k : ℕ} {d : D} {e : Event} (i : Fin 8) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = .store ⟨10 + i.val, by omega⟩) (he : X.get (g, k) = some e) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  obtain ⟨a, tok, c, -, h⟩ := elem_store_wr F R C hrd hblock hgrid i hσ hs he
  exact wr_not_ub h

/-- **The thread is followed through the vector load and the four unpacks.** At the vector
load, when the next four events are reads (the control half: a load faults on its address
only), the bytes they return are pairs of bfloat16 payloads of outputs, so each rebuilds into
a pair, the four unpacks succeed, and four positions later the machine is at the first element
store with the eight outputs of the chunk in the source registers of the eight stores. -/
theorem chunk_alive (F : Followed L mem0 X) (R : StoreRef P L X) (hrd : LeaderReads P L X)
    (hblock : L.block = 192) (hgrid : L.grid = P.sequences * P.heads) {k0 : ℕ} {d0 : D}
    (hσ0 : stateAt (code L) X g k0 = some (some d0)) (hs0 : d0.site = .load 177)
    (hrds : ∀ m < 4, ∃ pc a bs, X.get (g, k0 + m) = some ⟨pc, .rd a bs⟩) :
    ∃ d4 tok c, stateAt (code L) X g (k0 + 4) = some (some d4) ∧ d4.site = .store 10 ∧
      ∀ i < 8, d4.x (elemReg i) =
        .float .bf16 (chunkOut P (seqOf P L g) (headOf P L g) tok c i) := by
  obtain ⟨pc0, a0, b0, he0⟩ := hrds 0 (by omega)
  obtain ⟨pc1, a1, b1, he1⟩ := hrds 1 (by omega)
  obtain ⟨pc2, a2, b2, he2⟩ := hrds 2 (by omega)
  obtain ⟨pc3, a3, b3, he3⟩ := hrds 3 (by omega)
  have hgt := lt_threads F he0
  obtain ⟨hlead, t', row, c', hrow, hc', hlive, hreads, -⟩ := R.chunk g k0 d0 hσ0 hs0
  obtain ⟨hsq, -, hbl⟩ := block_eq (P := P) hblock hgrid hgt
  have hread := leaderReads_at hrd hblock hgrid hgt hlead
  have hdiv : g / L.block = blockOf P (seqOf P L g) (headOf P L g) := hbl.symm
  -- what each of the four reads returns
  have key : ∀ m < 4, ∀ (pcm : ℕ) (am : Acc) (bm : List (Option Byte)),
      X.get (g, k0 + m) = some ⟨pcm, .rd am bm⟩ →
      rebuild 3 bm = .ok (bf16Pair
        (chunkOut P (seqOf P L g) (headOf P L g) (16 * t' + row) c' (2 * m))
        (chunkOut P (seqOf P L g) (headOf P L g) (16 * t' + row) c' (2 * m + 1))) := by
    intro m hm pcm am bm he
    obtain ⟨hsz, hloc, hpolls⟩ := hreads m hm pcm am bm he
    have hb := hread (k0 + m) pcm am bm t' (16 * row + 256 * c' + 4 * m) he
      (by rw [hloc, hdiv]; rfl) (by omega)
      (by
        have hp := hpolls
        unfold storeFullBar at hp
        rw [hdiv] at hp
        exact hp)
      (fun n hn => by
        have : (16 * row + 256 * c' + 4 * m + n) % 256 / 16 = row := by omega
        omega)
    rw [hsz, outStage_chunk P _ _ t' hrow hm] at hb
    rw [hb, rebuild_pair]
  obtain ⟨s0, w, p, x⟩ := d0
  cases hs0
  have hσ1 := (stateAt_step he0 hσ0).trans (chunk_next0 (key 0 (by omega) _ _ _ he0))
  have hσ2 := (stateAt_step he1 hσ1).trans (chunk_next1 (key 1 (by omega) _ _ _ he1))
  have hσ3 := (stateAt_step he2 hσ2).trans (chunk_next2 (key 2 (by omega) _ _ _ he2))
  obtain ⟨d4, hn, hs4, hx⟩ := chunk_next3 (L := L) (g := g) (w := w) (p := p) (x := x)
    (pc := pc3) (a := a3)
    (fun m => chunkOut P (seqOf P L g) (headOf P L g) (16 * t' + row) c' (2 * m))
    (fun m => chunkOut P (seqOf P L g) (headOf P L g) (16 * t' + row) c' (2 * m + 1))
    (key 3 (by omega) _ _ _ he3)
  refine ⟨d4, 16 * t' + row, c', (stateAt_step he3 hσ3).trans hn, hs4, fun i hi => ?_⟩
  rw [hx i hi]
  congr 1
  split_ifs with hpar
  · congr 1
    omega
  · congr 1
    omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
