-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.FinalStore

@[expose] public section

/-!
# D. The store path of a partial last tile: the outputs pass through the leader's registers

A full tile of outputs goes from the output stage to global memory by tensor stores; nothing
passes through registers. For a partial last tile the store leader copies each live row itself:
sixteen times per row, a vector load `ld.shared.v4.b32` of 16 bytes of the output stage (four
read events of four bytes each, the sites `load 177`, `loadEl1`, `loadEl2`, `loadEl3`), four
`mov.b32 {lo, hi}, r` that unpack the four registers into eight 16-bit registers (the run
`r3021`), and eight `st.global.b16` (the sites `store 10` to `store 17`).

* **The machine along one chunk.** `chunk_step0` to `chunk_step3`: a followed successor of a
  read site was reached by a read whose bytes rebuild into a value, which the next site
  carries; after the fourth, the run has unpacked the four values. `chunk_next0` to
  `chunk_next3` are the converse (the thread is alive): when the bytes of each read are those
  of two bfloat16 payloads, they rebuild into a pair, the four unpacks succeed (`pair_cond`),
  and the machine continues to `store 10` with the eight payloads in the eight source registers
  (`pair_unpacked`). `elem_step`: the stores change no register. `elem_wr`: a write event at
  the `i`-th store writes the bytes of the stored form of its source register.
* `chunk_state`: the state at an element store, from the vector load of its chunk: the
  store's source register holds the bfloat16 payload of the output it stores.
* `out_elem`: **the field `elem` of `Protocol.OutContent`** (`Proof/Protocol/ResultGlue.lean`),
  verbatim: a write event of the store leader that covers an output byte of token `t` and
  channel `v` writes there the byte of the bfloat16 payload of `P.output s h t v`, given that
  the leader's earlier reads of live rows of the output stage returned the specified content
  `Protocol.outStage` of their tile. Hypotheses: `Followed`, `StoreRef` (the Store phase),
  `L.block = 192`.
* `elem_store_ok`: the source of an element store is a 16-bit payload, so the store is not
  undefined behaviour because of its value.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (storeLeader blockOf stageOf outByte outStage Bar
  storeLeader_div)
open PTX.Kernels.FlashKdaFwd.Recurrence (firstToken)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : ℕ}

/-! ## The machine along one chunk -/

/-- The slots after the vector load, when its four elements are pairs of bfloat16 payloads
`(lo m, hi m)`. -/
def pairSlots (x : ℕ → Value) (lo hi : ℕ → ℝ) : ℕ → Value :=
  valueEx x ([1126, 1127, 1128, 1129].zip [bf16Pair (lo 0) (hi 0), bf16Pair (lo 1) (hi 1),
    bf16Pair (lo 2) (hi 2), bf16Pair (lo 3) (hi 3)])

/-- **The four unpacks succeed on pairs**: the condition of the run after the vector load. -/
theorem pair_cond (s : Site) (w : ℕ → BitVec 64) (p : ℕ → Bool) (x : ℕ → Value)
    (lo hi : ℕ → ℝ) : Run.r3021_cond (valueOf ⟨s, w, p, pairSlots x lo hi⟩) :=
  ⟨⟨⟨⟨_, Rules.unpackE32_pair (a := .float .bf16 (lo 3)) (b := .float .bf16 (hi 3)) rfl rfl⟩,
    ⟨_, Rules.unpackE32_pair (a := .float .bf16 (lo 2)) (b := .float .bf16 (hi 2)) rfl rfl⟩⟩,
    ⟨_, Rules.unpackE32_pair (a := .float .bf16 (lo 1)) (b := .float .bf16 (hi 1)) rfl rfl⟩⟩,
    ⟨_, Rules.unpackE32_pair (a := .float .bf16 (lo 0)) (b := .float .bf16 (hi 0)) rfl rfl⟩⟩

/-- **The unpacked registers**: the source register of the `i`-th element store holds half
`i % 2` of element `i / 2` of the vector load. -/
theorem pair_unpacked (s : Site) (w : ℕ → BitVec 64) (p : ℕ → Bool) (x : ℕ → Value)
    (lo hi : ℕ → ℝ) (i : ℕ) (hi' : i < 8) :
    valueEx (pairSlots x lo hi) (Run.r3021_facts4 (valueOf ⟨s, w, p, pairSlots x lo hi⟩))
        (elemReg i) =
      .float .bf16 (if i % 2 = 0 then lo (i / 2) else hi (i / 2)) := by
  interval_cases i <;> rfl

/-- The thread is alive after the first read of the vector load when its bytes rebuild. -/
theorem chunk_next0 {w : ℕ → BitVec 64} {p : ℕ → Bool} {x : ℕ → Value} {pc : ℕ} {a : Acc}
    {bs : List (Option Byte)} {v : Value} (hv : rebuild 3 bs = .ok v) :
    Thread.next L g ⟨.load 177, w, p, x⟩ ⟨pc, .rd a bs⟩ =
      some (some ⟨.loadEl1 0 v, w, p, x⟩) := by
  rw [next_load_177]
  simp only [hv]

theorem chunk_next1 {w : ℕ → BitVec 64} {p : ℕ → Bool} {x : ℕ → Value} {pc : ℕ} {a : Acc}
    {bs : List (Option Byte)} {v0 v : Value} (hv : rebuild 3 bs = .ok v) :
    Thread.next L g ⟨.loadEl1 0 v0, w, p, x⟩ ⟨pc, .rd a bs⟩ =
      some (some ⟨.loadEl2 0 v0 v, w, p, x⟩) := by
  rw [next_loadEl1_0]
  simp only [hv]

theorem chunk_next2 {w : ℕ → BitVec 64} {p : ℕ → Bool} {x : ℕ → Value} {pc : ℕ} {a : Acc}
    {bs : List (Option Byte)} {v0 v1 v : Value} (hv : rebuild 3 bs = .ok v) :
    Thread.next L g ⟨.loadEl2 0 v0 v1, w, p, x⟩ ⟨pc, .rd a bs⟩ =
      some (some ⟨.loadEl3 0 v0 v1 v, w, p, x⟩) := by
  rw [next_loadEl2_0]
  simp only [hv]

/-- **The thread is alive after the vector load of four pairs**: the fourth read rebuilds, the
four unpacks succeed, and the machine is at the first element store with the eight payloads in
the source registers of the eight stores. -/
theorem chunk_next3 {w : ℕ → BitVec 64} {p : ℕ → Bool} {x : ℕ → Value} {pc : ℕ} {a : Acc}
    {bs : List (Option Byte)} (lo hi : ℕ → ℝ)
    (hv : rebuild 3 bs = .ok (bf16Pair (lo 3) (hi 3))) :
    ∃ d', Thread.next L g ⟨.loadEl3 0 (bf16Pair (lo 0) (hi 0)) (bf16Pair (lo 1) (hi 1))
        (bf16Pair (lo 2) (hi 2)), w, p, x⟩ ⟨pc, .rd a bs⟩ = some (some d') ∧
      d'.site = .store 10 ∧ ∀ i < 8, d'.x (elemReg i) =
        .float .bf16 (if i % 2 = 0 then lo (i / 2) else hi (i / 2)) := by
  refine ⟨after_loadEl3_0 L g ⟨.loadEl3 0 (bf16Pair (lo 0) (hi 0)) (bf16Pair (lo 1) (hi 1))
      (bf16Pair (lo 2) (hi 2)), w, p, x⟩ (bf16Pair (lo 0) (hi 0)) (bf16Pair (lo 1) (hi 1))
      (bf16Pair (lo 2) (hi 2)) (bf16Pair (lo 3) (hi 3)), ?_, rfl,
    fun i hi' => pair_unpacked _ w p x lo hi i hi'⟩
  rw [next_loadEl3_0]
  simp only [hv]
  exact across_pos (pair_cond _ w p x lo hi)

/-- A followed successor of the first read site: the event was a read whose bytes rebuild. -/
theorem chunk_step0 {d d' : D} {e : Event} (hs : d.site = .load 177)
    (hn : Thread.next L g d e = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ d' = ⟨.loadEl1 0 v, d.w, d.p, d.x⟩ := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_load_177] at hn
  split at hn
  · rename_i a bs hk
    split at hn
    · rename_i v hv
      cases hn
      exact ⟨a, bs, v, hk, hv, rfl⟩
    · cases hn
  · cases hn

theorem chunk_step1 {d d' : D} {e : Event} {v0 : Value} (hs : d.site = .loadEl1 0 v0)
    (hn : Thread.next L g d e = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧
      d' = ⟨.loadEl2 0 v0 v, d.w, d.p, d.x⟩ := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_loadEl1_0] at hn
  split at hn
  · rename_i a bs hk
    split at hn
    · rename_i v hv
      cases hn
      exact ⟨a, bs, v, hk, hv, rfl⟩
    · cases hn
  · cases hn

theorem chunk_step2 {d d' : D} {e : Event} {v0 v1 : Value} (hs : d.site = .loadEl2 0 v0 v1)
    (hn : Thread.next L g d e = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧
      d' = ⟨.loadEl3 0 v0 v1 v, d.w, d.p, d.x⟩ := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_loadEl2_0] at hn
  split at hn
  · rename_i a bs hk
    split at hn
    · rename_i v hv
      cases hn
      exact ⟨a, bs, v, hk, hv, rfl⟩
    · cases hn
  · cases hn

/-- A followed successor of the fourth read site is at the first element store, after the run
of the four unpacks on the four values read. -/
theorem chunk_step3 {d d' : D} {e : Event} {v0 v1 v2 : Value}
    (hs : d.site = .loadEl3 0 v0 v1 v2) (hn : Thread.next L g d e = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ d'.site = .store 10 ∧
      d'.x = valueEx (valueEx d.x ([1126, 1127, 1128, 1129].zip [v0, v1, v2, v]))
        (Run.r3021_facts4 (valueOf ⟨d.site, d.w, d.p,
          valueEx d.x ([1126, 1127, 1128, 1129].zip [v0, v1, v2, v])⟩)) := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [next_loadEl3_0] at hn
  split at hn
  · rename_i a bs hk
    split at hn
    · rename_i v hv
      obtain ⟨-, rfl⟩ := across_eq_some hn
      exact ⟨a, bs, v, hk, hv, rfl, rfl⟩
    · cases hn
  · cases hn

private theorem elem_step_at {j j' : Fin 146} {d d' : D} {e : Event} (hs : d.site = .store j)
    (hnext : ∀ w p x, Thread.next L g ⟨.store j, w, p, x⟩ e = some (some ⟨.store j', w, p, x⟩))
    (hn : Thread.next L g d e = some (some d')) : d'.site = .store j' ∧ d'.x = d.x := by
  obtain ⟨s, w, p, x⟩ := d
  cases hs
  rw [hnext] at hn
  cases hn
  exact ⟨rfl, rfl⟩

/-- **An element store changes no register**: a followed successor of the `n`-th of the first
seven is at the next one, with the same slots. -/
theorem elem_step {n : ℕ} (hn : n < 7) {d d' : D} {e : Event}
    (hs : d.site = .store ⟨10 + n, by omega⟩) (hnx : Thread.next L g d e = some (some d')) :
    d'.site = .store ⟨11 + n, by omega⟩ ∧ d'.x = d.x := by
  interval_cases n
  · have hs' : d.site = .store 10 := hs
    exact elem_step_at (j := 10) (j' := 11) hs' (fun w p x => next_store_10 w p x e) hnx
  · have hs' : d.site = .store 11 := hs
    exact elem_step_at (j := 11) (j' := 12) hs' (fun w p x => next_store_11 w p x e) hnx
  · have hs' : d.site = .store 12 := hs
    exact elem_step_at (j := 12) (j' := 13) hs' (fun w p x => next_store_12 w p x e) hnx
  · have hs' : d.site = .store 13 := hs
    exact elem_step_at (j := 13) (j' := 14) hs' (fun w p x => next_store_13 w p x e) hnx
  · have hs' : d.site = .store 14 := hs
    exact elem_step_at (j := 14) (j' := 15) hs' (fun w p x => next_store_14 w p x e) hnx
  · have hs' : d.site = .store 15 := hs
    exact elem_step_at (j := 15) (j' := 16) hs' (fun w p x => next_store_15 w p x e) hnx
  · have hs' : d.site = .store 16 := hs
    exact elem_step_at (j := 16) (j' := 17) hs' (fun w p x => next_store_16 w p x e) hnx

/-- **The bytes of an element store**: those of the stored form of its source register. -/
theorem elem_wr (F : Followed L mem0 X) {n : ℕ} (hn : n < 8) {k pc : ℕ} {a : Acc}
    {bs : List Byte} {d : D} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = .store ⟨10 + n, by omega⟩) :
    ∃ v', storeValue 16 (d.x (elemReg n)) = .ok v' ∧ bs = v'.toBytes := by
  interval_cases n
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3025) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3026) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3027) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3028) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3029) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3030) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3031) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl
  · exact store_bytes_direct F he hσ (by rw [hs]; exact Flow.code_3032) rfl
      (fun _ => memTmpl_direct_weakStore rfl rfl rfl rfl rfl) (by rw [hs]; rfl)
      (by rw [hs]; kernel_rfl) rfl

/-- From the first element store on: `n` positions later the thread is at the `n`-th element
store, with the slots it had at the first. -/
theorem elem_prefix (F : Followed L mem0 X) {k4 : ℕ} {d4 : D}
    (hσ4 : stateAt (code L) X g k4 = some (some d4)) (hs4 : d4.site = .store 10) :
    ∀ n, ∀ hn : n < 8, ∀ d, k4 + n ≤ (X.tr g).length →
      stateAt (code L) X g (k4 + n) = some (some d) →
      d.site = .store ⟨10 + n, by omega⟩ ∧ d.x = d4.x := by
  intro n
  induction n with
  | zero =>
    intro _ d _ hσ
    rw [Nat.add_zero, hσ4] at hσ
    cases hσ
    exact ⟨hs4, rfl⟩
  | succ n ih =>
    intro hn d' hlen hσ'
    obtain ⟨e, he⟩ := get_of_lt_length (X := X) (g := g) (k := k4 + n) (by omega)
    obtain ⟨d, hσ⟩ := state_before F (lt_threads F he) hσ' (Nat.le_succ (k4 + n))
    obtain ⟨hs, hc⟩ := ih (by omega) d (by omega) hσ
    obtain ⟨hs', hx⟩ := elem_step (n := n) (by omega) hs (next_some he hσ hσ')
    refine ⟨?_, hx.trans hc⟩
    rw [hs']
    congr 2
    omega

/-- **An element store is not undefined behaviour because of its value**: a 16-bit payload is
stored as it is. -/
theorem elem_store_ok {d : D} {r : ℕ} {x : ℝ} (hx : d.x r = .float .bf16 x) :
    storeValue 16 (d.x r) = .ok (.float .bf16 x) := by
  rw [hx]
  exact storeValue_bf16 x

/-! ## The content of the output stage, by chunk -/

/-- A byte of the specified content of the output stage, by its token, channel and byte. -/
theorem outStage_eq {s h b off tok β : ℕ} {ch : Fin 128} (h1 : 16 * b + off % 256 / 16 = tok)
    (h2 : (8 * (off / 256) + off % 16 / 2) % 128 = ch.val) (h3 : off % 2 = β) :
    outStage P s h b off = some ((Value.float .bf16 (P.output s h tok ch)).byteAt β) := by
  subst h1 h3
  unfold outStage
  congr 4
  exact Fin.ext h2

/-- Output `e` of chunk `c` of a token: the output of value channel `8 c + e`. -/
def chunkOut (P : Params) (s h tok c e : ℕ) : ℝ :=
  P.output s h tok ⟨(8 * c + e) % 128, Nat.mod_lt _ (by decide)⟩

/-- **The four bytes of element `m` of a chunk** of the specified content of the output stage:
the bytes of the bfloat16 payloads of the outputs `2 m` and `2 m + 1` of the chunk. -/
theorem outStage_chunk (P : Params) (s h t : ℕ) {row c m : ℕ} (hrow : row < 16) (hm : m < 4) :
    ((List.range 4).map fun n => outStage P s h t (16 * row + 256 * c + 4 * m + n)) =
      [some ((Value.float .bf16 (chunkOut P s h (16 * t + row) c (2 * m))).byteAt 0),
        some ((Value.float .bf16 (chunkOut P s h (16 * t + row) c (2 * m))).byteAt 1),
        some ((Value.float .bf16 (chunkOut P s h (16 * t + row) c (2 * m + 1))).byteAt 0),
        some ((Value.float .bf16 (chunkOut P s h (16 * t + row) c (2 * m + 1))).byteAt 1)] := by
  rw [range_map4]
  unfold chunkOut
  rw [outStage_eq (tok := 16 * t + row) (β := 0)
      (ch := ⟨(8 * c + 2 * m) % 128, Nat.mod_lt _ (by decide)⟩) (by omega) (by simp only; omega)
      (by omega),
    outStage_eq (tok := 16 * t + row) (β := 1)
      (ch := ⟨(8 * c + 2 * m) % 128, Nat.mod_lt _ (by decide)⟩) (by omega) (by simp only; omega)
      (by omega),
    outStage_eq (tok := 16 * t + row) (β := 0)
      (ch := ⟨(8 * c + (2 * m + 1)) % 128, Nat.mod_lt _ (by decide)⟩) (by omega)
      (by simp only; omega) (by omega),
    outStage_eq (tok := 16 * t + row) (β := 1)
      (ch := ⟨(8 * c + (2 * m + 1)) % 128, Nat.mod_lt _ (by decide)⟩) (by omega)
      (by simp only; omega) (by omega)]

/-! ## The element stores -/

/-- The blocks of a launch in terms of sequences and heads: block `h * N + s`. -/
theorem blockOf_mod {s h : ℕ} (hs : s < P.sequences) : blockOf P s h % P.sequences = s := by
  unfold blockOf
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem blockOf_div {s h : ℕ} (hs : s < P.sequences) : blockOf P s h / P.sequences = h := by
  unfold blockOf
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]

/-- **The state at an element store, from the vector load of its chunk.** Thread `g` is the
store leader of the block of sequence `s` and head `h`; it was at the vector load before
position `k0` and is followed before position `k0 + 4 + i`, where it has an event; its reads
before that position returned the specified content of the output stage (`hread`, the premise
of `OutContent.elem`). Then it is at the `i`-th element store, the store's source register
holds the bfloat16 payload of output `i` of a chunk `c'` of a token `16 t' + row` of the
sequence, and if its event is a write, it is the two bytes of that output in global memory. -/
theorem chunk_state (F : Followed L mem0 X) (R : StoreRef P L X) (hblock : L.block = 192)
    {s h : ℕ} (hs : s < P.sequences) {k0 i : ℕ} {d0 d : D} {e : Event}
    (hg : storeLeader L (blockOf P s h) = g) (hi : i < 8)
    (hσ0 : stateAt (code L) X g k0 = some (some d0)) (hs0 : d0.site = .load 177)
    (hσ : stateAt (code L) X g (k0 + 4 + i) = some (some d))
    (he : X.get (g, k0 + 4 + i) = some e)
    (hread : ∀ j < k0 + 4 + i, ∀ (pcr : ℕ) (ar : Acc) (br : List (Option Byte)) (b off : ℕ),
      X.get (g, j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P s h) (stageOf b).val off → off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P s h)) ((X.tr g).take j) =
        b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length s) →
        br = (List.range ar.size).map fun n => outStage P s h b (off + n)) :
    ∃ t' row c', 16 * t' + row < P.length s ∧ d.site = .store ⟨10 + i, by omega⟩ ∧
      d.x (elemReg i) = .float .bf16 (chunkOut P s h (16 * t' + row) c' i) ∧
      ∀ pc a bs, e = ⟨pc, .wr a bs⟩ → a.size = 2 ∧
        ∃ v : Fin 128, v.val = 8 * c' + i ∧ a.loc = P.outLoc s h (16 * t' + row) v := by
  have hdiv : g / L.block = blockOf P s h := hg ▸ storeLeader_div hblock
  have hseq : seqOf P L g = s := by rw [seqOf, hdiv, blockOf_mod hs]
  have hhead : headOf P L g = h := by rw [headOf, hdiv, blockOf_div hs]
  obtain ⟨-, t', row, c', hrow, hc', hlive, hreads, hwrites⟩ := R.chunk g k0 d0 hσ0 hs0
  rw [hseq] at hlive
  have hgt := lt_threads F he
  have hlen : k0 + 4 + i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- what each of the four reads returns
  have key : ∀ m < 4, ∀ (e : Event) (am : Acc) (bm : List (Option Byte)) (vm : Value),
      X.get (g, k0 + m) = some e → e.kind = .rd am bm → rebuild 3 bm = .ok vm →
      vm = bf16Pair (chunkOut P s h (16 * t' + row) c' (2 * m))
        (chunkOut P s h (16 * t' + row) c' (2 * m + 1)) := by
    intro m hm e am bm vm he hkind hvm
    obtain ⟨pce, ke⟩ := e
    simp only at hkind
    subst hkind
    obtain ⟨hsz, hloc, hpolls⟩ := hreads m hm pce am bm he
    have hb := hread (k0 + m) (by omega) pce am bm t' (16 * row + 256 * c' + 4 * m) he
      (by rw [hloc, hdiv]; rfl) (by omega)
      (by
        have hp := hpolls
        unfold storeFullBar at hp
        rw [hdiv] at hp
        exact hp)
      (fun n hn => by
        have : (16 * row + 256 * c' + 4 * m + n) % 256 / 16 = row := by omega
        omega)
    rw [hsz, outStage_chunk P s h t' hrow hm] at hb
    rw [hb, rebuild_pair] at hvm
    exact (Except.ok.inj hvm).symm
  -- the four reads
  obtain ⟨e0, he0⟩ := get_of_lt he (show k0 < k0 + 4 + i by omega)
  obtain ⟨e1, he1⟩ := get_of_lt he (show k0 + 1 < k0 + 4 + i by omega)
  obtain ⟨e2, he2⟩ := get_of_lt he (show k0 + 2 < k0 + 4 + i by omega)
  obtain ⟨e3, he3⟩ := get_of_lt he (show k0 + 3 < k0 + 4 + i by omega)
  obtain ⟨d1, hσ1⟩ := state_before F hgt hσ (show k0 + 1 ≤ k0 + 4 + i by omega)
  obtain ⟨d2, hσ2⟩ := state_before F hgt hσ (show k0 + 2 ≤ k0 + 4 + i by omega)
  obtain ⟨d3, hσ3⟩ := state_before F hgt hσ (show k0 + 3 ≤ k0 + 4 + i by omega)
  obtain ⟨d4, hσ4⟩ := state_before F hgt hσ (show k0 + 4 ≤ k0 + 4 + i by omega)
  obtain ⟨a0, b0, v0, hk0, hv0, rfl⟩ := chunk_step0 hs0 (next_some he0 hσ0 hσ1)
  obtain ⟨a1, b1, v1, hk1, hv1, rfl⟩ := chunk_step1 rfl (next_some he1 hσ1 hσ2)
  obtain ⟨a2, b2, v2, hk2, hv2, rfl⟩ := chunk_step2 rfl (next_some he2 hσ2 hσ3)
  obtain ⟨a3, b3, v3, hk3, hv3, hs4, hx4⟩ := chunk_step3 rfl (next_some he3 hσ3 hσ4)
  have h0 := key 0 (by omega) e0 a0 b0 v0 he0 hk0 hv0
  have h1 := key 1 (by omega) e1 a1 b1 v1 he1 hk1 hv1
  have h2 := key 2 (by omega) e2 a2 b2 v2 he2 hk2 hv2
  have h3 := key 3 (by omega) e3 a3 b3 v3 he3 hk3 hv3
  subst h0 h1 h2 h3
  -- the store
  obtain ⟨hsW, hxW⟩ := elem_prefix F hσ4 hs4 i hi d (by omega) hσ
  have hsrc : d.x (elemReg i) =
      .float .bf16 (chunkOut P s h (16 * t' + row) c' i) := by
    rw [hxW, hx4]
    refine (pair_unpacked _ d0.w d0.p d0.x (fun m => chunkOut P s h (16 * t' + row) c' (2 * m))
      (fun m => chunkOut P s h (16 * t' + row) c' (2 * m + 1)) i hi).trans ?_
    congr 1
    split_ifs with hpar
    · congr 1
      omega
    · congr 1
      omega
  refine ⟨t', row, c', hlive, hsW, hsrc, ?_⟩
  rintro pc a bs rfl
  obtain ⟨hsz, v0', hv0', hloc⟩ := hwrites ⟨i, hi⟩ pc a bs he
  rw [hseq, hhead] at hloc
  exact ⟨hsz, v0', hv0', hloc⟩

/-- **The field `elem` of `Protocol.OutContent`**: a write event of the store leader that
covers an output byte carries the byte of the bfloat16 payload of the specified output there,
given that the leader's earlier reads of live rows of the output buffers returned the specified
content of their tiles. -/
theorem out_elem (F : Followed L mem0 X) (R : StoreRef P L X) (hblock : L.block = 192)
    {s h t k i pc : ℕ} {a : Acc} {bs : List Byte} {v : Fin 128} (hs : s < P.sequences)
    (hh : h < P.heads) (_ht : t < P.length s) (hk : k < 2)
    (hw : X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .wr a bs⟩)
    (hc : a.Covers ((P.outLoc s h t v).at k))
    (hread : ∀ j < i, ∀ (pcr : ℕ) (ar : Acc) (br : List (Option Byte)) (b off : ℕ),
      X.get (storeLeader L (blockOf P s h), j) = some ⟨pcr, .rd ar br⟩ →
      ar.loc = outByte L (blockOf P s h) (stageOf b).val off → off + ar.size ≤ 4096 →
      okPolls ((Bar.storeFull (stageOf b)).loc L (blockOf P s h))
        ((X.tr (storeLeader L (blockOf P s h))).take j) = b / 2 + 1 →
      (∀ n < ar.size, 16 * b + (off + n) % 256 / 16 < P.length s) →
        br = (List.range ar.size).map fun n => outStage P s h b (off + n)) :
    wbyte a bs ((P.outLoc s h t v).at k) =
      some ((Value.float .bf16 (P.output s h t v)).byteAt k) := by
  generalize hgg : storeLeader L (blockOf P s h) = g at hw hread
  obtain ⟨k0, d0, ii, rfl, hσ0, hs0⟩ := R.elem g i pc a bs hw (hc.1.symm.trans rfl)
  obtain ⟨dW, hσW⟩ := state_of_wr F hw
  obtain ⟨t', row, c', -, hsW, hsrc, hwr⟩ :=
    chunk_state F R hblock hs hgg ii.isLt hσ0 hs0 hσW hw hread
  obtain ⟨hsz, v0', hv0', hloc⟩ := hwr pc a bs rfl
  obtain ⟨v', hv', rfl⟩ := elem_wr F ii.isLt hw hσW hsW
  rw [elem_store_ok hsrc] at hv'
  cases hv'
  have hout : chunkOut P s h (16 * t' + row) c' ii.val = P.output s h (16 * t' + row) v0' := by
    unfold chunkOut
    congr 1
    exact Fin.ext (by
      have := v0'.isLt
      simp only
      omega)
  obtain ⟨-, -, h3, h4⟩ := hc
  rw [hloc] at h3
  rw [hloc, hsz] at h4
  simp only [Params.outLoc, Loc.at] at h3 h4
  have hv2 := v.isLt
  have hv2' := v0'.isLt
  have hA : (firstToken P.length s + (16 * t' + row)) * P.heads + h =
      (firstToken P.length s + t) * P.heads + h := by omega
  have ht' : 16 * t' + row = t := by
    have := Nat.eq_of_mul_eq_mul_right (show 0 < P.heads by omega) (Nat.add_right_cancel hA)
    omega
  have hvv : v0' = v := Fin.ext (by omega)
  subst ht' hvv
  rw [wbyte, hloc, hout, toBytes_bf16]
  have e4 : ((P.outLoc s h (16 * t' + row) v0').at k).addr -
      (P.outLoc s h (16 * t' + row) v0').addr = k := by
    simp only [Params.outLoc, Loc.at]
    omega
  rw [e4]
  interval_cases k <;> rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
