-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.Lib.SmemElements
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.WFrame
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Lib.StoreForm
import Lemmas.Flow.NotBulkPrefetch
import Lemmas.Flow.NotNc
import Lemmas.Flow.NotTcCp
import Lemmas.Flow.NotTensorPrefetch
import Lemmas.Tensor.BoxWrite
import Lemmas.Tensor.TensorCopy

@[expose] public section

/-! # The shared-memory map

Every access of a consistent execution to shared memory, with its warp and its bytes (offsets from
`sb = L.sharedBase`), as `ShAcc` (`sh_intent`):

| Access | Event | Bytes |
|---|---|---|
| MMA warp, write and read | allocation word | `[sb + 312, sb + 316)` |
| softmax warps, write | statistics store | word `n` of the stage and row, from `sb + 368` |
| correction warps, read | statistics load | the same words |
| softmax warps, read | bias load | the stage's bias buffer, `sb + 166912 + 32768 st` |
| correction warps, write | final O store | a row of the stage's staging, `sb + 3072 + 65536 st` |
| loader, write | row copy of packet `c` | slot `c mod 3` of the K/V ring, from `sb + 68608` |
| warp 14, write | tensor load, site `j` | `[sb + off j, sb + off j + 16384)` (`tload_box`) |
| MMA warp, read | MMA operand byte | the Q stage (A) and the K or V slot (B) |
| output warp, read | tensor store | a staging box of the stage |

with `off j` the decoded site's shared offset (`Loader.inputSite`): the Q stages at 3072, 19456
(stage 0) and 35840, 52224 (stage 1), the Bias stages at 166912, 183296, 199680, 216064. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- A tensor load of a 64-column, 2-byte, 128-byte-swizzled box of 128 rows writes inside the
16384 bytes at its destination. -/
theorem box_lt {s : TensorCopy.Spec} {x y k : Nat} {l : Loc}
    (h0 : TensorTile.count s.descriptor.box 0 = 64) (hR : TensorTile.rows s.descriptor.box = 128)
    (hf : s.descriptor.format.bytes = 2) (hsw : s.descriptor.swizzle = .b128)
    (h : TensorCopy.writeLoc s x y k = some l) :
    s.sharedBase.addr ≤ l.addr ∧ l.addr < s.sharedBase.addr + 16384 := by
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds h
  rw [h0] at hx
  rw [hR] at hy
  rw [hf] at hb
  unfold TensorCopy.writeLoc TensorTransfer.slotAt at h
  rw [dite_eq_left (show x < TensorTile.count s.descriptor.box 0 by omega),
    dite_eq_left (show y < TensorTile.rows s.descriptor.box by omega),
    dite_eq_left (show k < s.descriptor.format.bytes by omega), Option.map_some,
    Option.some.injEq] at h
  subst h
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, h0, hf, hsw, TensorTile.swizzleWidth]
  have hlin : y * max (64 * 2) 128 + x * 2 + k = 128 * y + 2 * x + k := by
    simp only [Nat.reduceMul, max_self]; ring
  rw [hlin]
  have := TensorCopy.box_offset_lt (base := s.sharedBase.addr) (R := 128) hx hy hb
  omega

/-- **A tensor load writes inside the 16384 bytes of its decoded site's shared offset.** -/
theorem tload_box (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩)
    {x y k : Nat} {l : Loc} (hw : TensorCopy.writeLoc s x y k = some l) :
    ∃ j : Fin 14, l.space = .shared ∧ l.cta = i.1 / L.block ∧
      L.sharedBase + (Loader.inputSite j).sharedOffset ≤ l.addr ∧
      l.addr < L.sharedBase + (Loader.inputSite j).sharedOffset + 16384 := by
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  obtain ⟨s0, -⟩ := tload_ge hw
  obtain ⟨h1, h2, h3, h4, -⟩ := input_map p j
  obtain ⟨b1, b2⟩ := box_lt h1 h2 (by simp only [inputSpec, h3]; rfl) h4 hw
  refine ⟨j, s0, ?_, b1, b2⟩
  unfold TensorCopy.writeLoc at hw
  simp only [Option.map_eq_some_iff] at hw
  obtain ⟨_, -, rfl⟩ := hw
  simp only [TensorBox.sharedLoc, inputSpec]

/-- The decoded TMA sites are the Q stages, below the K/V ring, or the Bias stages, above it. -/
theorem tload_off_apart : ∀ j : Fin 14,
    3072 ≤ (Loader.inputSite j).sharedOffset ∧ (Loader.inputSite j).sharedOffset + 16384 ≤ 68608 ∨
    166912 ≤ (Loader.inputSite j).sharedOffset ∧
      (Loader.inputSite j).sharedOffset + 16384 ≤ 232448 := by decide

/-! ### Kinds of accesses the code has not -/

private theorem noNcSites : ∀ pc, Assumptions.all.any (·.ncLoads pc) = false := by
  intro pc; rfl

/-- No uncached load. -/
theorem no_nc (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get i = some ⟨pc, .nc a bs⟩) : False := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  · exact fires_not_nc (noNcSites _) hf rfl

private theorem noPrefetchCode : kernel.code.all (fun i => !bulkPrefetchOp i.op &&
    !tensorPrefetchOp i.op && !tcCpOp i.op) = true := by
  decide +kernel

/-- No atomic read-modify-write. -/
theorem no_rmw (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc : Nat} {a : Acc}
    {o : List (Option Byte)} {n : Option (List Byte)} (he : X.get i = some ⟨pc, .rmw a o n⟩) :
    False :=
  noActualRmw hX ⟨pc, he⟩

theorem no_prefetch (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) : (∀ a, e.kind ≠ .bulkPrefetch a) ∧
      (∀ a s, e.kind ≠ .tensorPrefetch a s) ∧ ∀ s, e.kind ≠ .tc (.cp s) := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · refine ⟨?_, ?_, ?_⟩
    all_goals intros
    all_goals rw [hf]
    all_goals nofun
  · have h := List.all_eq_true.mp noPrefetchCode ins (List.mem_of_getElem? hc)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨fun a hk => ?_, fun a s hk => ?_, fun s hk => ?_⟩
    · rw [fires_bulkPrefetch_op hf hk] at h; simp at h
    · rw [fires_tensorPrefetch_op hf hk] at h; simp at h
    · rw [fires_tcCp_op hf hk] at h; simp at h

/-! ### The map -/

/-- **The accesses of shared memory.** -/
inductive ShAcc (L : Launch) (X : Execution) : Ref → Acc → Bool → Prop
  /-- The write and the reads of the allocation word. -/
  | allocWr {g k a} (hw : Prologue.warpIndex L g = 12) (h : AllocAcc L g a) :
      ShAcc L X (.thread (g, k)) a true
  | allocRd {g k a} (hw : Prologue.warpIndex L g = 12) (h : AllocAcc L g a) :
      ShAcc L X (.thread (g, k)) a false
  /-- A softmax lane's statistics store, a correction lane's statistics load. -/
  | statWr {g k a} (hw : Prologue.warpIndex L g < 8) (h : Softmax.StatAt L g a) :
      ShAcc L X (.thread (g, k)) a true
  | statRd {g k a} (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
      (n st : Fin 2) (h : a.size = 4 ∧ a.loc = ⟨.shared, g / L.block,
        L.sharedBase + 368 + 1024 * n.val + 4 * (128 * st.val + Correction.rowN L g)⟩) :
      ShAcc L X (.thread (g, k)) a false
  /-- A bias load. -/
  | biasRd {g k a} (hw : Prologue.warpIndex L g < 8) (h : Softmax.BiasAt L g a) :
      ShAcc L X (.thread (g, k)) a false
  /-- A final O store. -/
  | fstWr {g k a} (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
      (st : Fin 2) (h : Correction.FstAt L g st a) : ShAcc L X (.thread (g, k)) a true
  /-- A loader lane's row copy. -/
  | rowCp {g k pc sp} (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
      (he : X.get (g, k) = some ⟨pc, .copy sp⟩) (h : LdCp L X g k sp) :
      ShAcc L X (.async (g, k) (.write .copy)) sp.dst true
  /-- A byte of a tensor load. -/
  | tmaWr {g k pc al sp x y z a} (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
      (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) (hz : a.size = 1)
      (hl : TensorCopy.writeLoc sp x y z = some a.loc) (hc : a.loc.cta = g / L.block) (j : Fin 14)
      (hlo : L.sharedBase + (Loader.inputSite j).sharedOffset ≤ a.loc.addr)
      (hhi : a.loc.addr < L.sharedBase + (Loader.inputSite j).sharedOffset + 16384) :
      ShAcc L X (.async (g, k) (.write (.load x y z))) a true
  /-- A byte of an MMA's A operand: of the Q stage. -/
  | mmaA {g k idx a st u j off} (hst : st < 2) (h : Tm.Qk L X g k st u j) (hz : a.size = 1)
      (ho : off < 32768) (hl : a.loc = ⟨.shared, g / L.block,
        L.sharedBase + 3072 + 32768 * st + off⟩) :
      ShAcc L X (.async (g, k) (.mmaRead false idx)) a false
  /-- A byte of an MMA's B operand: of the K slot of ring use `2 u`, or the V slot of `2 u + 1`. -/
  | mmaB {g k idx a st u j off t} (hst : st < 2)
      (h : Tm.Qk L X g k st u j ∧ t = 2 * u ∨ Tm.Pv L X g k st u j ∧ t = 2 * u + 1)
      (hz : a.size = 1) (ho : off < 32768)
      (hl : a.loc = ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (t % 3) + off⟩) :
      ShAcc L X (.async (g, k) (.mmaRead true idx)) a false
  /-- A byte a tensor store reads: of a staging box. -/
  | storeRd {g k pc al sp x y z a} (hw : Prologue.warpIndex L g = 13)
      (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hz : a.size = 1)
      (hl : TensorStore.readLoc sp x y z = some a.loc) (st : Fin 2) (bx : Fin 4)
      (hc : a.loc.cta = g / L.block)
      (hlo : L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val ≤ a.loc.addr)
      (hhi : a.loc.addr < L.sharedBase + 3072 + 65536 * st.val + 16384 * bx.val + 16384) :
      ShAcc L X (.async (g, k) (.read (.store x y z))) a false

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The memory events of the launch, by the warp.** -/
theorem mem_event {e : Event} (he : X.get (g, k) = some e) (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ (InWord p a ∨
        Prologue.warpIndex L g < 8 ∧ Softmax.BiasAt L g a ∨
        (8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11 ∧ ∃ n st : Fin 2, a.size = 4 ∧
          a.loc = ⟨.shared, g / L.block,
            L.sharedBase + 368 + 1024 * n.val + 4 * (128 * st.val + Correction.rowN L g)⟩) ∨
        Prologue.warpIndex L g = 12 ∧ AllocAcc L g a ∨ LocalAt L g a)) ∨
      (∃ a bs, e.kind = .wr a bs ∧ (Prologue.warpIndex L g < 8 ∧ Softmax.StatAt L g a ∨
        (8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11 ∧
          ((∃ st, Correction.FstAt L g st a) ∨ a.loc.space = .global)) ∨
        Prologue.warpIndex L g = 12 ∧ AllocAcc L g a ∨ LocalAt L g a)) ∨
      (∃ sp, e.kind = .copy sp ∧ (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) ∧
        LdCp L X g k sp) ∨
      (∃ a s, e.kind = .tensorIssue a s ∧
        (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)) ∨
      (∃ a s, e.kind = .tensorStore a s ∧ Prologue.warpIndex L g = 13) ∨
      ∃ a s acc ms, e.kind = .tc (.mma a s acc ms) ∧ Prologue.warpIndex L g = 12 := by
  have h16 := Prologue.warpIndex_lt hp g
  by_cases h8 : Prologue.warpIndex L g < 8
  · rcases soft_mem hp hX hFw h8 he hm with ⟨a, bs, hk, h | h⟩ | ⟨a, bs, hk, h⟩
    · exact .inl ⟨a, bs, hk, .inl h⟩
    · exact .inl ⟨a, bs, hk, .inr (.inl ⟨h8, h⟩)⟩
    · exact .inr (.inl ⟨a, bs, hk, .inl ⟨h8, h⟩⟩)
  by_cases h11 : Prologue.warpIndex L g ≤ 11
  · have h8' : 8 ≤ Prologue.warpIndex L g := by omega
    rcases corr_mem hp hX hFw h8' h11 he hm with ⟨a, bs, hk, h | h⟩ | ⟨a, bs, hk, h⟩
    · exact .inl ⟨a, bs, hk, .inl h⟩
    · exact .inl ⟨a, bs, hk, .inr (.inr (.inl ⟨h8', h11, h⟩))⟩
    · exact .inr (.inl ⟨a, bs, hk, .inr (.inl ⟨h8', h11, h⟩)⟩)
  by_cases h12 : Prologue.warpIndex L g = 12
  · rcases mma_mem hp hX hFw h12 he hm with ⟨a, bs, hk, h | h⟩ | ⟨a, bs, hk, h⟩ |
      ⟨a, s, acc, ms, hk⟩
    · exact .inl ⟨a, bs, hk, .inl h⟩
    · exact .inl ⟨a, bs, hk, .inr (.inr (.inr (.inl ⟨h12, h⟩)))⟩
    · exact .inr (.inl ⟨a, bs, hk, .inr (.inr (.inl ⟨h12, h⟩))⟩)
    · exact .inr (.inr (.inr (.inr (.inr ⟨a, s, acc, ms, hk, h12⟩))))
  by_cases h13 : Prologue.warpIndex L g = 13
  · rcases epi_mem hp hX hFw h13 he hm with ⟨a, bs, hk, h⟩ | ⟨a, s, hk⟩
    · exact .inl ⟨a, bs, hk, .inl h⟩
    · exact .inr (.inr (.inr (.inr (.inl ⟨a, s, hk, h13⟩))))
  have h14 : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15 := by omega
  rcases ld_mem hp hX hFw h14 he hm with ⟨a, bs, hk, h | h⟩ | ⟨a, bs, hk, h⟩ | ⟨sp, hk, h⟩ |
    ⟨a, s, hk⟩
  · exact .inl ⟨a, bs, hk, .inl h⟩
  · exact .inl ⟨a, bs, hk, .inr (.inr (.inr (.inr h)))⟩
  · exact .inr (.inl ⟨a, bs, hk, .inr (.inr (.inr h))⟩)
  · exact .inr (.inr (.inl ⟨sp, hk, h14, h⟩))
  · exact .inr (.inr (.inr (.inl ⟨a, s, hk, h14⟩)))

/-- An index with an operand byte is below the operand's 4096. -/
theorem mma_index {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) {op : TcMma.Operand} {idx : Nat} {l : Loc}
    (hb : s.byteLoc op idx = some l) : idx < 4096 := by
  obtain ⟨-, st, u, j, -, h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
  have hD : s.descriptor = Tm.qkDsc ∨ s.descriptor = Tm.pvDsc := by
    rcases h with h | h
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi; exact .inl rfl
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi; exact .inr rfl
  by_contra hn
  have hrow : ∀ D, (D = Tm.qkDsc ∨ D = Tm.pvDsc) → ¬ (TcMma.Valid D ∧
      idx / (D.kind.k * D.kind.width) < if op = .a ∧ D.ws = true ∧ D.m < 128 then 128
        else op.extent D) := by
    rintro D hD ⟨-, h⟩
    have h32 : D.kind.k * D.kind.width = 32 := by rcases hD with rfl | rfl <;> rfl
    have hext : (if op = .a ∧ D.ws = true ∧ D.m < 128 then 128 else op.extent D) = 128 := by
      rcases hD with rfl | rfl <;> cases op <;> rfl
    rw [h32, hext] at h
    omega
  unfold TcMma.OperandSpec.byteLoc at hb
  simp only [bind, Option.bind] at hb
  rw [ite_eq_left_of_eq_true _ _ (eq_true (hrow _ hD))] at hb
  cases hb

/-- **Every access of shared memory is in the map.** -/
theorem sh_intent {r : Ref} {a : Acc} {w : Bool} (hi : X.Intent r a w)
    (hs : a.loc.space = .shared) : ShAcc L X r a w := by
  rcases r with ⟨g, k⟩ | ⟨⟨g, k⟩, part⟩
  · rcases hi with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
    · rcases mem_event hp hX hFw he trivial with ⟨a', bs', hk, h⟩ | ⟨_, _, hk, -⟩ | ⟨_, hk, -⟩ |
        ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      rcases h with ⟨-, h⟩ | ⟨h8, h⟩ | ⟨h8, h11, n, st, h⟩ | ⟨h12, h⟩ | ⟨o, h, -⟩
      · exfalso
        rcases h with ⟨i, -, h⟩ | ⟨i, -, h⟩ | ⟨i, -, q, -, h⟩ <;> rw [h] at hs <;> cases hs
      · exact .biasRd h8 h
      · exact .statRd h8 h11 n st h
      · exact .allocRd h12 h
      · rw [h] at hs; cases hs
    · rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨a', bs', hk, h⟩ | ⟨_, hk, -⟩ |
        ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      rcases h with ⟨h8, h⟩ | ⟨h8, h11, ⟨st, h⟩ | h⟩ | ⟨h12, h⟩ | ⟨o, h, -⟩
      · exact .statWr h8 h
      · exact .fstWr h8 h11 st h
      · rw [h] at hs; cases hs
      · exact .allocWr h12 h
      · rw [h] at hs; cases hs
    · exact (noActualRmw hX ⟨pc, he⟩).elim
  · obtain ⟨rfl, hfp⟩ := hi
    cases part
    case async.mmaRead isB idx =>
      obtain ⟨hz, ⟨d, s, acc, mask, hi, hb⟩ | ⟨c, _, _, ⟨pc, he⟩, -⟩⟩ := hfp
      swap
      · exact ((no_prefetch hX he).2.2 c rfl).elim
      have hidx := mma_index hp hX hFw hi hb
      obtain ⟨-, st, u, j, hst, h⟩ := Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
      rcases h with h | h
      · obtain ⟨⟨o1, h1, e1⟩, o2, h2, e2⟩ := h.bytes hp hi hidx
        cases isB with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hb
          rw [e1] at hb
          exact .mmaA hst h hz h1 (Option.some.inj hb).symm
        | true =>
          simp only [↓reduceIte] at hb
          rw [e2] at hb
          exact .mmaB hst (.inl ⟨h, rfl⟩) hz h2 (Option.some.inj hb).symm
      · obtain ⟨e1, o2, h2, e2⟩ := h.bytes hp hi hidx
        cases isB with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hb
          rw [e1] at hb
          cases hb
        | true =>
          simp only [↓reduceIte] at hb
          rw [e2] at hb
          exact .mmaB hst (.inr ⟨h, rfl⟩) hz h2 (Option.some.inj hb).symm
    case async.readCopy =>
      rcases hfp with ⟨sp, ⟨pc, he⟩, rfl⟩ | ⟨pc, he⟩
      · rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
          ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
        rw [h.src] at hs
        cases hs
      · exact ((no_prefetch hX he).1 a rfl).elim
    case async.writeCopy =>
      obtain ⟨sp, ⟨pc, he⟩, -, rfl⟩ := hfp
      rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      exact .rowCp hw he h
    case async.writeElem j =>
      obtain ⟨sp, ⟨pc, he⟩, hj⟩ := hfp
      rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, h.whole] at hj
    case async.oldElem j =>
      obtain ⟨sp, r, ⟨pc, he⟩, hr, -⟩ := hfp
      rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      rw [h.whole] at hr
      cases hr
    case async.readLoad x y z =>
      obtain ⟨sp, al, -, hl, -⟩ := hfp
      rw [TensorCopy.readLoc_source] at hl
      simp only [Option.bind_eq_some_iff] at hl
      obtain ⟨_, -, hl⟩ := hl
      split at hl
      · rw [← Option.some.inj hl] at hs
        cases hs
      · cases hl
    case async.writeLoad x y z =>
      obtain ⟨sp, al, ⟨pc, he⟩, hl, hz⟩ := hfp
      rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      obtain ⟨j, h1, h2, h3, h4⟩ := tload_box hp hX hFw he hl
      exact .tmaWr hw he hz hl h2 j h3 h4
    case async.readStore x y z =>
      obtain ⟨sp, al, ⟨pc, he⟩, hl, hz⟩ := hfp
      rcases mem_event hp hX hFw he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, hk, hw⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
      obtain ⟨st, bx, h⟩ := storeRead_box hp hX hw ⟨pc, he⟩
      obtain ⟨-, h2, h3, h4⟩ := h x y z _ hl
      exact .storeRd hw he hz hl st bx h2 h3 h4
    case async.writeStore x y z =>
      obtain ⟨sp, al, -, hl, -⟩ := hfp
      rw [tstore_global hl] at hs
      cases hs
    case async.oldStore x y z =>
      obtain ⟨sp, al, hi, hr, -⟩ := hfp
      rw [(actualTensorStoreForm hX hi).2.2] at hr
      cases hr
    case async.writeCta =>
      obtain ⟨_, _, hi, -⟩ := hfp
      exact (noClcIssue hX hi).elim
    case async.readPrefetch =>
      obtain ⟨_, _, ⟨pc, he⟩, -⟩ := hfp
      exact ((no_prefetch hX he).2.1 _ _ rfl).elim
    all_goals exact hfp.elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
