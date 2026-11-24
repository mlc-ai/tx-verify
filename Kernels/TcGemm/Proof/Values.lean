-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Mbar
public import Kernels.TcGemm.Proof.Protocol.Intents
public import Lemmas.Async.ReadSources
public import Lemmas.Async.AsyncExecution
public import Lemmas.Tcgen05.TcCommit

@[expose] public section

/-! # `tc_gemm`: the values of the copies, the MMA and the loads

The copies read the launch content of `A` and `B`, which no write covers, and write it to `sA` and
`sB` (`copyA_write_byte`, `copyB_write_byte`). Thread 0's successful poll of `bar0` observes both
copies (`wait_observes_copies`) and happens before the MMA's issue, so the MMA's operand bytes are
the inputs' bytes (`mma_operands`) and its result at row `i`, column `j` is `D[i][j]`
(`mma_result`, `result_value`). A thread's load follows its successful poll of `bar1`, which
observes the MMA's completion (`wait_observes_mma`); the deallocation follows every access
(`dealloc_done`, through the second barrier). So word `j` of thread `g`'s load reads lane `g`,
column `col + j`, written by the MMA (`ld_source`): `D[g][j]` (`ld_vals`). No thread has undefined
behaviour (`u_nil`). -/

namespace PTX.Kernels.TcGemm.Proof
open TcMma (byteInt s32)
open PTX PTX.Proof PTX.Flow AsyncCopy Tmem.Pair
noncomputable section

/-- An `.i8` operand element is the byte at `row * 32 + k`. -/
private theorem elementBytes_i8 (sa sb sat : Bool) (bs : List (Option Byte)) (row k : Nat) :
    (TcMma.elementBytes (.i8 sa sb sat) bs row k).headD none = bs.getD (row * 32 + k) none := by
  simp [TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, List.getD_eq_getElem?_getD,
    List.head?_take]


variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

/-- `mapM` of a function that always succeeds. -/
theorem mapM_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (by simp), mapM_some f g l (fun y hy => h y (by simp [hy]))]
    rfl

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

theorem copyA_source_byte {bs : List Byte}
    (hr : X.MemReads (.async (0, 6) (.read .copy)) { loc := gA A, size := 4096 } (bs.map some))
    {k : Nat} (hk : k < 4096) {byte : Byte}
    (hm : mem0 ((gA A).at k) = some (some byte)) : bs[k]? = some byte := by
  have hh := read_initial_of_no_writer hX hr hk hm
    (fun _ _ _ hw => no_write_inputA hpre hW hw hk)
  simp only [List.getElem?_map] at hh
  cases hb : bs[k]? with
  | none => simp [hb] at hh
  | some b => simpa [hb] using hh

theorem copyB_source_byte {bs : List Byte}
    (hr : X.MemReads (.async (0, 7) (.read .copy)) { loc := gB B, size := 256 } (bs.map some))
    {k : Nat} (hk : k < 256) {byte : Byte}
    (hm : mem0 ((gB B).at k) = some (some byte)) : bs[k]? = some byte := by
  have hh := read_initial_of_no_writer hX hr hk hm
    (fun _ _ _ hw => no_write_inputB hpre hW hw hk)
  simp only [List.getElem?_map] at hh
  cases hb : bs[k]? with
  | none => simp [hb] at hh
  | some b => simpa [hb] using hh

theorem copyA_write_byte {bs : List Byte}
    (hw : X.MemWrites (.async (0, 6) (.write .copy)) { loc := sA L.sharedBase, size := 4096 } bs)
    {k : Nat} (hk : k < 4096) {byte : Byte}
    (hm : mem0 ((gA A).at k) = some (some byte)) : bs[k]? = some byte := by
  obtain ⟨s, hb, hr, _⟩ := hX.copy_write_read hw (hW.copy_form _)
  obtain ⟨pc, hi⟩ := hb
  rcases (hW.bulk hi).2.2.2 with ⟨_, rfl⟩ | ⟨hn, _⟩
  · exact copyA_source_byte hpre hX hW hr hk hm
  · cases hn

theorem copyB_write_byte {bs : List Byte}
    (hw : X.MemWrites (.async (0, 7) (.write .copy)) { loc := sB L.sharedBase, size := 256 } bs)
    {k : Nat} (hk : k < 256) {byte : Byte}
    (hm : mem0 ((gB B).at k) = some (some byte)) : bs[k]? = some byte := by
  obtain ⟨s, hb, hr, _⟩ := hX.copy_write_read hw (hW.copy_form _)
  obtain ⟨pc, hi⟩ := hb
  rcases (hW.bulk hi).2.2.2 with ⟨hn, _⟩ | ⟨_, rfl⟩
  · cases hn
  · exact copyB_source_byte hpre hX hW hr hk hm

/-- A consumer with a proven visibility edge to the real A copy reads that input byte.
The consumer can be an ordinary load or an independent MMA operand read. -/
theorem read_copyA_byte {e : Ref} {src : Acc} {bs : List (Option Byte)}
    (hr : X.MemReads e src bs) {j k : Nat} (hj : j < src.size) (hk : k < 4096)
    (hl : src.loc.at j = (sA L.sharedBase).at k) {raw : List Byte}
    (hw : X.MemWrites (.async (0, 6) (.write .copy)) { loc := sA L.sharedBase, size := 4096 } raw)
    (hv : modelCausality L X (src.loc.at j) (.async (0, 6) (.write .copy)) e) {byte : Byte}
    (hm : mem0 ((gA A).at k) = some (some byte)) : bs[j]? = some (some byte) := by
  have hc : ({ loc := sA L.sharedBase, size := 4096 } : Acc).Covers (src.loc.at j) := by
    rw [hl]; exact Acc.covers_at hk
  have hh := read_byte_of_unique_writer hX hr hj hw hc hv (fun w dst bytes hw' hc' =>
    (hW.copyA_writer hw' hk (by rwa [hl] at hc')).1)
  rw [hh, hl]
  simp only [wbyte, Loc.at, Nat.add_sub_cancel_left]
  exact congrArg some (copyA_write_byte hpre hX hW hw hk hm)

theorem read_copyB_byte {e : Ref} {src : Acc} {bs : List (Option Byte)}
    (hr : X.MemReads e src bs) {j k : Nat} (hj : j < src.size) (hk : k < 256)
    (hl : src.loc.at j = (sB L.sharedBase).at k) {raw : List Byte}
    (hw : X.MemWrites (.async (0, 7) (.write .copy)) { loc := sB L.sharedBase, size := 256 } raw)
    (hv : modelCausality L X (src.loc.at j) (.async (0, 7) (.write .copy)) e) {byte : Byte}
    (hm : mem0 ((gB B).at k) = some (some byte)) : bs[j]? = some (some byte) := by
  have hc : ({ loc := sB L.sharedBase, size := 256 } : Acc).Covers (src.loc.at j) := by
    rw [hl]; exact Acc.covers_at hk
  have hh := read_byte_of_unique_writer hX hr hj hw hc hv (fun w dst bytes hw' hc' =>
    (hW.copyB_writer hw' hk (by rwa [hl] at hc')).1)
  rw [hh, hl]
  simp only [wbyte, Loc.at, Nat.add_sub_cancel_left]
  exact congrArg some (copyB_write_byte hpre hX hW hw hk hm)

omit hpre hX in
/-- The kernel's MMA issue, at its trace position. -/
theorem kernel_mma_issue (hm : hd 0 + 2 + (P 0).n0 < m 0) :
    X.MmaIssue (0, hd 0 + 2 + (P 0).n0) (P 0).c (mmaSpec L.sharedBase) false mmaMask :=
  ⟨Flow.mma_0, by rw [hW.get_of_lt (by decide) hm, fullAt_mma]; rfl⟩

omit hpre in
/-- Recorded operands have the full 128 x 32 and 8 x 32 byte arrays. -/
theorem mma_lengths {mma : EvId} {ab bb : List (Option Byte)}
    (hop : X.async.mmaOperands mma = some ⟨ab, bb⟩) : ab.length = 4096 ∧ bb.length = 256 := by
  have hs : X.async.mmaStarted mma = true := by simp [Snapshot.mmaStarted, hop]
  rcases hX.tma.2.1.1 mma hs with ⟨d, s, accum, mask, ops, hi, hop', _, ha, hb⟩ |
    ⟨_, _, ⟨pc, hc⟩, -⟩ | ⟨_, _, ⟨pc, hc⟩, -⟩
  rotate_left
  · obtain ⟨g, j⟩ := mma; exact (hW.no_cp hc).elim
  · obtain ⟨g, j⟩ := mma; exact (hW.no_shift hc).elim
  obtain ⟨-, -, rfl, -, -⟩ := hW.mmaIssue hi
  rw [hop] at hop'
  cases hop'
  exact ⟨by simpa [mmaSpec, mmaDesc, TcMma.Operand.bytes, TcMma.Operand.rows,
      TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width] using ha,
    by simpa [mmaSpec, mmaDesc, TcMma.Operand.bytes, TcMma.Operand.rows,
      TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width] using hb⟩

omit hpre hX hW in
private theorem getD_some {l : List (Option Byte)} {n : Nat} (h : n < l.length) :
    l[n]? = some (l.getD n none) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem mma_a_byte_of_observed {ab bb : List (Option Byte)} {mma waiter : EvId}
    (hissue : X.MmaIssue mma (P 0).c (mmaSpec L.sharedBase) false mmaMask)
    (hop : X.async.mmaOperands mma = some ⟨ab, bb⟩)
    {ws : MbarScope} (ho : AsyncObserved X (0, 6) (.notify .copy) waiter true ws)
      (hb : baseCausality L X waiter mma)
    {i k : Nat} (hi : i < 128) (hk : k < 32) {byte : Byte}
    (hmem : mem0 ⟨.global, 0, A + offA i k⟩ = some (some byte)) :
    ab.getD (i * 32 + k) none = some byte := by
  let l := (sA L.sharedBase).at (offA i k)
  have hdiv : (i * 32 + k) / 32 = i := by omega
  have hmod : (i * 32 + k) % 32 = k := by omega
  have hfoot : (mmaSpec L.sharedBase).byteLoc .a (i * 32 + k) = some l := by
    rw [mmaSpec_a, ite_eq_left (by omega), hdiv, hmod]
  have hr : X.MemReads (.async mma (.mmaRead false (i * 32 + k))) { loc := l, size := 1 }
      [ab.getD (i * 32 + k) none] :=
    ⟨_, ⟨.inl ⟨_, _, _, _, hissue, hfoot⟩, ⟨ab, bb⟩, hop,
      getD_some
        (by have := (mma_lengths hX hW hop).1; simp only [Bool.false_eq_true, ↓reduceIte]; omega)⟩,
        rfl, rfl⟩
  have hmt : mma.1 < L.threads := by
    by_contra h
    have := (baseCausality_events hb).2
    rw [hX.outside _ (by omega)] at this
    simp at this
  have hsc : ∀ g < L.block, SameCta L g mma.1 := fun g hg =>
    ⟨by simp [Launch.threads, hpre.grid]; omega, hmt, by
      simp only [Launch.threads, hpre.grid] at hmt ⊢
      rw [Nat.div_eq_of_lt hg, Nat.div_eq_of_lt (by omega)]⟩
  have hwt : waiter.1 < L.threads := by
    by_contra h
    have := (baseCausality_events hb).1
    rw [hX.outside _ (by omega)] at this
    simp at this
  have hsw : SameCta L 0 waiter.1 :=
    ⟨by simp only [Launch.threads, hpre.grid] at hwt ⊢; omega, hwt, by
      simp only [Launch.threads, hpre.grid] at hwt ⊢
      rw [Nat.zero_div, Nat.div_eq_of_lt (by omega)]⟩
  obtain ⟨s, raw, hbulk, _, hw, _⟩ := hX.copy_effects ho (hW.copy_form _)
  obtain ⟨pc, he⟩ := hbulk
  obtain ⟨_, _, hg, hcases⟩ := hW.bulk he
  rcases hcases with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
  · have hl : l.at 0 = (sA L.sharedBase).at (offA i k) := by simp [l, Loc.at]
    have hq : offA i k < 4096 := by unfold offA; omega
    have hcov : ({ loc := sA L.sharedBase, size := 4096 } : Acc).Covers (l.at 0) := by
      rw [hl]; exact Acc.covers_at hq
    have hv : modelCausality L X (l.at 0) (.async (0, 6) (.write .copy))
        (.async mma (.mmaRead false (i * 32 + k))) :=
      ⟨.inl (hsc _ (by rw [hpre.block]; decide)),
        .direct ⟨⟨_, true, ⟨rfl, _, ⟨pc, he⟩, rfl, rfl⟩, hcov⟩,
        ⟨{ loc := l, size := 1 }, false, hr.intent, Acc.covers_at (show 0 < 1 from Nat.zero_lt_succ
          0)⟩,
        .inl ⟨waiter, .inr ⟨ws, by obtain ⟨n, mb, hn, hwo⟩ := ho; exact ⟨n, mb, .inl hn, hwo⟩,
          .of_sameCta hsw⟩, hb⟩⟩⟩
    have hbyte := read_copyA_byte hpre hX hW hr (j := 0) (show 0 < 1 from Nat.zero_lt_succ 0) hq hl
      hw hv
      (by simpa [gA, Loc.at] using hmem)
    exact Option.some.inj hbyte
  · cases hj

theorem mma_b_byte_of_observed {ab bb : List (Option Byte)} {mma waiter : EvId}
    (hissue : X.MmaIssue mma (P 0).c (mmaSpec L.sharedBase) false mmaMask)
    (hop : X.async.mmaOperands mma = some ⟨ab, bb⟩)
    {ws : MbarScope} (ho : AsyncObserved X (0, 7) (.notify .copy) waiter true ws)
      (hb : baseCausality L X waiter mma)
    {i k : Nat} (hi : i < 8) (hk : k < 32) {byte : Byte}
    (hmem : mem0 ⟨.global, 0, B + offB k i⟩ = some (some byte)) :
    bb.getD (i * 32 + k) none = some byte := by
  let l := (sB L.sharedBase).at (offB k i)
  have hdiv : (i * 32 + k) / 32 = i := by omega
  have hmod : (i * 32 + k) % 32 = k := by omega
  have hfoot : (mmaSpec L.sharedBase).byteLoc .b (i * 32 + k) = some l := by
    rw [mmaSpec_b, ite_eq_left (by omega), hdiv, hmod]
  have hr : X.MemReads (.async mma (.mmaRead true (i * 32 + k))) { loc := l, size := 1 }
      [bb.getD (i * 32 + k) none] :=
    ⟨_, ⟨.inl ⟨_, _, _, _, hissue, hfoot⟩, ⟨ab, bb⟩, hop,
      getD_some (by have := (mma_lengths hX hW hop).2; simp only [↓reduceIte]; omega)⟩, rfl, rfl⟩
  have hmt : mma.1 < L.threads := by
    by_contra h
    have := (baseCausality_events hb).2
    rw [hX.outside _ (by omega)] at this
    simp at this
  have hsc : ∀ g < L.block, SameCta L g mma.1 := fun g hg =>
    ⟨by simp [Launch.threads, hpre.grid]; omega, hmt, by
      simp only [Launch.threads, hpre.grid] at hmt ⊢
      rw [Nat.div_eq_of_lt hg, Nat.div_eq_of_lt (by omega)]⟩
  have hwt : waiter.1 < L.threads := by
    by_contra h
    have := (baseCausality_events hb).1
    rw [hX.outside _ (by omega)] at this
    simp at this
  have hsw : SameCta L 0 waiter.1 :=
    ⟨by simp only [Launch.threads, hpre.grid] at hwt ⊢; omega, hwt, by
      simp only [Launch.threads, hpre.grid] at hwt ⊢
      rw [Nat.zero_div, Nat.div_eq_of_lt (by omega)]⟩
  obtain ⟨s, raw, hbulk, _, hw, _⟩ := hX.copy_effects ho (hW.copy_form _)
  obtain ⟨pc, he⟩ := hbulk
  obtain ⟨_, _, hg, hcases⟩ := hW.bulk he
  rcases hcases with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
  · cases hj
  · have hl : l.at 0 = (sB L.sharedBase).at (offB k i) := by simp [l, Loc.at]
    have hq : offB k i < 256 := by unfold offB; omega
    have hcov : ({ loc := sB L.sharedBase, size := 256 } : Acc).Covers (l.at 0) := by
      rw [hl]; exact Acc.covers_at hq
    have hv : modelCausality L X (l.at 0) (.async (0, 7) (.write .copy))
        (.async mma (.mmaRead true (i * 32 + k))) :=
      ⟨.inl (hsc _ (by rw [hpre.block]; decide)),
        .direct ⟨⟨_, true, ⟨rfl, _, ⟨pc, he⟩, rfl, rfl⟩, hcov⟩,
        ⟨{ loc := l, size := 1 }, false, hr.intent, Acc.covers_at (show 0 < 1 from Nat.zero_lt_succ
          0)⟩,
        .inl ⟨waiter, .inr ⟨ws, by obtain ⟨n, mb, hn, hwo⟩ := ho; exact ⟨n, mb, .inl hn, hwo⟩,
          .of_sameCta hsw⟩, hb⟩⟩⟩
    have hbyte := read_copyB_byte hpre hX hW hr (j := 0) (show 0 < 1 from Nat.zero_lt_succ 0) hq hl
      hw hv
      (by simpa [gB, Loc.at] using hmem)
    exact Option.some.inj hbyte

/-- For an MMA whose operand reads have actually begun, this kernel's preceding
successful wait supplies both completion observations. No protocol premise is added
to Pre and no source-order shortcut is used for the copies' writes. -/
theorem mma_operands (hm : hd 0 + 2 + (P 0).n0 < m 0)
    (hstart : X.async.mmaStarted (0, hd 0 + 2 + (P 0).n0) = true) :
    ∃ ab bb, X.async.mmaOperands (0, hd 0 + 2 + (P 0).n0) = some ⟨ab, bb⟩ ∧
    (∀ i < 128, ∀ k < 32, byteInt true (ab.getD (i * 32 + k) none) = some (a i k)) ∧
    (∀ j < 8, ∀ k < 32, byteInt true (bb.getD (j * 32 + k) none) = some (b k j)) := by
  obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands (0, hd 0 + 2 + (P 0).n0) = some values := by
    cases hh : X.async.mmaOperands (0, hd 0 + 2 + (P 0).n0) with
    | none => simp [Snapshot.mmaStarted, hh] at hstart
    | some values => exact ⟨values, rfl⟩
  obtain ⟨ab, bb⟩ := values
  have hissue := kernel_mma_issue hW hm
  have hget : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
  obtain ⟨hoA, hoB⟩ := wait_observes_copies hX hW hget
  have hscope : SameCta L 0 0 := by
    have ht := threads_eq hpre
    exact ⟨by omega, by omega, rfl⟩
  have hord : baseCausality L X (0, hd 0 + 1 + (P 0).n0) (0, hd 0 + 2 + (P 0).n0) :=
    po_baseCausality (by omega) (len_of_get hissue.choose_spec) (by rw [hget]; rfl)
  refine ⟨ab, bb, hv, fun i hi k hk => ?_, fun j hj k hk => ?_⟩
  · obtain ⟨byte, hmem, hval⟩ := hpre.inputA i hi k hk
    rw [mma_a_byte_of_observed hpre hX hW hissue hv hoA hord hi hk hmem]
    exact hval
  · obtain ⟨byte, hmem, hval⟩ := hpre.inputB k hk j hj
    rw [mma_b_byte_of_observed hpre hX hW hissue hv hoB hord hj hk hmem]
    exact hval

/-- A successful poll of `bar1` follows thread 0's commit. -/
theorem commit_exists {w : EvId} {pc : Nat} {acq : Bool} {ws : MbarScope}
    (hw : X.get w = some ⟨pc, .wait (bar1 L.sharedBase) 0 true acq ws⟩) :
    hd 0 + 3 + (P 0).n0 < m 0 := by
  obtain ⟨commit, _, _, _, _, ⟨pc', hc⟩, _, _, _⟩ := (wait_observes_mma hpre hX hW hw).mma
  obtain ⟨g, j⟩ := commit
  obtain ⟨_, hj, rfl, rfl, _⟩ := hW.commit hc
  exact hj

/-- A load follows the thread's successful MMA wait, so thread 0 has issued its commit. -/
theorem load_after_commit {e : EvId} {ta : Nat} {vals : List Value} {sh : TcShape}
    (hl : X.TLd e ta vals sh) :
    hd 0 + 3 + (P 0).n0 < m 0 := by
  obtain ⟨pc, hp⟩ := hl
  obtain rfl := hW.tld_shape hp
  obtain ⟨g, j⟩ := e
  obtain ⟨hg, hj, rfl, -⟩ := hW.tld hp
  have hld := ldIdx_eq (g := g) (P g)
  have hw1 : X.get (g, tl g (P g) + (P g).n1) = some (wait1E L.sharedBase true) := by
    rw [hW.get_of_lt hg (by omega), fullAt_w1t]
  exact commit_exists hpre hX hW hw1

/-- This kernel releases its only allocation after every access has completed. -/
theorem dealloc_done :
    ∀ d pc grp dst t n e cell, X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc t n))⟩ →
      Access L X e cell → TcMma.CompletedBefore L X e d := by
  have hT := threads_eq hpre
  have hB := hpre.block
  rintro ⟨g, i⟩ pc grp dst t n e cell hd' hacc
  rcases hW.resource hd' with ⟨_, _, _, _, h⟩ | ⟨_, _, rfl, rfl, -⟩
  · cases h
  obtain ⟨hg, hi, hg32, rfl, rfl, rfl⟩ := hW.tdealloc hd'
  have hdone : ∀ h, h < 128 → ldIdx h (P h) + 11 < m h :=
    fun h hh => bar1_all hpre hX hW hg (by omega) hh
  have hlen := hW.length g hg
  have hbf : ∀ h i, h < 128 → i < ldIdx h (P h) + 11 →
      baseCausality L X (h, i) (g, ldIdx g (P g) + 13) :=
    fun h i hh hi => by
      have := ldIdx_eq (g := g) (P g); have := tl_ge (g := g) (P g)
      exact sync1 hpre hX hW hh hg hi (hdone h hh) (by omega) (by omega)
  rcases hacc with hm | ⟨jj, ta, vs, sh, ⟨pc', htl⟩, -⟩ | ⟨_, _, _, _, ⟨_, hst⟩, -⟩ |
    ⟨_, _, _, _, ⟨_, hcp⟩, -⟩ | ⟨_, ⟨_, hsh⟩, -⟩ | ⟨_, ⟨_, hsh⟩, -⟩
  · obtain ⟨rfl, -, -⟩ := mma_access hW hm
    have hld := ldIdx_eq (g := 0) (P 0)
    have htl := tl_zero (P 0)
    have h0d := hdone 0 (by decide)
    have hw : X.get (0, tl 0 (P 0) + (P 0).n1) = some (wait1E L.sharedBase true) := by
      rw [hW.get_of_lt (by decide) (by omega), fullAt_w1t]
    have ho := wait_observes_mma hpre hX hW hw
    set ws : MbarScope := .cta
    have h0 : 0 < L.threads := by have := threads_eq hpre; omega
    have hsc : ScopesMeet L .cluster 0 ws 0 :=
      ⟨⟨h0, h0, rfl⟩, by cases ws <;> first | exact ⟨h0, h0, rfl⟩ | exact ⟨h0, h0⟩⟩
    refine ⟨fun ⟨_, _, _, pc'', hl⟩ => ?_, fun ⟨_, _, _, _, hs⟩ => (hW.no_tst hs).elim, fun _ =>
      .inl ⟨(0, tl 0 (P 0) + (P 0).n1), ws, ho, hsc, hbf 0 _ (by decide) (by omega)⟩⟩
    obtain rfl := hW.tld_shape hl
    obtain ⟨_, _, hj', _⟩ := hW.tld hl
    omega
  · obtain ⟨h, j⟩ := e
    obtain rfl := hW.tld_shape htl
    obtain ⟨hh, hj, rfl, rfl, rfl⟩ := hW.tld htl
    have := hdone h hh
    have := ldIdx_eq (g := h) (P h); have := tl_ge (g := h) (P h)
    refine ⟨fun _ => ⟨(h, ldIdx h (P h) + 1), ⟨Flow.tmemWait_0, ?_⟩, rfl, by simp,
      .inl (hbf h _ hh (by simp))⟩, fun ⟨_, _, _, _, hs⟩ => (hW.no_tst hs).elim,
      fun hta => ?_⟩
    · rw [hW.get_of_lt hh (by omega), show ldIdx h (P h) + 1 = ldIdx h (P h) + 1 + 0 from rfl,
        fullAt_post]; rfl
    · rcases hta with ⟨_, _, _, _, pc'', hm⟩ | ⟨_, pc'', hm⟩ | ⟨_, pc'', hm⟩
      · obtain ⟨-, -, rfl, hj', -⟩ := hW.mma hm
        have := tl_zero (P 0)
        omega
      · exact (hW.no_cp hm).elim
      · exact (hW.no_shift hm).elim
  · exact (hW.no_tst hst).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_cp hcp).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_shift hsh).elim
  · obtain ⟨_, _⟩ := e; exact (hW.no_shift hsh).elim


/-- A load follows thread 0's operand and MMA waits: both copies have been notified and
the MMA has completed. -/
theorem load_completions {e : EvId} {ta : Nat} {vals : List Value} {sh : TcShape}
    (hl : X.TLd e ta vals sh) :
    (X.async.copies (0, 6)).notified = true ∧ (X.async.copies (0, 7)).notified = true ∧
      X.async.mmaDone (0, hd 0 + 2 + (P 0).n0) = true := by
  have hc := load_after_commit hpre hX hW hl
  have htl := tl_zero (P 0)
  have hw0 : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
  obtain ⟨hA, hB⟩ := wait_observes_copies hX hW hw0
  obtain ⟨_, _, ⟨_, _, hnA, _⟩, _⟩ := hA.copy
  obtain ⟨_, _, ⟨_, _, hnB, _⟩, _⟩ := hB.copy
  obtain ⟨pc, hp⟩ := hl
  obtain rfl := hW.tld_shape hp
  obtain ⟨g, j⟩ := e
  obtain ⟨hg, hj, rfl, -⟩ := hW.tld hp
  have hld := ldIdx_eq (g := g) (P g)
  have hw1 : X.get (g, tl g (P g) + (P g).n1) = some (wait1E L.sharedBase true) := by
    rw [hW.get_of_lt hg (by omega), fullAt_w1t]
  exact ⟨hnA, hnB, commit_observed_done hX.tcCommit (wait_observes_mma hpre hX hW hw1)⟩

/-- Once its operand reads have occurred, the kernel MMA derives `D[i][j]` exactly for every
cell of its tile. -/
theorem mma_result (hmm : hd 0 + 2 + (P 0).n0 < m 0)
    (hs : X.async.mmaStarted (0, hd 0 + 2 + (P 0).n0) = true) {row col : Nat}
    (hr : row < 128) (hc : col < 8) (hb : (P 0).c + 8 ≤ 512) :
    TcMma.Result L [] X (0, hd 0 + 2 + (P 0).n0) ⟨0, row, (P 0).c + col⟩
      (s32 (dot a b row col)) := by
  obtain ⟨ab, bb, hop, hA, hB'⟩ := mma_operands hpre hX hW hmm hs
  have hval : TcMma.mmaTerms (.i8 true true false) ab bb row col =
      some ((List.range 32).map fun k => a row k * b k col) := by
    simp only [TcMma.mmaTerms, TcMma.Kind.k, elementBytes_i8]
    rw [mapM_some _ (fun k => a row k * b k col) _ (fun k hk => by
      have hk' := List.mem_range.mp hk
      simp only [hA row hr k hk', hB' col hc k hk']; rfl)]
  refine .overwrite (kernel_mma_issue hW hmm) (mma_writeCell hr hc hb) hop ?_
  simp only [TcMma.eval, mmaSpec, mmaDesc, TcMma.intEval, TcMma.operandRow,
    Bool.false_eq_true, false_and, ↓reduceIte, hval]
  rfl

/-- Any derived result for a cell of the kernel MMA's tile is that cell's exact product. -/
theorem result_value (hmm : hd 0 + 2 + (P 0).n0 < m 0) {src : EvId} {row col : Nat}
    {v : Value} (hr : TcMma.Result L [] X src ⟨0, row, (P 0).c + col⟩ v) :
    v = s32 (dot a b row col) := by
  cases hr with
  | overwrite issue position reads arith =>
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hW.mmaIssue issue
    obtain ⟨hcell, hr, hc, hb⟩ := mma_writeCell_inv position
    simp only [TcMma.Cell.mk.injEq, true_and] at hcell
    obtain ⟨rfl, hcol⟩ := hcell
    have hcol' : col = _ := Nat.add_left_cancel hcol
    subst hcol'
    have hs : X.async.mmaStarted (0, hd 0 + 2 + (P 0).n0) = true := by
      simp [AsyncCopy.Snapshot.mmaStarted, reads]
    obtain ⟨ab, bb, hop, hA, hB'⟩ := mma_operands hpre hX hW hmm hs
    rw [hop] at reads
    cases reads
    have hval : TcMma.mmaTerms (.i8 true true false) ab bb row col =
        some ((List.range 32).map fun k => a row k * b k col) := by
      simp only [TcMma.mmaTerms, TcMma.Kind.k, elementBytes_i8]
      rw [mapM_some _ (fun k => a row k * b k col) _ (fun k hk => by
        have hk' := List.mem_range.mp hk
        simp only [hA row hr k hk', hB' col hc k hk']; rfl)]
    simp only [TcMma.eval, mmaSpec, mmaDesc, TcMma.intEval, TcMma.operandRow,
    Bool.false_eq_true, false_and, ↓reduceIte, hval] at arith
    cases arith
    rfl
  | accumulate issue _ _ _ _ _ =>
    obtain ⟨-, -, -, h, -⟩ := hW.mmaIssue issue
    cases h
  | accumulateStored issue _ _ _ _ _ =>
    obtain ⟨-, -, -, h, -⟩ := hW.mmaIssue issue
    cases h

/-- Register `j` of thread `g`'s load reads lane `g`, column `col + j` of CTA 0 (`LoadCell`),
whose read source is the completed MMA, which wrote `D[g][j]` there. -/
theorem ld_source {g : Nat} (hg : g < 128) (hm : ldIdx g (P g) < m g) {j : Nat} (hj : j < 8) :
    TcMma.LoadCell L X (g, ldIdx g (P g)) j ⟨0, g, (P 0).col + j⟩ ∧
      TcMma.ReadSource L X .ld (0, hd 0 + 2 + (P 0).n0) (g, ldIdx g (P g))
        ⟨0, g, (P 0).col + j⟩ ∧
      TcMma.Wrote L [] X (0, hd 0 + 2 + (P 0).n0) ⟨0, g, (P 0).col + j⟩ (s32 (dot a b g j)) := by
  set S := L.sharedBase
  have hT := threads_eq hpre
  have hB := hpre.block
  have hld := ldIdx_eq (g := g) (P g)
  have htl := tl_ge (g := g) (P g)
  have h0 : hd 0 = 9 := rfl
  have hw1 : X.get (g, tl g (P g) + (P g).n1) = some (wait1E S true) := by
    rw [hW.get_of_lt hg (by omega), fullAt_w1t]
  have hcm := commit_exists hpre hX hW hw1
  have hcg := c_eq hpre hX hW hg (by omega)
  have hc0 := c_eq hpre hX hW (g := 0) (by decide) (by omega)
  have hcol := col_ok hpre hX hW (P := P) (m := m) (by omega)
  have ho := wait_observes_mma hpre hX hW hw1
  set ws : MbarScope := .cta
  have hg0 : g / L.block = 0 := Nat.div_eq_of_lt (by rw [hB]; omega)
  have hsc : ScopesMeet L .cluster 0 ws g := by
    have ht := threads_eq hpre
    refine ⟨⟨by omega, by omega, by simp [hg0]⟩, ?_⟩
    exact ⟨by omega, by omega, by simp [hg0]⟩
  have hmm : hd 0 + 2 + (P 0).n0 < m 0 := by omega
  have hissue := kernel_mma_issue hW hmm
  have htld : X.TLd (g, ldIdx g (P g)) (taddr g (P g).c) (P g).vals .s32x32b :=
    ⟨Flow.tmemLoad_0, by rw [hW.get_of_lt hg hm, fullAt_ld]; rfl⟩
  have hta1 : taddr g (P g).c / 2 ^ 16 + laneOf L g = g := by
    unfold taddr laneOf; rw [hB, hcg]; omega
  have hta2 : taddr g (P g).c % 2 ^ 16 = (P 0).col := by unfold taddr; rw [hcg]; omega
  have hcell : TcMma.writeCell (mmaSpec S) (P 0).c mmaMask g j = some ⟨0, g, (P 0).col + j⟩ := by
    rw [mma_writeCell hg hj (by omega), hc0]
  have hwrite : X.MmaCell (0, hd 0 + 2 + (P 0).n0) ⟨0, g, (P 0).col + j⟩ :=
    ⟨_, _, _, _, g, j, hissue, hcell⟩
  have hload : TcMma.LoadCell L X (g, ldIdx g (P g)) j ⟨0, g, (P 0).col + j⟩ :=
    ⟨_, _, _, htld, by rw [hW.vals]; exact hj, by
      simp only [tcDataCell_s32x32b, tcDataCell32, laneBase, laneOf, TcMma.Cell.mk.injEq]
      refine ⟨by rw [hB]; omega, by rw [hB]; omega, by rw [hta2]⟩⟩
  have hne : ((0, hd 0 + 2 + (P 0).n0) : EvId) ≠ (g, ldIdx g (P g)) := fun h => by
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    have := tl_zero (P 0)
    have := ldIdx_eq (g := 0) (P 0)
    omega
  refine ⟨hload, ⟨hne, .inl hwrite,
    .inl
      (.inl (.inl ⟨(g, tl g (P g) + (P g).n1), ws, ho, hsc, po_baseCausality (by omega) (len_of_get
      htld.choose_spec) (by simp [hw1, wait1E, Event.acc])⟩)),
    ?_, ?_⟩, ?_⟩
  · intro other ho'
    rcases ho' with ho' | ⟨_, _, _, _, ⟨_, hst⟩, -⟩ | ⟨_, _, _, _, ⟨_, hcp⟩, -⟩ |
      ⟨_, ⟨_, hsh⟩, -⟩
    · exact .inl (mma_access hW (.inl ho')).1
    · exact (hW.no_tst hst).elim
    · obtain ⟨_, _⟩ := other; exact (hW.no_cp hcp).elim
    · obtain ⟨_, _⟩ := other; exact (hW.no_shift hsh).elim
  · intro key r hr _ d hrel
    obtain ⟨t, n, pc', grp, hget⟩ := release_event hrel
    exact .inl (dealloc_done hpre hX hW d pc' grp none t n _ _ hget (.inr (.inl ⟨j, hload⟩)))
  · have hr := mma_result hpre hX hW hmm
      (hX.tma.2.1.2 _ (commit_observed_done hX.tcCommit ho)) hg hj (by omega)
    rw [hc0] at hr
    exact .inl hr

/-- **The loaded words.** Word `j` of thread `g`'s load is `D[g][j]`. -/
theorem ld_vals {g : Nat} (hg : g < 128) (hm : ldIdx g (P g) < m g) :
    ∀ j < 8, (P g).vals[j]? = some (s32 (dot a b g j)) := by
  intro j hj
  have hcg := c_eq hpre hX hW hg
    (by have := ldIdx_eq (g := g) (P g); have := tl_ge (g := g) (P g); omega)
  have htld : X.TLd (g, ldIdx g (P g)) (taddr g (P g).c) (P g).vals .s32x32b :=
    ⟨Flow.tmemLoad_0, by rw [hW.get_of_lt hg hm, fullAt_ld]; rfl⟩
  obtain ⟨hc, hs, hv⟩ := ld_source hpre hX hW hg hm hj
  obtain ⟨word, hw, hc⟩ := hX.tcRead.1 _ _ _ _ j _ _ _ htld hc hs hv
  rcases hc with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact hw
  · simp [s32, Value.bytes] at hb

/-- The loaded words are words. -/
theorem words {g : Nat} (hg : g < 128) (hm : ldIdx g (P g) < m g) {j : Nat} (hj : j < 8) :
    (word (P g).vals j).bytes = 4 := by
  have := ld_vals hpre hX hW hg hm j hj
  simp [word, List.getD_eq_getElem?_getD, this, s32, Value.bytes]

/-- No thread performs undefined behaviour. -/
theorem u_nil {g : Nat} (hg : g < 128) : u g = [] := by
  rcases hW.ub g hg with h | ⟨pc, f, -, ⟨hm, hbad⟩ | ⟨j, hj, hm, hbad⟩⟩
  · exact h
  · exact absurd hbad (rd_ok hpre hX hW hg (by omega))
  · exact absurd (storeOk_of_bytes (words hpre hX hW hg (by omega) hj)) hbad

end

end

end PTX.Kernels.TcGemm.Proof
