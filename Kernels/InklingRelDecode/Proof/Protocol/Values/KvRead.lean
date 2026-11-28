-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvCopies
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseOrder
import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Kernels.InklingRelDecode.Proof.Protocol.KV.ReadUse
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Lemmas.Order.ReadSame
import Lemmas.Tcgen05.MmaBytePair
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Protocol.SingleTmaRing.RingFacts

@[expose] public section

/-! # The operand bytes an MMA reads from a ring slot

The B operand byte an MMA reads is the byte of the tensor copy of its use that covers it: every
other write of the byte is a copy of an earlier use (before that copy), a copy of a later use
(after the read), or the allocation's store of the base word (before every copy). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The slot and use of an MMA's B operand reads**: the CTA `c` and slot `σ` of every byte it
reads, and its use of the slot, below the completed phases of the ready barrier. -/
theorem read_ctx (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (words : RoleBytes L X) {g k pc dst s acc mask}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩) :
    ∃ c, ∃ σ : Fin 3, c < L.grid ∧ g = KV.leader L X c 7 ∧
      (∀ idx l, s.byteLoc .b idx = some l → l.cta = c ∧ Iface.InSlot L σ.val l.addr) ∧
      SingleTmaRing.readUse X ((KV.decl Q L X c).slot σ) (g, k) <
        okPolls (KV.Ring.ready.obj L c σ) (X.tr g) := by
  obtain ⟨warp, elected, σ, hbyte, T, n, le, lt, slot, bound⟩ :=
    Mma.Export.read_slot hp hX hf words he
  have hg := Frame.lt_of_get hX he
  have hcg : g / L.block < L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads, Nat.mul_comm] using hg)
  have heq : KV.leader L X (g / L.block) 7 = g := by
    obtain ⟨ev, hev, rest⟩ := elected
    have := KV.leader_eq hX hg ⟨ev, (List.take_sublist k _).subset hev, rest⟩
    rwa [warp] at this
  have credit := KV.read_credit hp hX hf words rows hg warp rfl bound le lt slot (s := σ)
  refine ⟨g / L.block, σ, hcg, heq.symm, hbyte, ?_⟩
  have := SingleTmaRing.okPolls_take_le (KV.Ring.ready.obj L (g / L.block) σ) (X.tr g) k
  have h2 : SingleTmaRing.readUse X ((KV.decl Q L X (g / L.block)).slot σ) (g, k) + 1 ≤
      okPolls (KV.Ring.ready.obj L (g / L.block) σ) ((X.tr g).take k) := credit
  exact lt_of_lt_of_le h2 this

/-- **Every write of a ring byte other than the copy of the read's use is before that copy or after
the read.** -/
theorem other_writes (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) {c l} {σ : Fin 3} (ring : InRing L l)
    (hc : l.cta = c) (hs : Iface.InSlot L σ.val l.addr) {gl kl x y z a}
    (w0 : X.Intent (.async (gl, kl) (.write (.load x y z))) a true) (ca : a.Covers l)
    {g k isB idx b} (rd : X.Intent (.async (g, k) (.mmaRead isB idx)) b false) (cb : b.Covers l)
    (use : copyUseOf X (ringSlot Q L X c σ) (.async (gl, kl) (.write (.load x y z))) =
      readUseOf X (ringSlot Q L X c σ) (.async (g, k) (.mmaRead isB idx))) {w' a'}
    (hw : X.Intent w' a' true) (ca' : a'.Covers l) :
    w' = .async (gl, kl) (.write (.load x y z)) ∨
      ByteCausality L X l w' (.async (gl, kl) (.write (.load x y z))) ∨
      ByteCausality L X l (.async (g, k) (.mmaRead isB idx)) w' := by
  have copy : (∀ g k, w' ≠ .thread (g, k)) → w' = .async (gl, kl) (.write (.load x y z)) ∨
      ByteCausality L X l w' (.async (gl, kl) (.write (.load x y z))) ∨
      ByteCausality L X l (.async (g, k) (.mmaRead isB idx)) w' := fun async => by
    rcases copies_use_order hp hX hf rows init words hu hw w0 ca' ca ring async
      (fun _ _ => nofun) hc hs with ⟨-, bc⟩ | heq | ⟨hgt, -⟩
    · exact .inr (.inl bc)
    · exact .inl heq
    · rcases copy_read_side hp hX hf rows init words hw rd ca' cb ring async ⟨_, _, _, rfl⟩ hc
        hs with ⟨hle, -⟩ | ⟨-, bc⟩
      · omega
      · exact .inr (.inr bc)
  by_cases base : l.addr < L.sharedBase + 4
  · rcases base_writer hp hX hw ca' ring.1 ring.2.1 base with ⟨g', k', bs, rfl, store⟩ | async
    · exact .inr (.inl (alloc_before_copy hp hX hf store ca' w0 ca (fun _ _ => nofun)
        ⟨ring.1, ring.2.1, base⟩))
    · exact copy async
  · exact copy (kv_async_write hp hX hw ca' ⟨ring.1, by omega, ring.2.2⟩)

/-- **The B operand byte an MMA reads from a ring slot is the byte of the copy of its use.** -/
theorem ring_byte (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) {g k pc dst s acc mask ops idx l c}
    {σ : Fin 3} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) (hl : s.byteLoc .b idx = some l)
    (hc : l.cta = c) (hs : Iface.InSlot L σ.val l.addr) {gl kl pcl a sp o x y z w}
    (hcp : X.get (gl, kl) = some ⟨pcl, .tensorIssue a sp⟩) (ho : X.tensor (gl, kl) = some o)
    (hosp : o.spec = sp) (hw : TensorCopy.writeLoc sp x y z = some l)
    (hb : TensorCopy.writeByte o x y z = some w)
    (use : copyUseOf X (ringSlot Q L X c σ) (.async (gl, kl) (.write (.load x y z))) =
      readUseOf X (ringSlot Q L X c σ) (.async (g, k) (.mmaRead true idx))) :
    ops.b[idx]? = some (some w) := by
  obtain ⟨obs, hrd, hget⟩ := hX.mma_read_exists (isB := true) ⟨pc, he⟩ hops (by simpa using hl)
  have memr : X.MemReads (.async (g, k) (.mmaRead true idx)) { loc := l, size := 1 } [obs] :=
    ⟨obs, hrd, rfl, rfl⟩
  have memw : X.MemWrites (.async (gl, kl) (.write (.load x y z))) { loc := l, size := 1 } [w] :=
    ⟨o, a, w, ho, hosp ▸ ⟨pcl, hcp⟩, hosp ▸ hw, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have wintent := memw.intent
  have rintent : X.Intent (.async (g, k) (.mmaRead true idx)) { loc := l, size := 1 } false :=
    ⟨rfl, rfl, .inl ⟨dst, s, acc, mask, ⟨pc, he⟩, by simpa using hl⟩⟩
  have cov : ({ loc := l, size := 1 } : Acc).Covers l := by simp [Acc.Covers, Loc.InRange]
  have ring : InRing L l := by
    refine ⟨TcMma.OperandSpec.byteLoc_shared hl, ?_⟩
    have := hs
    unfold Iface.InSlot at this
    have h3 : 32768 * (σ.val + 1) ≤ 32768 * 3 := Nat.mul_le_mul_left _ σ.isLt
    generalize 32768 * (σ.val + 1) = P at *
    omega
  have before := copy_read_side hp hX hf rows init words wintent rintent cov cov ring
    (fun _ _ => nofun) ⟨_, _, _, rfl⟩ hc hs
  rcases before with ⟨-, bc⟩ | ⟨hlt, -⟩
  · have := read_byte_of_writers_hidden hX memr (k := 0) Nat.zero_lt_one
      (fun w' => w' = .async (gl, kl) (.write (.load x y z))) (some w) memw cov bc
      (fun w' d bs hW hw' hcv => by
        subst hW
        obtain ⟨hfp, rfl⟩ := memw.unique hw'
        simp [wbyte, ← hfp.1, Loc.at])
      (fun w' d bs hw' hcv => by
        rcases other_writes hp hX hf rows init words hu ring hc hs wintent cov rintent cov use
          hw'.intent hcv with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h))
    have hget' : ops.b[idx]? = some obs := hget
    rw [hget']
    exact congrArg some (Option.some.inj (by simpa using this))
  · omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
