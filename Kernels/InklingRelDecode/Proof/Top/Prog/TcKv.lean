-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvRead
public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvByte
public import Kernels.InklingRelDecode.Proof.Iface.KvCopyForm
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Lemmas.Flow.WriteBytes
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.MmaBytePair

@[expose] public section

/-! # The operand bytes of the MMAs have visible writes: the ring bytes

A write that covers a byte has a byte there (`Prog.wbyte_of_write`), and the B operand byte an
issued MMA reads from a ring slot has the copy of its use as a write before the read
(`Prog.kvVisible`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow Protocol Protocol.Values Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem sized_code :
    kernel.code.all (fun i => !writeOp i.op || sizedWrite i.op) = true := by
  decide +kernel

/-- **A write covering a byte has a byte there.** -/
theorem Prog.wbyte_of_write (hX : Consistent L kernel Assumptions.all m X) {w a bs loc}
    (hw : X.MemWrites w a bs) (hc : a.Covers loc) : ∃ v, wbyte a bs loc = some v := by
  have hlen : bs.length = a.size → ∃ v, wbyte a bs loc = some v := fun h => by
    obtain ⟨-, -, h1, h2⟩ := hc
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  apply hlen
  rcases Lib.write_kinds hX hw with ⟨i, pc, rfl, he⟩ | ⟨i, x, y, z, addr, sp, rfl, -⟩
  · obtain ⟨_, bad⟩ | ⟨t, ins, o, -, hcode, hf⟩ := get_source hX he
    · cases bad
    have h := List.all_eq_true.mp sized_code ins (List.mem_of_getElem? hcode)
    rw [fires_write_op hf rfl] at h
    exact fires_write_length hf rfl (by simpa using h)
  · obtain ⟨o, addr, b, -, -, -, -, sz, rfl, -⟩ := hw
    simp [sz]

/-- **The B operand byte of an issued MMA that lies in a ring slot has a copy of its use before
the read**, once the slot's ready barrier completed the use (`Values.read_ctx`). -/
theorem Prog.kvVisible {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) {g k pc dst s acc mask idx l}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩) (hl : s.byteLoc .b idx = some l) :
    ∃ w a bs, X.MemWrites w a bs ∧ a.Covers l ∧
      ByteCausality L X l w (.async (g, k) (.mmaRead true idx)) := by
  obtain ⟨c, σ, hcg, hg, hbyte, hpoll⟩ := read_ctx hp hX hf rows words he
  obtain ⟨hc0, hs0⟩ := hbyte _ _ hl
  subst hg
  obtain ⟨gl, kl, pcl, a, sp, o, x, y, z, r, sl, kvh, isV, hh, dst', bar, hcp, ho, hos, hn, hwl,
    hu', -, hr, hsl, hkvh, hV, hH, hal, hspec⟩ := ring_copy_exists hp hX hf rows init words hu form
    hcg (TcMma.OperandSpec.byteLoc_shared hl) hc0 hs0 hpoll
  subst hspec
  have bnd := TensorCopy.writeLoc_bounds hwl
  simp [Lib.kvCopySpec, mapKv, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, TensorDescriptor.Format.bytes] at bnd
  have hi : X.TensorIssue (gl, kl) a o.spec := ⟨pcl, by rw [hos]; exact hcp⟩
  have hz : z < 2 := by have := bnd.2.2; omega
  have hb := copy_write_byte hp hX nub hr hsl hkvh hV hH ho hi hos hn (x := x) (y := y) (z := z)
    bnd.1 bnd.2.1 hz
  have memw : X.MemWrites (.async (gl, kl) (.write (.load x y z))) { loc := l, size := 1 }
      [_] := ⟨o, a, _, ho, hos ▸ ⟨pcl, hcp⟩, hos ▸ hwl, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have rintent : X.Intent (.async (KV.leader L X c 7, k) (.mmaRead true idx))
      { loc := l, size := 1 } false :=
    ⟨rfl, rfl, .inl ⟨dst, s, acc, mask, ⟨pc, he⟩, by simpa using hl⟩⟩
  have cov : ({ loc := l, size := 1 } : Acc).Covers l := by simp [Acc.Covers, Loc.InRange]
  have ring : InRing L l := by
    refine ⟨TcMma.OperandSpec.byteLoc_shared hl, ?_⟩
    have := hs0
    unfold Iface.InSlot at this
    have h3 : 32768 * (σ.val + 1) ≤ 32768 * 3 := Nat.mul_le_mul_left _ σ.isLt
    generalize 32768 * (σ.val + 1) = P at *
    omega
  rcases copy_read_side hp hX hf rows init words memw.intent rintent cov cov ring
    (fun _ _ => nofun) ⟨_, _, _, rfl⟩ hc0 hs0 with ⟨-, bc⟩ | ⟨hlt, -⟩
  · exact ⟨_, _, _, memw, cov, bc⟩
  · exact absurd hu' (by
      have : Lib.readUseOf X (ringSlot Q L X c σ)
          (.async (KV.leader L X c 7, k) (.mmaRead true idx)) <
          Lib.copyUseOf X (ringSlot Q L X c σ) (.async (gl, kl) (.write (.load x y z))) := hlt
      intro h
      change _ = SingleTmaRing.readUse X ((KV.decl Q L X c).slot σ) (KV.leader L X c 7, k) at h
      have h2 : SingleTmaRing.readUse X ((KV.decl Q L X c).slot σ) (KV.leader L X c 7, k) < _ :=
        this
      omega)

end PTX.Kernels.InklingRelDecode.Proof.Top
