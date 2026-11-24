-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Lemmas.Order.ReadLast
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.RefNext

import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

/-! # Bias words from a tensor-copy hand-off

The hand-off identifies the tensor-copy byte visible at each position in a shared bias word and
orders the other overlapping writes. The read returns those bytes, which rebuild to the
fragment's expected pair of BF16 payloads and masks.
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A tensor-copy byte with the value and ordering required at one position of a bias read. -/
def BiasByteHandoff (L : Launch) (X : Execution) (r : EvId) (loc : Loc) (byte : Byte) : Prop :=
  ∃ i x y k dst data,
    let w := AsyncCopy.Ref.async i (.write (.load x y k))
    X.MemWrites w dst data ∧ dst.Covers loc ∧ wbyte dst data loc = some byte ∧
      modelCausality L X loc w (.thread r) ∧
      ∀ w' dst' data', X.MemWrites w' dst' data' → dst'.Covers loc →
        w' = w ∨ modelCausality L X loc w' w ∨ modelCausality L X loc (.thread r) w'

/-- The bias hand-off supplies the two physical BF16 elements of each 32-bit read. -/
def BiasReadHandoff (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d n c e b j a bs, X.get (g, k) = some e →
    Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n)) →
    Softmax.Ref p L g (d, c) → d.site = .bld b j → e.kind = .rd a bs →
    ∃ lo hi : Option ℝ, ∀ t : Fin 4,
      BiasByteHandoff L X (g, k) (a.loc.at t.val)
        ((biasValue (if t.val < 2 then lo else hi)).byteAt (t.val % 2))

/-- The four bytes of two bias elements in increasing address order. -/
def biasPairBytes (lo hi : Option ℝ) : List (Option Byte) :=
  [some ((biasValue lo).byteAt 0), some ((biasValue lo).byteAt 1),
   some ((biasValue hi).byteAt 0), some ((biasValue hi).byteAt 1)]

/-- BYTES reconstructs two payloads or masks as the word the softmax machine accepts. -/
theorem rebuild_biasPairBytes (lo hi : Option ℝ) :
    ∃ v, rebuild 3 (biasPairBytes lo hi) = .ok v ∧ biasOk v = true := by
  have hbytes (x : Option ℝ) :
      (biasValue x).toBytes = [(biasValue x).byteAt 0, (biasValue x).byteAt 1] := by
    cases x <;> rfl
  have heq : biasPairBytes lo hi = ((biasValue lo).toBytes ++ (biasValue hi).toBytes).map some := by
    rw [hbytes lo, hbytes hi]; rfl
  refine ⟨(match lo, hi with
    | none, none => b32 0xFF80FF80
    | _, _ => .pair (biasValue lo) (biasValue hi)), ?_, ?_⟩
  · rw [heq]
    cases lo <;> cases hi <;>
      simp [biasValue, rebuild, rebuild.halves, Value.toBytes, Value.bytes, Value.byteAt,
        FloatFmt.bytes, intByte, List.range_succ, rebuildBits, littleEndianBits, byteBits,
        Value.bitPattern, bind, Option.bind, Except.bind, pure, Except.pure, b32]
  · cases lo <;> cases hi <;> rfl

/-- An actual bias read returns exactly the two elements from its ordered byte sources. -/
theorem read_biasPairBytes (hX : Consistent L kernel Assumptions.all m X)
    {r : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.MemReads (.thread r) a bs)
    (ha : a.size = 4) {lo hi : Option ℝ}
    (hsrc : ∀ t : Fin 4, BiasByteHandoff L X r (a.loc.at t.val)
      ((biasValue (if t.val < 2 then lo else hi)).byteAt (t.val % 2))) :
    bs = biasPairBytes lo hi := by
  have hlen := (hX.rf (.thread r) a bs he).1.trans ha
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hka : k < a.size := ha ▸ hk
    obtain ⟨i, x, y, j, dst, data, hw, hc, hv, hb, hall⟩ := hsrc ⟨k, hk⟩
    rw [read_byte_of_last_write hX he hka hw hc hb hall, hv]
    interval_cases k <;> norm_num [biasPairBytes]
  · rw [List.getElem?_eq_none (hlen.trans_le (Nat.le_of_not_gt hk))]
    have hlen' : (biasPairBytes lo hi).length ≤ k := Nat.le_of_not_gt hk
    exact (List.getElem?_eq_none hlen').symm

/-- Every bias site decodes to a shared load of 32-bit elements. -/
private theorem bias_load {g : Nat} (b : Bool) (j : Fin 16) :
    ∃ ins base regs off, kernel.code[(Site.bld b j).pc]? = some ins ∧
      ∀ t, eventTmpl Assumptions.all L g t ins.op =
        loadTmpl Assumptions.all L g t .shared false 32 regs base off := by
  cases b <;> fin_cases j <;> exact ⟨_, _, _, _, by code_lookup, fun _ => rfl⟩

/-- The actual read at a bias site reads a four-byte element. -/
theorem bias_read_size (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k : Nat} {d : D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n)))
    {b : Bool} {j : Fin 16} (hs : d.site = .bld b j) {a : Acc} {bs : List (Option Byte)}
    (hr : e.kind = .rd a bs) : a.size = 4 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => threadD_sound hp hg) hX he hσ
  obtain ⟨ins', base, regs, off, hc', ht⟩ := bias_load (L := L) (g := g) b j
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  rw [ht t] at hf
  simp only [loadTmpl, Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · have hu := (congrArg Event.kind hf.1).symm.trans hr
    cases hu
  · rename_i a' hacc
    obtain ⟨bytes, -, hkind, -⟩ := hf
    have ha := (Kind.rd.inj (hr.symm.trans (congrArg Event.kind hkind))).1
    subst a'
    cases hloc : effAddr L g t .shared base off <;>
      simp only [hloc, bind, Except.bind] at hacc
    · cases hacc
    · unfold elemAcc at hacc
      split at hacc <;> cases hacc
      rfl

/-- The bias portion of the fragment's source obligation follows from the ordered copies. -/
theorem expect_bias (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hB : BiasReadHandoff p L X)
    {g k : Nat} {d : D} {n : Cls → Nat} {c : Cnt → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.softmax,d⟩,n)))
    (hJ : Softmax.Ref p L g (d, c)) {b : Bool} {j : Fin 16} (hs : d.site = .bld b j) :
    ExpectD p L g d e := by
  simp only [ExpectD, hs]
  intro a bs hr
  have ha := bias_read_size hp hX he hσ hs hr
  obtain ⟨lo, hi, hsrc⟩ := hB g k d n c e b j a bs he hσ hJ hs hr
  obtain ⟨pc, kind⟩ := e
  change kind = .rd a bs at hr
  subst kind
  have hread : X.MemReads (.thread (g, k)) a bs := .inl ⟨pc, he⟩
  rw [read_biasPairBytes hX hread ha hsrc]
  exact rebuild_biasPairBytes lo hi

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
