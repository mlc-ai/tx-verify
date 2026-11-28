-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpBytes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.ASource
import Lemmas.Async.ReadReuse

@[expose] public section

/-! # The words of a done query copy are defined

The copy observed the bytes it reads once it started (`mmaOperands`). Each is the byte of the
query tensor load that wrote it: that load's write is ordered before the copy's read by the lane's
poll of `qTma` (`cp_bytes_ordered`), and every other write of the byte is ordered with it, so the
read has the written byte (`read_byte_of_ordered_reuse`). A copy without decompression
(`mma_cp_fmt`) leaves the four consecutive bytes of each word, so `TcCopy.cpWord` is `some`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **An operand byte of a started query copy is defined.** -/
theorem cp_operand_byte {g iC : Nat} {c : TcCopy.Spec} (hi : X.CpIssue (g, iC) c)
    {operands : MmaOperands} (hop : X.async.mmaOperands (g, iC) = some operands)
    {k : Nat} (hk : k < c.ctas.length * c.shape.sourceBytes) :
    ∃ b, operands.a[k]? = some (some b) := by
  obtain ⟨src, hf, hv, ⟨b, hb, hac⟩, hord⟩ := cp_bytes_ordered hp hX hFw hR hI hB hi hk
  have hlen : operands.a.length = c.ctas.length * c.shape.sourceBytes := by
    obtain ⟨-, ⟨hst, -⟩, -, -⟩ := hX.tma
    have hs : X.async.mmaStarted (g, iC) = true := by simp [Snapshot.mmaStarted, hop]
    obtain ⟨pc, hC⟩ := hi
    rcases hst _ hs with ⟨d, s, acc, mask, ops, ⟨pc', h'⟩, hop', -⟩ |
      ⟨c', ops, ⟨pc', h'⟩, hop', hl, -⟩ | ⟨s, ops, ⟨pc', h'⟩, hop', -⟩ <;>
      rw [hC] at h' <;> simp only [Option.some.injEq, Event.mk.injEq] at h'
    · obtain ⟨-, h⟩ := h'; cases h
    · obtain ⟨-, h⟩ := h'
      obtain rfl := Kind.tc.inj h |> TcKind.cp.inj
      rw [hop] at hop'
      obtain rfl := Option.some.inj hop'
      exact hl
    · obtain ⟨-, h⟩ := h'; cases h
  obtain ⟨o, ho⟩ : ∃ o, operands.a[k]? = some o := ⟨_, List.getElem?_eq_some_iff.2 ⟨by omega, rfl⟩⟩
  obtain ⟨l, ref, access, bytes, hw, hcv⟩ := src
  simp only at hb hac hf hv hord
  subst hb hac
  have hr : X.MemReads (.async (g, iC) (.mmaRead false k)) { loc := l, size := 1 } [o] :=
    ⟨o, ⟨hf, operands, hop, ho⟩, rfl, rfl⟩
  have := read_byte_of_ordered_reuse hX hr (k := 0) Nat.zero_lt_one hw
    (Acc.covers_at Nat.zero_lt_one) (by simpa [Loc.at] using hv)
    (fun w a bs hw' hc => by simpa [Loc.at] using hord w a bs hw' (by simpa [Loc.at] using hc))
  refine ⟨b, ?_⟩
  rw [ho]
  simpa [wbyte, Loc.at] using this

/-- **The words of every done copy are defined** (`TmRace.CpDefined`). -/
theorem cp_defined : TmRace.CpDefined X := by
  intro cp c cell hi hd ⟨c', cta, index, lane, hi', hcta, hidx, hlane, hcell⟩
  obtain ⟨g, iC⟩ := cp
  obtain ⟨pc, hC⟩ := hi
  obtain ⟨pc', hC'⟩ := hi'
  rw [hC] at hC'
  obtain rfl := TcKind.cp.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj hC')).2)
  obtain ⟨-, ⟨-, hdone⟩, -, -⟩ := hX.tma
  have hs := hdone _ hd
  obtain ⟨operands, hop⟩ : ∃ operands, X.async.mmaOperands (g, iC) = some operands := by
    cases h : X.async.mmaOperands (g, iC) with
    | none => simp [Snapshot.mmaStarted, h] at hs
    | some o => exact ⟨o, rfl⟩
  have hat : MmaAt L g pc := cp_mmaAt hp hX hFw hC
  obtain ⟨-, hsh, -, hct⟩ := mma_cp_spec hp hX hFw hC ⟨hat.2.1, hat.2.2⟩
  have hfmt := mma_cp_fmt hp hX hFw hC ⟨hat.2.1, hat.2.2⟩
  have hcl : c.ctas.length = 1 := by rw [hct]; rfl
  have hrb : c.shape.rowBytes = 32 := by rw [hsh]; rfl
  have hrw : c.shape.rows = 128 := by rw [hsh]; rfl
  have hsb : c.shape.sourceBytes = 4096 := by
    simp only [TcCpShape.sourceBytes, hrb, hrw]
  have hk0 : ∀ {k}, c.ctas[k]? = some cta → k = 0 := by
    intro k h
    rw [hct] at h
    cases k with
    | zero => rfl
    | succ k => simp at h
  have hb : ∀ t, t < 4 → ∃ b, operands.a[index / 32 * 32 + 4 * (index % 32 / 4) + t]? =
      some (some b) := by
    intro t ht
    refine cp_operand_byte hp hX hFw hR hI hB ⟨pc, hC⟩ hop ?_
    rw [hcl, hsb]
    rw [hsb] at hidx
    omega
  obtain ⟨b0, h0⟩ := hb 0 (by decide)
  obtain ⟨b1, h1⟩ := hb 1 (by decide)
  obtain ⟨b2, h2⟩ := hb 2 (by decide)
  obtain ⟨b3, h3⟩ := hb 3 (by decide)
  obtain ⟨v, hv⟩ : ∃ v, TcCopy.cpWord c (operands.a.drop (0 * c.shape.sourceBytes))
      (index / 32) (index % 32 / 4) = some v := by
    rw [Nat.add_zero] at h0
    simp [TcCopy.cpWord, hfmt, TcCopy.word, hrb, h0, h1, h2, h3]
  refine ⟨v, c, 0, cta, operands, index / 32, index % 32 / 4, lane, ⟨pc, hC⟩, ?_, hop,
    ?_, ?_, ?_, ?_, hv⟩
  · rw [hct] at hcta ⊢
    simp only [List.mem_singleton] at hcta
    simp [hcta]
  · rw [hrw]; omega
  · rw [hrb]; omega
  · rw [hrb] at hlane; exact hlane
  · rw [hcell, hrb]
    simp only [TcCopy.cell]
    rw [hrb]
    congr 1
    omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
