-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Lib.WinSet
import Kernels.InklingRelDecode.Proof.Softmax.Export.HalfAB
import Kernels.InklingRelDecode.Proof.Softmax.Export.HalfC

/-! # The registers of the bias path hold halves

The three groups of the bias path (the packs of the preloads' and the loop's words, the unpacks
and widenings of the first window) read halves, resp. words of two halves. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Lib

variable {Q : Params} {L : Launch} {g : Nat}

private theorem halfPc_scan : scanCode (fun pc ins =>
    !(((decide (574 ≤ pc) && decide (pc < 2331)) || (decide (2560 ≤ pc) && decide (pc < 2853))) &&
      !Assumptions.emuSites.contains pc && (Iface.halfSrcs ins.op).isSome) ||
      decide ((816 ≤ pc ∧ pc < 848) ∨ (1014 ≤ pc ∧ pc < 1046) ∨ (1303 ≤ pc ∧ pc ≤ 1429)))
    kernel.code 0 = true := by
  decide +kernel

private theorem halfPc_range (pc : Nat) (h : Iface.halfPc pc = true) :
    (816 ≤ pc ∧ pc < 848) ∨ (1014 ≤ pc ∧ pc < 1046) ∨ (1303 ≤ pc ∧ pc ≤ 1429) := by
  cases hc : kernel.code[pc]? with
  | none => simp [Iface.halfPc, hc] at h
  | some ins =>
    have := scanCode_get halfPc_scan hc
    simp only [Iface.halfPc, hc] at h
    rw [Nat.zero_add] at this
    simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this

/-- **The registers a pack, unpack or widening of the bias path reads hold halves**
(`Iface.LateValues.half`). -/
public theorem half_late {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (hpc : Iface.halfPc t.pc = true) :
    ∀ i, kernel.code[t.pc]? = some i → ∀ srcs, Iface.halfSrcs i.op = some srcs →
      ∀ r, .reg r ∈ srcs → ∃ v, t.regs r = some v ∧ TyG.halfSrcOk i.op v := by
  intro i hc srcs hs r hr
  rcases halfPc_range _ hpc with h | h | h
  · exact half_ab hp hX hf hS h5 lane hl (.inl h) hc hs hr
  · exact half_ab hp hX hf hS h5 lane hl (.inr h) hc hs hr
  · exact half_c hp hX hf hS h5 lane hl h.1 h.2 hc hs hr

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
